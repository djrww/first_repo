///|
/// Vector Incremental Topology (向量增量拓撲 - Planar Half-Edge DCEL Graph)
/// and Fine-Grained Reactivity (細粒度響應式 - Push-Pull Signal/Computed Dependency DAG).

///|
/// 2D Vector / Point in world or screen space.
pub(all) struct Vec2 {
  x : Double
  y : Double
} derive(Eq, Debug)

///|
pub extend Vec2 with Eq::{equal, not_equal}

///|
#deprecated("Use `Debug::to_repr` instead", skip_current_package=true)
#doc(hidden)
pub extend Vec2 with @debug.Debug::{to_repr}

///|
/// Construct a `Vec2`.
pub fn Vec2::new(x : Double, y : Double) -> Vec2 {
  { x, y, }
}

///|
/// Euclidean distance between two 2D points.
pub fn Vec2::dist(self : Vec2, other : Vec2) -> Double {
  let dx = self.x - other.x
  let dy = self.y - other.y
  (dx * dx + dy * dy).sqrt()
}

///|
/// Axis-Aligned Bounding Box (AABB) used by R-Tree, Sparse Grid, Dirty Rectangles, and Local Culling.
pub(all) struct Aabb {
  min_x : Double
  min_y : Double
  max_x : Double
  max_y : Double
} derive(Eq, Debug)

///|
pub extend Aabb with Eq::{equal, not_equal}

///|
#deprecated("Use `Debug::to_repr` instead", skip_current_package=true)
#doc(hidden)
pub extend Aabb with @debug.Debug::{to_repr}

///|
/// Construct a normalized AABB.
pub fn Aabb::new(
  min_x : Double,
  min_y : Double,
  max_x : Double,
  max_y : Double,
) -> Aabb {
  {
    min_x: min_x.min(max_x),
    min_y: min_y.min(max_y),
    max_x: min_x.max(max_x),
    max_y: min_y.max(max_y),
  }
}

///|
/// Compute surface area of the AABB.
pub fn Aabb::area(self : Aabb) -> Double {
  let w = (self.max_x - self.min_x).max(0.0)
  let h = (self.max_y - self.min_y).max(0.0)
  w * h
}

///|
/// Check if two AABBs intersect (inclusive of touching borders).
pub fn Aabb::intersects(self : Aabb, other : Aabb) -> Bool {
  self.min_x <= other.max_x &&
  self.max_x >= other.min_x &&
  self.min_y <= other.max_y &&
  self.max_y >= other.min_y
}

///|
/// Return the union AABB enclosing both `self` and `other`.
pub fn Aabb::union(self : Aabb, other : Aabb) -> Aabb {
  {
    min_x: self.min_x.min(other.min_x),
    min_y: self.min_y.min(other.min_y),
    max_x: self.max_x.max(other.max_x),
    max_y: self.max_y.max(other.max_y),
  }
}

///|
/// Return the intersection of two AABBs, or `None` if disjoint.
pub fn Aabb::intersection(self : Aabb, other : Aabb) -> Aabb? {
  let ix0 = self.min_x.max(other.min_x)
  let iy0 = self.min_y.max(other.min_y)
  let ix1 = self.max_x.min(other.max_x)
  let iy1 = self.max_y.min(other.max_y)
  if ix0 <= ix1 && iy0 <= iy1 {
    Some({ min_x: ix0, min_y: iy0, max_x: ix1, max_y: iy1, })
  } else {
    None
  }
}

///|
/// Smallest AABB enclosing every box in `boxes`; `None` when the list is empty.
pub fn Aabb::union_all(boxes : Array[Aabb]) -> Aabb? {
  if boxes.length() == 0 {
    return None
  }
  let mut acc = boxes[0]
  for i = 1; i < boxes.length(); i = i + 1 {
    acc = acc.union(boxes[i])
  }
  Some(acc)
}

///|
/// Expand AABB by `margin` in all 4 directions (for stroke width & anti-aliasing feather).
pub fn Aabb::inflate(self : Aabb, margin : Double) -> Aabb {
  {
    min_x: self.min_x - margin,
    min_y: self.min_y - margin,
    max_x: self.max_x + margin,
    max_y: self.max_y + margin,
  }
}

///|
/// Topological Vertex in the Planar Half-Edge DCEL Graph (向量增量拓撲頂點).
pub(all) struct TopoVertex {
  id : Int
  mut pos : Vec2
  incident_half_edges : Array[Int]
  mut version : Int
}

///|
/// Directed Half-Edge in the Doubly Connected Edge List (DCEL).
/// Paired with `twin_id = id ^ 1` representing the opposite direction.
pub(all) struct HalfEdge {
  id : Int
  mut origin_vertex : Int
  mut twin_id : Int
  mut next_edge : Int
  mut prev_edge : Int
  mut face_id : Int
  primitive_id : Int
  mut active : Bool
}

///|
/// Topological Face / Closed Region in the Planar Vector Topology.
pub(all) struct TopoFace {
  id : Int
  boundary_half_edge : Int
  mut signed_area : Double
  mut winding_number : Int
}

///|
/// Vector Incremental Topology Graph (向量增量拓撲):
/// Maintains vertices, twin half-edges, planar intersection splits, and closed faces
/// incrementally without full mesh reconstruction.
pub(all) struct VectorTopologyGraph {
  vertices : Array[TopoVertex]
  half_edges : Array[HalfEdge]
  faces : Array[TopoFace]
  mut snap_epsilon : Double
  mut topo_epoch : Int
  mut incremental_splits : Int
}

///|
/// Create a new empty Vector Incremental Topology Graph.
pub fn VectorTopologyGraph::new(snap_epsilon : Double) -> VectorTopologyGraph {
  {
    vertices: [],
    half_edges: [],
    faces: [],
    snap_epsilon,
    topo_epoch: 0,
    incremental_splits: 0,
  }
}

///|
/// Incrementally insert or snap-merge a 2D vertex within `snap_epsilon`.
pub fn VectorTopologyGraph::upsert_vertex(
  self : VectorTopologyGraph,
  pos : Vec2,
) -> Int {
  for v in self.vertices {
    if v.pos.dist(pos) <= self.snap_epsilon {
      return v.id
    }
  }
  let id = self.vertices.length()
  self.topo_epoch = self.topo_epoch + 1
  self.vertices.push({
    id,
    pos,
    incident_half_edges: [],
    version: self.topo_epoch,
  })
  id
}

///|
/// Compute segment-segment intersection between (p1, p2) and (p3, p4),
/// strictly inside both open segments (t, u in (1e-5, 1 - 1e-5)).
pub fn intersect_open_segments(
  p1 : Vec2,
  p2 : Vec2,
  p3 : Vec2,
  p4 : Vec2,
) -> Vec2? {
  let r_x = p2.x - p1.x
  let r_y = p2.y - p1.y
  let s_x = p4.x - p3.x
  let s_y = p4.y - p3.y
  let denom = r_x * s_y - r_y * s_x
  if denom.abs() < 1.0e-9 {
    return None
  }
  let qp_x = p3.x - p1.x
  let qp_y = p3.y - p1.y
  let t = (qp_x * s_y - qp_y * s_x) / denom
  let u = (qp_x * r_y - qp_y * r_x) / denom
  if t > 1.0e-4 && t < 0.9999 && u > 1.0e-4 && u < 0.9999 {
    Some({ x: p1.x + t * r_x, y: p1.y + t * r_y, })
  } else {
    None
  }
}

///|
/// Raw internal addition of a twin pair of half-edges between `u` and `v`.
fn VectorTopologyGraph::add_raw_half_edge_pair(
  self : VectorTopologyGraph,
  u : Int,
  v : Int,
  primitive_id : Int,
) -> Int {
  let he_id = self.half_edges.length()
  let twin_id = he_id + 1
  self.half_edges.push({
    id: he_id,
    origin_vertex: u,
    twin_id,
    next_edge: twin_id,
    prev_edge: twin_id,
    face_id: -1,
    primitive_id,
    active: true,
  })
  self.half_edges.push({
    id: twin_id,
    origin_vertex: v,
    twin_id: he_id,
    next_edge: he_id,
    prev_edge: he_id,
    face_id: -1,
    primitive_id,
    active: true,
  })
  self.vertices[u].incident_half_edges.push(he_id)
  self.vertices[v].incident_half_edges.push(twin_id)
  he_id
}

///|
/// Split an existing undirected edge (represented by `he_id` and its `twin_id`)
/// at an interior vertex `mid_v`, preserving planar DCEL invariants incrementally.
/// The two new half-edge pairs inherit the primitive, the face of the half-edge they
/// replace, and the neighbouring `next`/`prev` links, so closed face rings stay wired.
pub fn VectorTopologyGraph::split_edge_incremental(
  self : VectorTopologyGraph,
  he_id : Int,
  mid_v : Int,
) -> (Int, Int) {
  let twin_id = self.half_edges[he_id].twin_id
  let u = self.half_edges[he_id].origin_vertex
  let v = self.half_edges[twin_id].origin_vertex
  let prim = self.half_edges[he_id].primitive_id
  let forward_next = self.half_edges[he_id].next_edge
  let forward_prev = self.half_edges[he_id].prev_edge
  let forward_face = self.half_edges[he_id].face_id
  let twin_next = self.half_edges[twin_id].next_edge
  let twin_prev = self.half_edges[twin_id].prev_edge
  let twin_face = self.half_edges[twin_id].face_id
  self.half_edges[he_id].active = false
  self.half_edges[twin_id].active = false
  let e1 = self.add_raw_half_edge_pair(u, mid_v, prim)
  let e2 = self.add_raw_half_edge_pair(mid_v, v, prim)
  let t1 = self.half_edges[e1].twin_id
  let t2 = self.half_edges[e2].twin_id
  // Forward chain: (forward_prev) -> e1 -> e2 -> (forward_next)
  let has_forward_prev = forward_prev != twin_id && forward_prev != he_id
  let has_forward_next = forward_next != twin_id && forward_next != he_id
  self.half_edges[e1].next_edge = e2
  self.half_edges[e2].prev_edge = e1
  self.half_edges[e1].prev_edge = if has_forward_prev { forward_prev } else { e2 }
  self.half_edges[e2].next_edge = if has_forward_next { forward_next } else { e1 }
  self.half_edges[e1].face_id = forward_face
  self.half_edges[e2].face_id = forward_face
  if has_forward_prev {
    self.half_edges[forward_prev].next_edge = e1
  }
  if has_forward_next {
    self.half_edges[forward_next].prev_edge = e2
  }
  // Twin chain: (twin_prev) -> t2 -> t1 -> (twin_next)
  let has_twin_prev = twin_prev != he_id && twin_prev != twin_id
  let has_twin_next = twin_next != he_id && twin_next != twin_id
  self.half_edges[t2].next_edge = t1
  self.half_edges[t1].prev_edge = t2
  self.half_edges[t2].prev_edge = if has_twin_prev { twin_prev } else { t1 }
  self.half_edges[t1].next_edge = if has_twin_next { twin_next } else { t2 }
  self.half_edges[t1].face_id = twin_face
  self.half_edges[t2].face_id = twin_face
  if has_twin_prev {
    self.half_edges[twin_prev].next_edge = t2
  }
  if has_twin_next {
    self.half_edges[twin_next].prev_edge = t1
  }
  self.incremental_splits = self.incremental_splits + 1
  self.topo_epoch = self.topo_epoch + 1
  (e1, e2)
}

///|
/// Incrementally insert a vector segment `(p_start, p_end)` into the planar topology graph.
/// Every interior crossing with an active edge is detected, the crossed edges are split at
/// their intersection vertices, and the new segment is chained through all of them, so a
/// segment crossing several edges is fully decomposed.
pub fn VectorTopologyGraph::insert_segment_incremental(
  self : VectorTopologyGraph,
  p_start : Vec2,
  p_end : Vec2,
  primitive_id : Int,
) -> Int {
  let u = self.upsert_vertex(p_start)
  let v = self.upsert_vertex(p_end)
  if u == v {
    return -1
  }
  let dx = p_end.x - p_start.x
  let dy = p_end.y - p_start.y
  let len_sq = dx * dx + dy * dy
  // Collect every crossing as (parameter_along_new_segment, vertex_id, half_edge_id)
  let hits : Array[(Double, Int, Int)] = []
  let num_existing = self.half_edges.length()
  let mut i = 0
  while i < num_existing {
    let he = self.half_edges[i]
    if he.active {
      let twin = self.half_edges[he.twin_id]
      let a = self.vertices[he.origin_vertex].pos
      let b = self.vertices[twin.origin_vertex].pos
      match intersect_open_segments(p_start, p_end, a, b) {
        Some(ip) => {
          let vid = self.upsert_vertex(ip)
          if vid != u && vid != v {
            let mut duplicate = false
            for h in hits {
              let (_, hv, _) = h
              if hv == vid {
                duplicate = true
              }
            }
            if !duplicate {
              let t = if len_sq > 1.0e-18 {
                ((ip.x - p_start.x) * dx + (ip.y - p_start.y) * dy) / len_sq
              } else {
                0.0
              }
              hits.push((t, vid, i))
            }
          }
        }
        None => ()
      }
    }
    i = i + 2
  }
  self.topo_epoch = self.topo_epoch + 1
  if hits.length() == 0 {
    return self.add_raw_half_edge_pair(u, v, primitive_id)
  }
  // Order the crossings along the new segment (insertion sort on the parameter)
  for a = 1; a < hits.length(); a = a + 1 {
    let key = hits[a]
    let (key_t, _, _) = key
    let mut b = a - 1
    let mut moving = true
    while b >= 0 && moving {
      let (prev_t, _, _) = hits[b]
      if prev_t > key_t {
        hits[b + 1] = hits[b]
        b = b - 1
      } else {
        moving = false
      }
    }
    hits[b + 1] = key
  }
  // Split every crossed edge at its own intersection vertex
  for h in hits {
    let (_, vid, he_id) = h
    let _ = self.split_edge_incremental(he_id, vid)
  }
  // Chain the sub-segments of the new primitive through the crossings
  let segments : Array[Int] = []
  let mut prev_v = u
  for h in hits {
    let (_, vid, _) = h
    segments.push(self.add_raw_half_edge_pair(prev_v, vid, primitive_id))
    prev_v = vid
  }
  segments.push(self.add_raw_half_edge_pair(prev_v, v, primitive_id))
  for a = 0; a + 1 < segments.length(); a = a + 1 {
    self.half_edges[segments[a]].next_edge = segments[a + 1]
    self.half_edges[segments[a + 1]].prev_edge = segments[a]
  }
  segments[0]
}

///|
/// Incrementally move a topological vertex `v_id` to `new_pos`, bumping its version
/// and returning its affected incident primitive IDs for fine-grained invalidation.
pub fn VectorTopologyGraph::move_vertex_incremental(
  self : VectorTopologyGraph,
  v_id : Int,
  new_pos : Vec2,
) -> Array[Int] {
  let affected : Array[Int] = []
  if v_id < 0 || v_id >= self.vertices.length() {
    return affected
  }
  self.topo_epoch = self.topo_epoch + 1
  self.vertices[v_id].pos = new_pos
  self.vertices[v_id].version = self.topo_epoch
  for he_id in self.vertices[v_id].incident_half_edges {
    if he_id >= 0 && he_id < self.half_edges.length() {
      let he = self.half_edges[he_id]
      if he.active {
        let mut seen = false
        for p in affected {
          if p == he.primitive_id {
            seen = true
          }
        }
        if !seen {
          affected.push(he.primitive_id)
        }
      }
    }
  }
  affected
}

///|
/// Register a closed polygon face from a sequence of vertices, computing its signed area
/// (via Shoelace theorem) and topological winding number.
pub fn VectorTopologyGraph::register_closed_face(
  self : VectorTopologyGraph,
  vertex_loop : Array[Int],
  primitive_id : Int,
) -> Int {
  let n = vertex_loop.length()
  if n < 3 {
    return -1
  }
  let ring_edges : Array[Int] = []
  let mut shoelace2 = 0.0
  for i = 0; i < n; i = i + 1 {
    let u = vertex_loop[i]
    let v = vertex_loop[(i + 1) % n]
    let he = self.add_raw_half_edge_pair(u, v, primitive_id)
    ring_edges.push(he)
    let pu = self.vertices[u].pos
    let pv = self.vertices[v].pos
    shoelace2 = shoelace2 + (pu.x * pv.y - pv.x * pu.y)
  }
  let face_id = self.faces.length()
  for i = 0; i < n; i = i + 1 {
    let cur = ring_edges[i]
    let nxt = ring_edges[(i + 1) % n]
    let prv = ring_edges[(i + n - 1) % n]
    self.half_edges[cur].next_edge = nxt
    self.half_edges[cur].prev_edge = prv
    self.half_edges[cur].face_id = face_id
  }
  let signed_area = 0.5 * shoelace2
  let winding = if signed_area >= 0.0 { 1 } else { -1 }
  self.faces.push({
    id: face_id,
    boundary_half_edge: ring_edges[0],
    signed_area,
    winding_number: winding,
  })
  self.topo_epoch = self.topo_epoch + 1
  face_id
}

///|
/// Count active undirected edges in the planar topology graph.
pub fn VectorTopologyGraph::active_undirected_edge_count(
  self : VectorTopologyGraph,
) -> Int {
  let mut count = 0
  let mut i = 0
  while i < self.half_edges.length() {
    if self.half_edges[i].active {
      count = count + 1
    }
    i = i + 2
  }
  count
}

///|
/// Compute the topological Euler characteristic chi = V - E + F of the active graph.
pub fn VectorTopologyGraph::euler_characteristic(
  self : VectorTopologyGraph,
) -> Int {
  let v = self.vertices.length()
  let e = self.active_undirected_edge_count()
  let f = self.faces.length()
  v - e + f
}

///|
/// Node kind in the Fine-Grained Reactive Dependency Graph (細粒度響應式).
pub(all) enum ReactiveNodeKind {
  SourceSignal
  ComputedSum
  ComputedScale(Double)
  ComputedAabbOffset
}

///|
/// Single Reactive Signal or Computed Node in the Fine-Grained Reactive DAG.
pub(all) struct ReactiveNode {
  id : Int
  kind : ReactiveNodeKind
  mut value : Double
  deps : Array[Int] // upstream signal/computed IDs
  subscribers : Array[Int] // downstream computed IDs
  bound_primitive_id : Int // >= 0 if this node directly drives a render primitive
  mut dirty : Bool
  mut version : Int
}

///|
/// Fine-Grained Reactive Graph (細粒度響應式系統):
/// Tracks exact signal-to-computed-to-primitive dependencies with glitch-free
/// topological propagation so only mutated vector primitives and their dirty rects
/// are recomputed and re-rasterized.
pub(all) struct FineGrainedReactiveGraph {
  nodes : Array[ReactiveNode]
  dirty_primitives_queue : Array[Int]
  mut propagation_passes : Int
  mut recomputed_nodes_count : Int
}

///|
/// Construct a new Fine-Grained Reactive Graph.
pub fn FineGrainedReactiveGraph::new() -> FineGrainedReactiveGraph {
  {
    nodes: [],
    dirty_primitives_queue: [],
    propagation_passes: 0,
    recomputed_nodes_count: 0,
  }
}

///|
/// Create a reactive source signal with `initial_val`, optionally bound to `primitive_id`.
pub fn FineGrainedReactiveGraph::create_signal(
  self : FineGrainedReactiveGraph,
  initial_val : Double,
  bound_primitive_id : Int,
) -> Int {
  let id = self.nodes.length()
  self.nodes.push({
    id,
    kind: SourceSignal,
    value: initial_val,
    deps: [],
    subscribers: [],
    bound_primitive_id,
    dirty: false,
    version: 1,
  })
  id
}

///|
/// Create a fine-grained computed node depending on `deps` and bound to `bound_primitive_id`.
pub fn FineGrainedReactiveGraph::create_computed(
  self : FineGrainedReactiveGraph,
  kind : ReactiveNodeKind,
  deps : Array[Int],
  bound_primitive_id : Int,
) -> Int {
  let id = self.nodes.length()
  self.nodes.push({
    id,
    kind,
    value: 0.0,
    deps: deps.copy(),
    subscribers: [],
    bound_primitive_id,
    dirty: true,
    version: 0,
  })
  for d in deps {
    if d >= 0 && d < self.nodes.length() {
      self.nodes[d].subscribers.push(id)
    }
  }
  // The node is intentionally left dirty: evaluating it here could read a dependency that
  // is created later, so the first `propagate_dirty` evaluates it in dependency order.
  id
}

///|
/// Push a unique primitive ID into `dirty_primitives_queue`.
fn FineGrainedReactiveGraph::mark_primitive_dirty(
  self : FineGrainedReactiveGraph,
  prim_id : Int,
) -> Unit {
  if prim_id < 0 {
    return
  }
  for p in self.dirty_primitives_queue {
    if p == prim_id {
      return
    }
  }
  self.dirty_primitives_queue.push(prim_id)
}

///|
/// Evaluate a single computed node from its upstream dependencies.
fn FineGrainedReactiveGraph::evaluate_node(
  self : FineGrainedReactiveGraph,
  node_id : Int,
) -> Unit {
  let node = self.nodes[node_id]
  let new_val = match node.kind {
    SourceSignal => node.value
    ComputedSum => {
      let mut s = 0.0
      for d in node.deps {
        s = s + self.nodes[d].value
      }
      s
    }
    ComputedScale(factor) =>
      if node.deps.length() > 0 {
        self.nodes[node.deps[0]].value * factor
      } else {
        0.0
      }
    ComputedAabbOffset => {
      let mut acc = 0.0
      for d in node.deps {
        acc = acc + self.nodes[d].value
      }
      acc
    }
  }
  let changed = (new_val - node.value).abs() > 1.0e-12 || node.version == 0
  self.nodes[node_id].value = new_val
  self.nodes[node_id].dirty = false
  if changed {
    self.nodes[node_id].version = self.nodes[node_id].version + 1
    self.recomputed_nodes_count = self.recomputed_nodes_count + 1
    self.mark_primitive_dirty(node.bound_primitive_id)
  }
}

///|
/// Set a source signal's value and recursively mark only its reachable downstream subgraph dirty.
pub fn FineGrainedReactiveGraph::set_signal(
  self : FineGrainedReactiveGraph,
  signal_id : Int,
  new_val : Double,
) -> Unit {
  if signal_id < 0 || signal_id >= self.nodes.length() {
    return
  }
  if (self.nodes[signal_id].value - new_val).abs() <= 1.0e-12 {
    return
  }
  self.nodes[signal_id].value = new_val
  self.nodes[signal_id].version = self.nodes[signal_id].version + 1
  self.mark_primitive_dirty(self.nodes[signal_id].bound_primitive_id)

  // BFS mark downstream computed nodes dirty
  let queue : Array[Int] = []
  for sub in self.nodes[signal_id].subscribers {
    queue.push(sub)
  }
  let mut head = 0
  while head < queue.length() {
    let cur = queue[head]
    head = head + 1
    if !self.nodes[cur].dirty {
      self.nodes[cur].dirty = true
      for nxt in self.nodes[cur].subscribers {
        queue.push(nxt)
      }
    }
  }
}

///|
/// Dependency-first (post-order) evaluation order over the currently dirty nodes.
/// Computed nodes are therefore always evaluated after the nodes they depend on, whatever
/// order they were created in, which is what makes the propagation glitch-free.
fn FineGrainedReactiveGraph::dirty_evaluation_order(
  self : FineGrainedReactiveGraph,
) -> Array[Int] {
  let n = self.nodes.length()
  let state = Array::make(n, 0) // 0 = unvisited, 1 = in progress, 2 = finished
  let order : Array[Int] = []
  let stack : Array[(Int, Int)] = [] // (node id, next dependency index)
  for start = 0; start < n; start = start + 1 {
    if !self.nodes[start].dirty || state[start] != 0 {
      continue
    }
    state[start] = 1
    stack.push((start, 0))
    while stack.length() > 0 {
      let top = stack[stack.length() - 1]
      let (node_id, dep_idx) = top
      let deps = self.nodes[node_id].deps
      if dep_idx < deps.length() {
        stack[stack.length() - 1] = (node_id, dep_idx + 1)
        let dep = deps[dep_idx]
        if dep >= 0 && dep < n && state[dep] == 0 && self.nodes[dep].dirty {
          state[dep] = 1
          stack.push((dep, 0))
        }
      } else {
        let _ = stack.pop()
        state[node_id] = 2
        order.push(node_id)
      }
    }
  }
  order
}

///|
/// Glitch-free topological propagation of all dirty computed nodes.
/// Returns the exact list of primitive IDs invalidated in this reactive transaction.
pub fn FineGrainedReactiveGraph::propagate_dirty(
  self : FineGrainedReactiveGraph,
) -> Array[Int] {
  self.propagation_passes = self.propagation_passes + 1
  let order = self.dirty_evaluation_order()
  for i in order {
    if self.nodes[i].dirty {
      self.evaluate_node(i)
    }
  }
  let out = self.dirty_primitives_queue.copy()
  self.dirty_primitives_queue.clear()
  out
}
