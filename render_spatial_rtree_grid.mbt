///|
/// Spatial Indexing & Dirty-Region Management for the Rendering Engine:
/// - R-tree 區域樹 (Dynamic Guttman R-tree with Quadratic Split & Minimum Enlargement)
/// - 稀疏網格 (Sparse Spatial Hash Grid with Morton Z-Order Curve)
/// - 筆跡叢集化 (Spatio-Temporal & Tangent-Affinity Stroke Clustering + RDP Simplification)
/// - 髒矩形檢測 (Dirty Rectangle Detection & Area-Waste Union Coalescing)

///|
/// Entry stored inside an R-tree node (either a leaf primitive or a child node reference).
pub(all) struct RTreeEntry {
  mut aabb : Aabb
  child_node_id : Int // -1 if leaf entry
  primitive_id : Int // >= 0 if leaf entry
}

///|
/// Node in the Dynamic R-tree Spatial Index (R-tree 區域樹).
pub(all) struct RTreeNode {
  id : Int
  mut is_leaf : Bool
  mut parent_id : Int
  mut aabb : Aabb
  entries : Array[RTreeEntry]
}

///|
/// Dynamic R-tree Spatial Index supporting O(log N) range culling, insertion,
/// quadratic node splitting, and incremental AABB updates.
pub(all) struct RTree {
  max_entries : Int
  nodes : Array[RTreeNode]
  mut root_id : Int
  mut total_queries : Int
  mut visited_nodes_in_queries : Int
}

///|
/// Create a new Dynamic R-tree with `max_entries` per node (minimum 4).
pub fn RTree::new(max_entries : Int) -> RTree {
  let cap = max_entries.max(4)
  let root : RTreeNode = {
    id: 0,
    is_leaf: true,
    parent_id: -1,
    aabb: Aabb::new(0.0, 0.0, 0.0, 0.0),
    entries: [],
  }
  {
    max_entries: cap,
    nodes: [root],
    root_id: 0,
    total_queries: 0,
    visited_nodes_in_queries: 0,
  }
}

///|
/// Recompute the tight bounding box of `node_id` from its entries.
fn RTree::recompute_node_aabb(self : RTree, node_id : Int) -> Unit {
  let entries = self.nodes[node_id].entries
  if entries.length() == 0 {
    self.nodes[node_id].aabb = Aabb::new(0.0, 0.0, 0.0, 0.0)
    return
  }
  let boxes : Array[Aabb] = []
  for e in entries {
    boxes.push(e.aabb)
  }
  self.nodes[node_id].aabb = match Aabb::union_all(boxes) {
    Some(box) => box
    None => Aabb::new(0.0, 0.0, 0.0, 0.0)
  }
}

///|
/// Choose the leaf node that requires the minimum area enlargement to include `box`.
fn RTree::choose_leaf(self : RTree, box : Aabb) -> Int {
  let mut cur = self.root_id
  while !self.nodes[cur].is_leaf {
    let entries = self.nodes[cur].entries
    let mut best_child = entries[0].child_node_id
    let mut best_enlargement = scan_infinity
    let mut best_area = scan_infinity
    for e in entries {
      let cur_area = e.aabb.area()
      let enlarged_area = e.aabb.union(box).area()
      let enlargement = enlarged_area - cur_area
      if enlargement < best_enlargement - tol_eps ||
        (
          (enlargement - best_enlargement).abs() <= tol_eps &&
          cur_area < best_area
        ) {
        best_enlargement = enlargement
        best_area = cur_area
        best_child = e.child_node_id
      }
    }
    cur = best_child
  }
  cur
}

///|
/// Guttman Quadratic Split of an overflowing R-tree node `node_id`.
/// Returns the newly created sibling node ID.
fn RTree::split_node_quadratic(self : RTree, node_id : Int) -> Int {
  let all_entries = self.nodes[node_id].entries.copy()
  let n = all_entries.length()
  // 1. Pick seeds (i0, j0) maximizing dead-space waste: area(E_i U E_j) - area(E_i) - area(E_j)
  let mut seed_a = 0
  let mut seed_b = if n > 1 { 1 } else { 0 }
  let mut max_waste = -scan_infinity
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      let u = all_entries[i].aabb.union(all_entries[j].aabb)
      let waste = u.area() -
        all_entries[i].aabb.area() -
        all_entries[j].aabb.area()
      if waste > max_waste {
        max_waste = waste
        seed_a = i
        seed_b = j
      }
    }
  }

  let new_node_id = self.nodes.length()
  let is_leaf = self.nodes[node_id].is_leaf
  let parent_id = self.nodes[node_id].parent_id
  let new_node : RTreeNode = {
    id: new_node_id,
    is_leaf,
    parent_id,
    aabb: all_entries[seed_b].aabb,
    entries: [all_entries[seed_b]],
  }
  self.nodes.push(new_node)

  self.nodes[node_id].entries.clear()
  self.nodes[node_id].entries.push(all_entries[seed_a])
  self.nodes[node_id].aabb = all_entries[seed_a].aabb

  // Update child parent pointer if internal node
  if !is_leaf {
    let child_b = all_entries[seed_b].child_node_id
    if child_b >= 0 {
      self.nodes[child_b].parent_id = new_node_id
    }
  }

  // 2. Distribute remaining entries by minimum area enlargement.
  // Guttman's minimum-fill rule: a group must receive every remaining entry once that is
  // the only way for it to reach ceil(0.4 * M) entries, so neither group is left too small.
  let min_fill = ((self.max_entries * 2) + 4) / 5
  let mut count_a = 1
  let mut count_b = 1
  let mut remaining = n - 2
  for idx = 0; idx < n; idx = idx + 1 {
    if idx != seed_a && idx != seed_b {
      let e = all_entries[idx]
      let box_a = self.nodes[node_id].aabb
      let box_b = self.nodes[new_node_id].aabb
      let target_id = if count_a + remaining <= min_fill {
        node_id
      } else if count_b + remaining <= min_fill {
        new_node_id
      } else {
        let enl_a = box_a.union(e.aabb).area() - box_a.area()
        let enl_b = box_b.union(e.aabb).area() - box_b.area()
        if enl_a <= enl_b { node_id } else { new_node_id }
      }
      self.nodes[target_id].entries.push(e)
      self.nodes[target_id].aabb = self.nodes[target_id].aabb.union(e.aabb)
      if !is_leaf && e.child_node_id >= 0 {
        self.nodes[e.child_node_id].parent_id = target_id
      }
      if target_id == node_id {
        count_a = count_a + 1
      } else {
        count_b = count_b + 1
      }
      remaining = remaining - 1
    }
  }
  new_node_id
}

///|
/// Adjust R-tree upward from `leaf_id`, propagating AABB updates and node splits.
fn RTree::adjust_tree(
  self : RTree,
  start_id : Int,
  split_sibling : Int,
) -> Unit {
  let mut cur = start_id
  let mut sibling = split_sibling
  while true {
    self.recompute_node_aabb(cur)
    if sibling != -1 {
      self.recompute_node_aabb(sibling)
    }
    let parent = self.nodes[cur].parent_id
    if parent == -1 {
      // If root was split, allocate a new root above `cur` and `sibling`
      if sibling != -1 {
        let new_root_id = self.nodes.length()
        let cur_box = self.nodes[cur].aabb
        let sib_box = self.nodes[sibling].aabb
        let new_root : RTreeNode = {
          id: new_root_id,
          is_leaf: false,
          parent_id: -1,
          aabb: cur_box.union(sib_box),
          entries: [
            { aabb: cur_box, child_node_id: cur, primitive_id: -1, },
            { aabb: sib_box, child_node_id: sibling, primitive_id: -1, },
          ],
        }
        self.nodes.push(new_root)
        self.nodes[cur].parent_id = new_root_id
        self.nodes[sibling].parent_id = new_root_id
        self.root_id = new_root_id
      }
      break
    }
    // Update `cur`'s entry in `parent`
    for i = 0; i < self.nodes[parent].entries.length(); i = i + 1 {
      if self.nodes[parent].entries[i].child_node_id == cur {
        self.nodes[parent].entries[i].aabb = self.nodes[cur].aabb
        break
      }
    }
    let mut next_sibling = -1
    if sibling != -1 {
      self.nodes[parent].entries.push({
        aabb: self.nodes[sibling].aabb,
        child_node_id: sibling,
        primitive_id: -1,
      })
      self.nodes[sibling].parent_id = parent
      if self.nodes[parent].entries.length() > self.max_entries {
        next_sibling = self.split_node_quadratic(parent)
      }
    }
    cur = parent
    sibling = next_sibling
  }
}

///|
/// Insert a primitive with bounding box `aabb` into the R-tree.
pub fn RTree::insert(self : RTree, primitive_id : Int, aabb : Aabb) -> Unit {
  let leaf_id = self.choose_leaf(aabb)
  self.nodes[leaf_id].entries.push({ aabb, child_node_id: -1, primitive_id, })
  let mut split_sib = -1
  if self.nodes[leaf_id].entries.length() > self.max_entries {
    split_sib = self.split_node_quadratic(leaf_id)
  }
  self.adjust_tree(leaf_id, split_sib)
}

///|
/// Incrementally update an existing primitive's AABB in the R-tree and propagate tight bounds
/// upward. The primitive's leaf is located by scanning the leaf nodes (O(N)); the tree does
/// not maintain a primitive -> leaf index.
pub fn RTree::update_primitive_aabb(
  self : RTree,
  primitive_id : Int,
  new_aabb : Aabb,
) -> Bool {
  for nid = 0; nid < self.nodes.length(); nid = nid + 1 {
    if self.nodes[nid].is_leaf {
      for i = 0; i < self.nodes[nid].entries.length(); i = i + 1 {
        if self.nodes[nid].entries[i].primitive_id == primitive_id {
          self.nodes[nid].entries[i].aabb = new_aabb
          // Propagate the change upwards directly through the parent chain rather than
          // rescanning the whole tree.
          let mut cur = nid
          self.recompute_node_aabb(cur)
          let mut parent = self.nodes[cur].parent_id
          while parent != -1 {
            for e = 0; e < self.nodes[parent].entries.length(); e = e + 1 {
              if self.nodes[parent].entries[e].child_node_id == cur {
                self.nodes[parent].entries[e].aabb = self.nodes[cur].aabb
                break
              }
            }
            self.recompute_node_aabb(parent)
            cur = parent
            parent = self.nodes[parent].parent_id
          }
          return true
        }
      }
    }
  }
  false
}

///|
/// Query the R-tree for all `primitive_id`s whose AABB intersects `query_box` (局部剔除).
pub fn RTree::query_aabb(self : RTree, query_box : Aabb) -> Array[Int] {
  self.total_queries = self.total_queries + 1
  let hits : Array[Int] = []
  let stack : Array[Int] = [self.root_id]
  while stack.length() > 0 {
    match stack.pop() {
      Some(nid) => {
        self.visited_nodes_in_queries = self.visited_nodes_in_queries + 1
        let node = self.nodes[nid]
        if node.entries.length() > 0 && node.aabb.intersects(query_box) {
          if node.is_leaf {
            for e in node.entries {
              if e.aabb.intersects(query_box) {
                hits.push(e.primitive_id)
              }
            }
          } else {
            for e in node.entries {
              if e.aabb.intersects(query_box) && e.child_node_id >= 0 {
                stack.push(e.child_node_id)
              }
            }
          }
        }
      }
      None => break
    }
  }
  hits
}

///|
/// Interleave the lower `morton_coord_bits` bits of `tx` and `ty` (each clamped to the
/// representable coordinate range) into a Morton Z-order curve code.
pub fn morton_encode_2d(tx : Int, ty : Int) -> Int {
  let max_coord = (1 << morton_coord_bits) - 1
  let ux = tx.clamp(min=0, max=max_coord)
  let uy = ty.clamp(min=0, max=max_coord)
  let mut code = 0
  for bit = 0; bit < morton_coord_bits; bit = bit + 1 {
    let bx = (ux >> bit) & 1
    let by = (uy >> bit) & 1
    code = code | (bx << (2 * bit)) | (by << (2 * bit + 1))
  }
  code
}

///|
/// Single active cell in the Sparse Spatial Hash Grid (稀疏網格單元).
pub(all) struct SparseTileCell {
  tile_x : Int
  tile_y : Int
  primitives : Array[Int]
}

///|
/// Sparse Spatial Hash Grid (稀疏網格):
/// Divides infinite/large 2D canvas space into `tile_size x tile_size` tiles indexed by
/// Morton Z-order hash, allocating cells only for non-empty tiles.
pub(all) struct SparseSpatialGrid {
  tile_size : Double
  num_buckets : Int
  buckets : Array[Array[SparseTileCell]]
  /// Number of cells that currently hold at least one primitive.
  mut active_tile_count : Int
  /// Total number of cells ever allocated (telemetry only).
  mut total_cells_allocated : Int
}

///|
/// Construct a new Sparse Spatial Hash Grid with `tile_size` (e.g., 16.0 or 32.0 pixels).
pub fn SparseSpatialGrid::new(
  tile_size : Double,
  num_buckets : Int,
) -> SparseSpatialGrid {
  let nb = num_buckets.max(16)
  let buckets : Array[Array[SparseTileCell]] = []
  for _i = 0; _i < nb; _i = _i + 1 {
    buckets.push([])
  }
  {
    tile_size: tile_size.max(4.0),
    num_buckets: nb,
    buckets,
    active_tile_count: 0,
    total_cells_allocated: 0,
  }
}

///|
/// Convert a world coordinate `x` to a signed integer tile index. Coordinates on the
/// negative side of the canvas map to negative tile indices, so the grid really tiles the
/// infinite canvas instead of folding all negative space into column/row 0.
/// (`morton_encode_2d` still clamps the *hash* input to 0..16383; bucket collisions are
/// harmless because a cell is identified by its exact `(tile_x, tile_y)` pair.)
fn SparseSpatialGrid::coord_to_tile(
  self : SparseSpatialGrid,
  c : Double,
) -> Int {
  (c / self.tile_size).floor().to_int()
}

///|
/// Get or create a sparse tile cell at `(tx, ty)`.
fn SparseSpatialGrid::get_or_create_cell(
  self : SparseSpatialGrid,
  tx : Int,
  ty : Int,
) -> (Int, Int) {
  let mkey = morton_encode_2d(tx, ty)
  let b_idx = (mkey & 0x7FFFFFFF) % self.num_buckets
  let bucket = self.buckets[b_idx]
  for i = 0; i < bucket.length(); i = i + 1 {
    if bucket[i].tile_x == tx && bucket[i].tile_y == ty {
      return (b_idx, i)
    }
  }
  let idx = bucket.length()
  bucket.push({
    tile_x: tx,
    tile_y: ty,
    primitives: [],
  })
  self.active_tile_count = self.active_tile_count + 1
  self.total_cells_allocated = self.total_cells_allocated + 1
  (b_idx, idx)
}

///|
/// Insert `primitive_id` into all sparse tiles overlapped by `aabb`.
pub fn SparseSpatialGrid::insert_primitive(
  self : SparseSpatialGrid,
  primitive_id : Int,
  aabb : Aabb,
) -> Unit {
  let tx0 = self.coord_to_tile(aabb.min_x)
  let ty0 = self.coord_to_tile(aabb.min_y)
  let tx1 = self.coord_to_tile(aabb.max_x)
  let ty1 = self.coord_to_tile(aabb.max_y)
  for ty = ty0; ty <= ty1; ty = ty + 1 {
    for tx = tx0; tx <= tx1; tx = tx + 1 {
      let (b_idx, c_idx) = self.get_or_create_cell(tx, ty)
      let prims = self.buckets[b_idx][c_idx].primitives
      let mut exists = false
      for p in prims {
        if p == primitive_id {
          exists = true
        }
      }
      if !exists {
        prims.push(primitive_id)
      }
    }
  }
}

///|
/// Remove `primitive_id` from all sparse tiles overlapped by `old_aabb`.
pub fn SparseSpatialGrid::remove_primitive(
  self : SparseSpatialGrid,
  primitive_id : Int,
  old_aabb : Aabb,
) -> Unit {
  let tx0 = self.coord_to_tile(old_aabb.min_x)
  let ty0 = self.coord_to_tile(old_aabb.min_y)
  let tx1 = self.coord_to_tile(old_aabb.max_x)
  let ty1 = self.coord_to_tile(old_aabb.max_y)
  for ty = ty0; ty <= ty1; ty = ty + 1 {
    for tx = tx0; tx <= tx1; tx = tx + 1 {
      let mkey = morton_encode_2d(tx, ty)
      let b_idx = (mkey & 0x7FFFFFFF) % self.num_buckets
      let bucket = self.buckets[b_idx]
      let mut slot = -1
      for i = 0; i < bucket.length(); i = i + 1 {
        if bucket[i].tile_x == tx && bucket[i].tile_y == ty {
          slot = i
        }
      }
      if slot < 0 {
        continue
      }
      let kept : Array[Int] = []
      for p in bucket[slot].primitives {
        if p != primitive_id {
          kept.push(p)
        }
      }
      bucket[slot].primitives.clear()
      for p in kept {
        bucket[slot].primitives.push(p)
      }
      if bucket[slot].primitives.length() == 0 {
        // Release the emptied cell so the live-tile telemetry reflects reality and the
        // bucket does not accumulate dead cells across frames.
        let last = bucket.length() - 1
        bucket[slot] = bucket[last]
        let _ = bucket.pop()
        self.active_tile_count = (self.active_tile_count - 1).max(0)
      }
    }
  }
}

///|
/// Query unique primitive IDs residing in the sparse tiles overlapped by `region`.
pub fn SparseSpatialGrid::query_primitives_in_rect(
  self : SparseSpatialGrid,
  region : Aabb,
) -> Array[Int] {
  let out : Array[Int] = []
  let tx0 = self.coord_to_tile(region.min_x)
  let ty0 = self.coord_to_tile(region.min_y)
  let tx1 = self.coord_to_tile(region.max_x)
  let ty1 = self.coord_to_tile(region.max_y)
  for ty = ty0; ty <= ty1; ty = ty + 1 {
    for tx = tx0; tx <= tx1; tx = tx + 1 {
      let mkey = morton_encode_2d(tx, ty)
      let b_idx = (mkey & 0x7FFFFFFF) % self.num_buckets
      for cell in self.buckets[b_idx] {
        if cell.tile_x == tx && cell.tile_y == ty {
          for p in cell.primitives {
            let mut seen = false
            for x in out {
              if x == p {
                seen = true
              }
            }
            if !seen {
              out.push(p)
            }
          }
        }
      }
    }
  }
  out
}

///|
/// Sample point along a freehand vector stroke (筆跡採樣點).
pub(all) struct StrokePoint {
  pos : Vec2
  pressure : Double
  timestamp : Double
}

///|
/// Vector Stroke Primitive with simplified LOD polyline and bounding box.
pub(all) struct VectorStroke {
  id : Int
  raw_points : Array[StrokePoint]
  simplified_points : Array[Vec2]
  stroke_width : Double
  aabb : Aabb
  mean_tangent : Vec2
}

///|
/// Perpendicular distance from point `p` to line segment `(a, b)` for Ramer-Douglas-Peucker.
fn point_to_segment_distance(p : Vec2, a : Vec2, b : Vec2) -> Double {
  let dx = b.x - a.x
  let dy = b.y - a.y
  let len_sq = dx * dx + dy * dy
  if len_sq < tol_eps_tight {
    return p.dist(a)
  }
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / len_sq
  let clamped_t = t.clamp(min=0.0, max=1.0)
  let proj : Vec2 = { x: a.x + clamped_t * dx, y: a.y + clamped_t * dy, }
  p.dist(proj)
}

///|
/// Ramer-Douglas-Peucker (RDP) Polyline Simplification reducing stroke vertex count
/// while preserving topological & visual contour within `epsilon`.
pub fn simplify_stroke_rdp(
  points : Array[Vec2],
  epsilon : Double,
) -> Array[Vec2] {
  let n = points.length()
  if n <= 2 {
    return points.copy()
  }
  let keep = Array::make(n, false)
  keep[0] = true
  keep[n - 1] = true
  let stack : Array[(Int, Int)] = [(0, n - 1)]
  while stack.length() > 0 {
    match stack.pop() {
      Some((start_idx, end_idx)) =>
        if end_idx > start_idx + 1 {
          let mut max_dist = -1.0
          let mut split_idx = -1
          let a = points[start_idx]
          let b = points[end_idx]
          for i = start_idx + 1; i < end_idx; i = i + 1 {
            let d = point_to_segment_distance(points[i], a, b)
            if d > max_dist {
              max_dist = d
              split_idx = i
            }
          }
          if max_dist > epsilon && split_idx != -1 {
            keep[split_idx] = true
            stack.push((start_idx, split_idx))
            stack.push((split_idx, end_idx))
          }
        }
      None => break
    }
  }
  let simplified : Array[Vec2] = []
  for i = 0; i < n; i = i + 1 {
    if keep[i] {
      simplified.push(points[i])
    }
  }
  simplified
}

///|
/// Construct a `VectorStroke` from raw ink samples, automatically computing its
/// RDP simplified contour, inflated AABB, and unit mean tangent vector.
pub fn VectorStroke::from_samples(
  id : Int,
  raw_points : Array[StrokePoint],
  stroke_width : Double,
  rdp_epsilon : Double,
) -> VectorStroke {
  let pts : Array[Vec2] = []
  for sp in raw_points {
    pts.push(sp.pos)
  }
  let simplified = simplify_stroke_rdp(pts, rdp_epsilon)
  let base_aabb = match Aabb::from_points(simplified) {
    Some(box) => box.inflate(stroke_width * 0.5 + 1.0)
    None => Aabb::new(0.0, 0.0, 0.0, 0.0)
  }
  let mut tx = 1.0
  let mut ty = 0.0
  if simplified.length() >= 2 {
    let first = simplified[0]
    let last = simplified[simplified.length() - 1]
    let dx = last.x - first.x
    let dy = last.y - first.y
    let len = (dx * dx + dy * dy).sqrt()
    if len > tol_eps {
      tx = dx / len
      ty = dy / len
    }
  }
  {
    id,
    raw_points,
    simplified_points: simplified,
    stroke_width,
    aabb: base_aabb,
    mean_tangent: { x: tx, y: ty, },
  }
}

///|
/// Cluster of spatially and directionally coherent vector strokes (筆跡叢集).
pub(all) struct StrokeCluster {
  cluster_id : Int
  stroke_ids : Array[Int]
  mut merged_aabb : Aabb
  mut centroid : Vec2
  /// Running average of the member strokes' unit tangents, used to pick the best-fitting
  /// cluster among the candidates whose boxes overlap a new stroke.
  mut mean_tangent : Vec2
  mut total_raw_vertices : Int
  mut total_simplified_vertices : Int
}

///|
/// Stroke Clustering Engine (筆跡叢集化引擎):
/// Groups individual strokes into spatial-directional clusters so whole stroke groups
/// share cached tile layers, batch VBO slices, and single-step R-tree culling.
pub(all) struct StrokeClusterEngine {
  spatial_radius : Double
  clusters : Array[StrokeCluster]
}

///|
/// Create a new StrokeClusterEngine with proximity threshold `spatial_radius`.
pub fn StrokeClusterEngine::new(spatial_radius : Double) -> StrokeClusterEngine {
  { spatial_radius, clusters: [], }
}

///|
/// Insert a `VectorStroke` into the best matching cluster (by AABB proximity, then tangent
/// affinity) or allocate a new cluster if no existing cluster is within `spatial_radius`.
/// The proximity test of the inflated boxes decides which clusters are candidates; among
/// those candidates the one whose accumulated `mean_tangent` best agrees with the stroke's
/// own tangent is chosen, with the overlap area as a tie-break. That is what makes the
/// clustering spatial-directional rather than purely spatial.
pub fn StrokeClusterEngine::add_stroke_to_clusters(
  self : StrokeClusterEngine,
  stroke : VectorStroke,
) -> Int {
  let expanded_box = stroke.aabb.inflate(self.spatial_radius)
  let stroke_center : Vec2 = {
    x: 0.5 * (stroke.aabb.min_x + stroke.aabb.max_x),
    y: 0.5 * (stroke.aabb.min_y + stroke.aabb.max_y),
  }
  let mut best_idx = -1
  let mut best_affinity = -2.0
  let mut best_overlap = -1.0
  for i = 0; i < self.clusters.length(); i = i + 1 {
    if self.clusters[i].merged_aabb.intersects(expanded_box) {
      let overlap = match stroke.aabb.intersection(self.clusters[i].merged_aabb) {
        Some(box) => box.area()
        None => 0.0
      }
      let affinity = stroke.mean_tangent.x * self.clusters[i].mean_tangent.x +
        stroke.mean_tangent.y * self.clusters[i].mean_tangent.y
      if affinity > best_affinity + tol_eps ||
        ((affinity - best_affinity).abs() <= tol_eps && overlap > best_overlap) {
        best_affinity = affinity
        best_overlap = overlap
        best_idx = i
      }
    }
  }
  if best_idx >= 0 {
    self.clusters[best_idx].stroke_ids.push(stroke.id)
    self.clusters[best_idx].merged_aabb = self.clusters[best_idx].merged_aabb.union(
      stroke.aabb,
    )
    let k = self.clusters[best_idx].stroke_ids.length().to_double()
    self.clusters[best_idx].centroid = {
      x: (self.clusters[best_idx].centroid.x * (k - 1.0) + stroke_center.x) / k,
      y: (self.clusters[best_idx].centroid.y * (k - 1.0) + stroke_center.y) / k,
    }
    self.clusters[best_idx].mean_tangent = {
      x: (self.clusters[best_idx].mean_tangent.x * (k - 1.0) + stroke.mean_tangent.x) / k,
      y: (self.clusters[best_idx].mean_tangent.y * (k - 1.0) + stroke.mean_tangent.y) / k,
    }
    self.clusters[best_idx].total_raw_vertices = self.clusters[best_idx].total_raw_vertices +
      stroke.raw_points.length()
    self.clusters[best_idx].total_simplified_vertices = self.clusters[best_idx].total_simplified_vertices +
      stroke.simplified_points.length()
    return self.clusters[best_idx].cluster_id
  }
  let cid = self.clusters.length()
  self.clusters.push({
    cluster_id: cid,
    stroke_ids: [stroke.id],
    merged_aabb: stroke.aabb,
    centroid: stroke_center,
    mean_tangent: stroke.mean_tangent,
    total_raw_vertices: stroke.raw_points.length(),
    total_simplified_vertices: stroke.simplified_points.length(),
  })
  cid
}

///|
/// Dirty Rectangle Tracker & Coalescer (髒矩形檢測與合併器).
pub(all) struct DirtyRectTracker {
  viewport_width : Double
  viewport_height : Double
  coalesce_ratio : Double // e.g., 1.25: merge if union_area <= 1.25 * (area_a + area_b)
  raw_dirty_rects : Array[Aabb]
  coalesced_dirty_rects : Array[Aabb]
  mut total_coalesce_merges : Int
}

///|
/// Construct a DirtyRectTracker for a viewport `[0, width] x [0, height]`.
pub fn DirtyRectTracker::new(
  viewport_width : Double,
  viewport_height : Double,
  coalesce_ratio : Double,
) -> DirtyRectTracker {
  {
    viewport_width,
    viewport_height,
    coalesce_ratio,
    raw_dirty_rects: [],
    coalesced_dirty_rects: [],
    total_coalesce_merges: 0,
  }
}

///|
/// Record a dirty region (e.g. old AABB before mutation or new AABB after mutation),
/// automatically clipped to the viewport boundaries.
pub fn DirtyRectTracker::mark_dirty_aabb(
  self : DirtyRectTracker,
  region : Aabb,
) -> Unit {
  let viewport : Aabb = {
    min_x: 0.0,
    min_y: 0.0,
    max_x: self.viewport_width,
    max_y: self.viewport_height,
  }
  match region.intersection(viewport) {
    Some(clipped) =>
      if clipped.area() > tol_eps_mesh {
        self.raw_dirty_rects.push(clipped)
      }
    None => ()
  }
}

///|
/// Coalesce overlapping or nearby dirty rectangles using the area-waste union criterion:
/// merges (R_i, R_j) whenever R_i.intersects(R_j) OR Area(R_i U R_j) <= coalesce_ratio * (Area(R_i) + Area(R_j)).
pub fn DirtyRectTracker::coalesce_dirty_regions(
  self : DirtyRectTracker,
) -> Array[Aabb] {
  let working = self.raw_dirty_rects.copy()
  let mut merged_any = true
  while merged_any {
    merged_any = false
    let n = working.length()
    for i = 0; i < n && !merged_any; i = i + 1 {
      for j = i + 1; j < n && !merged_any; j = j + 1 {
        let a = working[i]
        let b = working[j]
        let u = a.union(b)
        let sum_area = a.area() + b.area()
        if a.intersects(b) || u.area() <= self.coalesce_ratio * sum_area + dirty_coalesce_area_slack {
          working[i] = u
          // Remove j by swapping with last element
          let last_idx = working.length() - 1
          working[j] = working[last_idx]
          let _ = working.pop()
          self.total_coalesce_merges = self.total_coalesce_merges + 1
          merged_any = true
        }
      }
    }
  }
  self.coalesced_dirty_rects.clear()
  for r in working {
    self.coalesced_dirty_rects.push(r)
  }
  self.raw_dirty_rects.clear()
  self.coalesced_dirty_rects.copy()
}
