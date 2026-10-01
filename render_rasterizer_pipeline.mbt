///|
/// Full & Local Scissor Rasterizer (光柵 & 局部光柵),
/// 4x RGSS Rotated-Grid Super-Sampling + SDF Anti-Aliasing (反鋸齒),
/// R-Tree + Sparse Grid Local Culling (局部剔除), and
/// End-to-End Incremental Rendering Engine (增量渲染系統邏輯).

///|
/// 2D RGBA Framebuffer supporting full and local scissor-rect rasterization.
pub(all) struct Framebuffer {
  width : Int
  height : Int
  pixels : Array[ColorRgba]
  bg_color : ColorRgba
  mut pixels_shaded_total : Int
  mut subsamples_tested_total : Int
}

///|
/// Allocate a new Framebuffer of `width x height` initialized to `bg_color`.
pub fn Framebuffer::new(
  width : Int,
  height : Int,
  bg_color : ColorRgba,
) -> Framebuffer {
  let w = width.max(1)
  let h = height.max(1)
  let pixels = Array::make(w * h, bg_color)
  {
    width: w,
    height: h,
    pixels,
    bg_color,
    pixels_shaded_total: 0,
    subsamples_tested_total: 0,
  }
}

///|
/// Clear only the pixels inside a local `scissor` AABB to `bg_color` (局部光柵清理).
pub fn Framebuffer::clear_scissor_rect(
  self : Framebuffer,
  scissor : Aabb,
) -> Int {
  // A scissor that lies fully outside the framebuffer must clear nothing; clamping its
  // coordinates directly would silently fold it onto row/column 0.
  if scissor.max_x < 0.0 ||
    scissor.max_y < 0.0 ||
    scissor.min_x >= self.width.to_double() ||
    scissor.min_y >= self.height.to_double() {
    return 0
  }
  let x0 = scissor.min_x.floor().to_int().clamp(min=0, max=self.width - 1)
  let y0 = scissor.min_y.floor().to_int().clamp(min=0, max=self.height - 1)
  let x1 = scissor.max_x.ceil().to_int().clamp(min=0, max=self.width - 1)
  let y1 = scissor.max_y.ceil().to_int().clamp(min=0, max=self.height - 1)
  let mut cleared = 0
  for y = y0; y <= y1; y = y + 1 {
    let row = y * self.width
    for x = x0; x <= x1; x = x + 1 {
      self.pixels[row + x] = self.bg_color
      cleared = cleared + 1
    }
  }
  cleared
}

///|
/// Read pixel at `(x, y)`.
pub fn Framebuffer::get_pixel(
  self : Framebuffer,
  x : Int,
  y : Int,
) -> ColorRgba {
  if x < 0 || x >= self.width || y < 0 || y >= self.height {
    return self.bg_color
  }
  self.pixels[y * self.width + x]
}

///|
/// 2D Half-Space Edge Function: E(a, b, p) = (p.x - a.x)*(b.y - a.y) - (p.y - a.y)*(b.x - a.x).
fn edge_function(a : Vec2, b : Vec2, p : Vec2) -> Double {
  (p.x - a.x) * (b.y - a.y) - (p.y - a.y) * (b.x - a.x)
}

///|
/// Rasterize a single triangle `(v0, v1, v2)` clipped to `scissor_rect` (局部光柵)
/// using 4x RGSS (Rotated-Grid Super-Sampling) Anti-Aliasing (反鋸齒) and
/// programmable `shader` + `sdf_atlas`.
/// Returns the number of pixels shaded inside `scissor_rect`.
pub fn Framebuffer::rasterize_triangle_local_aa(
  self : Framebuffer,
  v0 : GpuVertex,
  v1 : GpuVertex,
  v2 : GpuVertex,
  shader : FragmentShaderProgram,
  sdf_atlas : SdfTextureAtlas,
  scissor_rect : Aabb,
) -> Int {
  let p0 : Vec2 = { x: v0.x, y: v0.y, }
  let p1 : Vec2 = { x: v1.x, y: v1.y, }
  let p2 : Vec2 = { x: v2.x, y: v2.y, }
  let area2 = edge_function(p0, p1, p2)
  if area2.abs() < 1.0e-8 {
    return 0
  }
  let sign = if area2 > 0.0 { 1.0 } else { -1.0 }
  let inv_area = 1.0 / (area2 * sign)

  // Compute triangle AABB intersected with local scissor_rect and screen bounds
  let tri_min_x = p0.x.min(p1.x).min(p2.x).max(scissor_rect.min_x)
  let tri_min_y = p0.y.min(p1.y).min(p2.y).max(scissor_rect.min_y)
  let tri_max_x = p0.x.max(p1.x).max(p2.x).min(scissor_rect.max_x)
  let tri_max_y = p0.y.max(p1.y).max(p2.y).min(scissor_rect.max_y)

  if tri_min_x > tri_max_x || tri_min_y > tri_max_y {
    return 0
  }

  let x0 = tri_min_x.floor().to_int().clamp(min=0, max=self.width - 1)
  let y0 = tri_min_y.floor().to_int().clamp(min=0, max=self.height - 1)
  let x1 = tri_max_x.ceil().to_int().clamp(min=0, max=self.width - 1)
  let y1 = tri_max_y.ceil().to_int().clamp(min=0, max=self.height - 1)

  // 4x Rotated Grid Super-Sampling (RGSS) sub-pixel offsets
  let rgss_offsets : Array[(Double, Double)] = [
    (0.125, 0.375),
    (-0.375, 0.125),
    (0.375, -0.125),
    (-0.125, -0.375),
  ]

  let mut shaded_Here = 0
  for py = y0; py <= y1; py = py + 1 {
    let cy = py.to_double() + 0.5
    let row_offset = py * self.width
    for px = x0; px <= x1; px = px + 1 {
      let cx = px.to_double() + 0.5
      let mut covered_samples = 0
      let mut sum_w0 = 0.0
      let mut sum_w1 = 0.0
      let mut sum_w2 = 0.0

      for offset in rgss_offsets {
        let (ox, oy) = offset
        let sp : Vec2 = { x: cx + ox, y: cy + oy, }
        self.subsamples_tested_total = self.subsamples_tested_total + 1
        let e0 = edge_function(p1, p2, sp) * sign
        let e1 = edge_function(p2, p0, sp) * sign
        let e2 = edge_function(p0, p1, sp) * sign
        if e0 >= -1.0e-7 && e1 >= -1.0e-7 && e2 >= -1.0e-7 {
          covered_samples = covered_samples + 1
          sum_w0 = sum_w0 + e0 * inv_area
          sum_w1 = sum_w1 + e1 * inv_area
          sum_w2 = sum_w2 + e2 * inv_area
        }
      }

      if covered_samples > 0 {
        let cov_count_f = covered_samples.to_double()
        let coverage = cov_count_f * 0.25
        let b0 = (sum_w0 / cov_count_f).clamp(min=0.0, max=1.0)
        let b1 = (sum_w1 / cov_count_f).clamp(min=0.0, max=1.0)
        let b2 = (sum_w2 / cov_count_f).clamp(min=0.0, max=1.0)

        let u = b0 * v0.u + b1 * v1.u + b2 * v2.u
        let v = b0 * v0.v + b1 * v1.v + b2 * v2.v
        let interp_color : ColorRgba = {
          r: b0 * v0.color.r + b1 * v1.color.r + b2 * v2.color.r,
          g: b0 * v0.color.g + b1 * v1.color.g + b2 * v2.color.g,
          b: b0 * v0.color.b + b1 * v1.color.b + b2 * v2.color.b,
          a: b0 * v0.color.a + b1 * v1.color.a + b2 * v2.color.a,
        }
        let raw_frag = execute_fragment_shader(
          shader,
          { x: cx, y: cy, },
          { x: u, y: v, },
          interp_color,
          sdf_atlas,
        )
        let aa_frag : ColorRgba = { ..raw_frag, a: raw_frag.a * coverage, }
        if aa_frag.a > 1.0e-5 {
          let dst = self.pixels[row_offset + px]
          self.pixels[row_offset + px] = blend_src_over(aa_frag, dst)
          shaded_Here = shaded_Here + 1
          self.pixels_shaded_total = self.pixels_shaded_total + 1
        }
      }
    }
  }
  shaded_Here
}

///|
/// Rasterize a `ZeroCopyBufferSlice` directly from `arena` within `scissor_rect`.
pub fn Framebuffer::rasterize_slice_zero_copy_local(
  self : Framebuffer,
  arena : ZeroCopyVertexArena,
  slice : ZeroCopyBufferSlice,
  transform : Affine2D,
  shader : FragmentShaderProgram,
  sdf_atlas : SdfTextureAtlas,
  scissor_rect : Aabb,
) -> Int {
  let mut shaded = 0
  let mut i = 0
  while i + 2 < slice.index_count {
    let idx0 = arena.raw_ibo_indices[slice.ibo_index_offset + i]
    let idx1 = arena.raw_ibo_indices[slice.ibo_index_offset + i + 1]
    let idx2 = arena.raw_ibo_indices[slice.ibo_index_offset + i + 2]
    let v0 = execute_vertex_shader(arena.read_global_vertex(idx0), transform)
    let v1 = execute_vertex_shader(arena.read_global_vertex(idx1), transform)
    let v2 = execute_vertex_shader(arena.read_global_vertex(idx2), transform)
    shaded = shaded +
      self.rasterize_triangle_local_aa(
        v0, v1, v2, shader, sdf_atlas, scissor_rect,
      )
    i = i + 3
  }
  shaded
}

///|
/// Scene Primitive registered in the Incremental Rendering Engine.
pub(all) struct RenderPrimitive {
  id : Int
  mut slice : ZeroCopyBufferSlice
  mut aabb : Aabb
  shader : FragmentShaderProgram
  mut transform : Affine2D
  tx_signal_id : Int
  ty_signal_id : Int
  computed_aabb_node_id : Int
  mut prev_tx : Double
  mut prev_ty : Double
}

///|
/// Telemetry metrics returned after each Incremental Render Frame.
pub(all) struct FrameRenderMetrics {
  frame_index : Int
  dirty_primitives_count : Int
  coalesced_dirty_rects_count : Int
  dirty_area_ratio : Double
  primitives_drawn : Int
  primitives_locally_culled : Int
  pixels_shaded_in_frame : Int
  subsamples_evaluated_in_frame : Int
  zero_copy_in_place_updates : Int
  active_sparse_tiles : Int
  stroke_clusters_count : Int
  topology_vertices : Int
  topology_half_edges : Int
}

///|
/// Unified Incremental Vector & Raster Rendering System (增量渲染引擎):
/// Combines Vector Incremental Topology, Fine-Grained Reactivity, R-Tree, Sparse Grid,
/// Stroke Clustering, Dirty Rectangle Coalescing, Zero-Copy VBO/IBO Arena, SDF Texture Atlas,
/// Programmable Shaders, Local Culling, and 4x RGSS Anti-Aliased Local Rasterization.
pub(all) struct IncrementalRenderEngine {
  width : Int
  height : Int
  topology : VectorTopologyGraph
  reactive : FineGrainedReactiveGraph
  rtree : RTree
  sparse_grid : SparseSpatialGrid
  stroke_clusterer : StrokeClusterEngine
  dirty_tracker : DirtyRectTracker
  vbo_arena : ZeroCopyVertexArena
  sdf_atlas : SdfTextureAtlas
  framebuffer : Framebuffer
  primitives : Array[RenderPrimitive]
  mut frame_counter : Int
}

///|
/// Create and initialize the Unified Incremental Rendering Engine.
pub fn IncrementalRenderEngine::new(
  width : Int,
  height : Int,
  tile_size : Double,
) -> IncrementalRenderEngine {
  let sdf_shapes : Array[SdfShapeKind] = [
    SdfCircle({ x: 0.5, y: 0.5, }, 0.36),
    SdfCapsule({ x: 0.25, y: 0.5, }, { x: 0.75, y: 0.5, }, 0.18),
  ]
  let sdf_atlas = SdfTextureAtlas::bake_from_shapes(32, 32, sdf_shapes)
  {
    width,
    height,
    topology: VectorTopologyGraph::new(0.05),
    reactive: FineGrainedReactiveGraph::new(),
    rtree: RTree::new(4),
    sparse_grid: SparseSpatialGrid::new(tile_size, 64),
    stroke_clusterer: StrokeClusterEngine::new(24.0),
    dirty_tracker: DirtyRectTracker::new(
      width.to_double(),
      height.to_double(),
      1.20,
    ),
    vbo_arena: ZeroCopyVertexArena::new(),
    sdf_atlas,
    framebuffer: Framebuffer::new(
      width,
      height,
      ColorRgba::new(0.06, 0.08, 0.12, 1.0),
    ),
    primitives: [],
    frame_counter: 0,
  }
}

///|
/// Add a vector quad primitive `(min_x, min_y, max_x, max_y)` with `shader` and `color`
/// into the engine:
/// 1. Registers closed polygon face & half-edges in `VectorTopologyGraph`
/// 2. Allocates zero-copy interleaved vertices & triangle indices in `ZeroCopyVertexArena`
/// 3. Creates fine-grained reactive signals `(tx, ty)` and computed AABB dependency node
/// 4. Inserts into `RTree` and `SparseSpatialGrid`, and marks initial `DirtyRect`.
pub fn IncrementalRenderEngine::add_vector_quad(
  self : IncrementalRenderEngine,
  min_x : Double,
  min_y : Double,
  max_x : Double,
  max_y : Double,
  color : ColorRgba,
  shader : FragmentShaderProgram,
) -> Int {
  let prim_id = self.primitives.length()

  // 1. Register planar topology vertices and closed face
  let tv0 = self.topology.upsert_vertex({ x: min_x, y: min_y, })
  let tv1 = self.topology.upsert_vertex({ x: max_x, y: min_y, })
  let tv2 = self.topology.upsert_vertex({ x: max_x, y: max_y, })
  let tv3 = self.topology.upsert_vertex({ x: min_x, y: max_y, })
  let _ = self.topology.register_closed_face([tv0, tv1, tv2, tv3], prim_id)

  // 2. Allocate Zero-Copy VBO/IBO Slice
  let verts : Array[GpuVertex] = [
    { x: min_x, y: min_y, u: 0.0, v: 0.0, color, },
    { x: max_x, y: min_y, u: 1.0, v: 0.0, color, },
    { x: max_x, y: max_y, u: 1.0, v: 1.0, color, },
    { x: min_x, y: max_y, u: 0.0, v: 1.0, color, },
  ]
  let indices : Array[Int] = [0, 1, 2, 0, 2, 3]
  let slice = self.vbo_arena.allocate_mesh_zero_copy(verts, indices)
  let aabb = Aabb::new(min_x, min_y, max_x, max_y).inflate(1.0)

  // 3. Create Fine-Grained Reactive Signals for translation (tx, ty)
  let tx_sig = self.reactive.create_signal(0.0, prim_id)
  let ty_sig = self.reactive.create_signal(0.0, prim_id)
  let comp_node = self.reactive.create_computed(
    ComputedAabbOffset,
    [tx_sig, ty_sig],
    prim_id,
  )

  // 4. Register in R-Tree, Sparse Grid, and Dirty Rect Tracker
  self.rtree.insert(prim_id, aabb)
  self.sparse_grid.insert_primitive(prim_id, aabb)
  self.dirty_tracker.mark_dirty_aabb(aabb)

  self.primitives.push({
    id: prim_id,
    slice,
    aabb,
    shader,
    transform: Affine2D::identity(),
    tx_signal_id: tx_sig,
    ty_signal_id: ty_sig,
    computed_aabb_node_id: comp_node,
    prev_tx: 0.0,
    prev_ty: 0.0,
  })
  prim_id
}

///|
/// Add a freehand ink/vector stroke into the engine:
/// 1. Simplifies raw samples via Ramer-Douglas-Peucker (`VectorStroke::from_samples`)
/// 2. Assigns the stroke to a spatial-directional cluster in `StrokeClusterEngine`
/// 3. Incrementally inserts stroke segments (with planar intersection splitting!) into `VectorTopologyGraph`
/// 4. Extrudes the simplified polyline into a triangle strip in `ZeroCopyVertexArena`
/// 5. Inserts into `RTree`, `SparseSpatialGrid`, and `DirtyRectTracker`.
/// Returns `(primitive_id, cluster_id)`.
pub fn IncrementalRenderEngine::add_clustered_vector_stroke(
  self : IncrementalRenderEngine,
  samples : Array[StrokePoint],
  stroke_width : Double,
  color : ColorRgba,
) -> (Int, Int) {
  let prim_id = self.primitives.length()
  let stroke = VectorStroke::from_samples(prim_id, samples, stroke_width, 0.75)
  let cluster_id = self.stroke_clusterer.add_stroke_to_clusters(stroke)

  let pts = stroke.simplified_points
  let verts : Array[GpuVertex] = []
  let indices : Array[Int] = []
  let half_w = (stroke_width * 0.5).max(1.0)

  for i = 0; i + 1 < pts.length(); i = i + 1 {
    let a = pts[i]
    let b = pts[i + 1]
    let _ = self.topology.insert_segment_incremental(a, b, prim_id)
    let dx = b.x - a.x
    let dy = b.y - a.y
    let len = (dx * dx + dy * dy).sqrt().max(1.0e-6)
    let nx = -dy / len * half_w
    let ny = dx / len * half_w
    let base = verts.length()
    verts.push({ x: a.x + nx, y: a.y + ny, u: 0.0, v: 0.0, color, })
    verts.push({ x: a.x - nx, y: a.y - ny, u: 0.0, v: 1.0, color, })
    verts.push({ x: b.x - nx, y: b.y - ny, u: 1.0, v: 1.0, color, })
    verts.push({ x: b.x + nx, y: b.y + ny, u: 1.0, v: 0.0, color, })
    indices.push(base)
    indices.push(base + 1)
    indices.push(base + 2)
    indices.push(base)
    indices.push(base + 2)
    indices.push(base + 3)
  }

  let slice = self.vbo_arena.allocate_mesh_zero_copy(verts, indices)
  let aabb = stroke.aabb
  let tx_sig = self.reactive.create_signal(0.0, prim_id)
  let ty_sig = self.reactive.create_signal(0.0, prim_id)
  let comp_node = self.reactive.create_computed(
    ComputedAabbOffset,
    [tx_sig, ty_sig],
    prim_id,
  )

  self.rtree.insert(prim_id, aabb)
  self.sparse_grid.insert_primitive(prim_id, aabb)
  self.dirty_tracker.mark_dirty_aabb(aabb)

  self.primitives.push({
    id: prim_id,
    slice,
    aabb,
    shader: FlatColorShader(color),
    transform: Affine2D::identity(),
    tx_signal_id: tx_sig,
    ty_signal_id: ty_sig,
    computed_aabb_node_id: comp_node,
    prev_tx: 0.0,
    prev_ty: 0.0,
  })
  (prim_id, cluster_id)
}

///|
/// Mutate a primitive's position via its fine-grained reactive signals `(tx, ty)`.
/// Only this primitive (and any downstream dependents) will be marked dirty on the next frame!
pub fn IncrementalRenderEngine::set_primitive_translation_reactive(
  self : IncrementalRenderEngine,
  prim_id : Int,
  new_tx : Double,
  new_ty : Double,
) -> Unit {
  if prim_id < 0 || prim_id >= self.primitives.length() {
    return
  }
  let p = self.primitives[prim_id]
  self.reactive.set_signal(p.tx_signal_id, new_tx)
  self.reactive.set_signal(p.ty_signal_id, new_ty)
}

///|
/// Perform Local Culling (局部剔除) for a `dirty_rect` by intersecting R-Tree spatial queries
/// and Sparse Spatial Grid tile queries, returning sorted visible primitive IDs.
pub fn IncrementalRenderEngine::local_cull_for_dirty_rect(
  self : IncrementalRenderEngine,
  dirty_rect : Aabb,
) -> Array[Int] {
  let rtree_hits = self.rtree.query_aabb(dirty_rect)
  let grid_hits = self.sparse_grid.query_primitives_in_rect(dirty_rect)
  let visible : Array[Int] = []
  for pid in rtree_hits {
    let mut in_grid = false
    for g in grid_hits {
      if g == pid {
        in_grid = true
        break
      }
    }
    if in_grid {
      let mut already = false
      for v in visible {
        if v == pid {
          already = true
        }
      }
      if !already {
        visible.push(pid)
      }
    }
  }
  // Sort ascending by primitive ID (painter's draw order)
  for i = 1; i < visible.length(); i = i + 1 {
    let key = visible[i]
    let mut j = i - 1
    while j >= 0 && visible[j] > key {
      visible[j + 1] = visible[j]
      j = j - 1
    }
    visible[j + 1] = key
  }
  visible
}

///|
/// Execute one complete Incremental Render Frame (增量渲染主管線):
/// 1. Propagate fine-grained reactive signals -> get dirty primitives
/// 2. For each dirty primitive: record old AABB in DirtyRectTracker, patch VBO in-place (zero-copy),
///    update R-Tree and Sparse Grid, and record new AABB in DirtyRectTracker
/// 3. Coalesce Dirty Rectangles
/// 4. For each coalesced Dirty Rectangle:
///    - Clear only the dirty scissor region
///    - Run Local Culling via R-Tree + Sparse Grid
///    - Locally rasterize only visible primitives inside the scissor rect with 4x RGSS + SDF AA!
pub fn IncrementalRenderEngine::render_incremental_frame(
  self : IncrementalRenderEngine,
) -> FrameRenderMetrics {
  self.frame_counter = self.frame_counter + 1
  let prev_shaded = self.framebuffer.pixels_shaded_total
  let prev_subsamples = self.framebuffer.subsamples_tested_total
  let prev_in_place = self.vbo_arena.in_place_mutations

  // 1. Fine-Grained Reactive Propagation
  let dirty_prims = self.reactive.propagate_dirty()

  // 2. Zero-Copy VBO In-Place Patch + Spatial Index Update + Dirty Rect Registration
  for pid in dirty_prims {
    if pid >= 0 && pid < self.primitives.length() {
      let p = self.primitives[pid]
      let cur_tx = self.reactive.nodes[p.tx_signal_id].value
      let cur_ty = self.reactive.nodes[p.ty_signal_id].value
      let dx = cur_tx - p.prev_tx
      let dy = cur_ty - p.prev_ty
      if dx.abs() > 1.0e-9 || dy.abs() > 1.0e-9 {
        // Mark old AABB dirty so old trail is erased
        self.dirty_tracker.mark_dirty_aabb(p.aabb)
        self.sparse_grid.remove_primitive(pid, p.aabb)

        // Zero-copy in-place vertex buffer mutation
        let updated_slice = self.vbo_arena.translate_slice_in_place(
          p.slice,
          dx,
          dy,
        )
        let new_aabb = self.vbo_arena
          .compute_slice_aabb(updated_slice)
          .inflate(1.0)
        self.primitives[pid].slice = updated_slice
        self.primitives[pid].aabb = new_aabb
        self.primitives[pid].prev_tx = cur_tx
        self.primitives[pid].prev_ty = cur_ty

        // Update R-Tree, Sparse Grid, and mark new AABB dirty
        let _ = self.rtree.update_primitive_aabb(pid, new_aabb)
        self.sparse_grid.insert_primitive(pid, new_aabb)
        self.dirty_tracker.mark_dirty_aabb(new_aabb)
      }
    }
  }

  // 3. Coalesce Dirty Rectangles
  let dirty_rects = self.dirty_tracker.coalesce_dirty_regions()
  let mut dirty_area = 0.0
  for dr in dirty_rects {
    dirty_area = dirty_area + dr.area()
  }
  let total_screen_area = (self.width * self.height).max(1).to_double()
  let dirty_ratio = (dirty_area / total_screen_area).clamp(min=0.0, max=1.0)

  // 4. Local Culling + Local Scissor Rasterization per Dirty Rectangle.
  // The scissor only clips work done while its dirty rectangle is being repainted; it is a
  // work-reduction window for this frame, not a persistent stencil buffer.
  let drawn_map = Array::make(self.primitives.length(), false)
  for dr in dirty_rects {
    let _ = self.framebuffer.clear_scissor_rect(dr)
    let visible_ids = self.local_cull_for_dirty_rect(dr)
    for pid in visible_ids {
      if pid >= 0 && pid < self.primitives.length() {
        drawn_map[pid] = true
        let prim = self.primitives[pid]
        let _ = self.framebuffer.rasterize_slice_zero_copy_local(
          self.vbo_arena,
          prim.slice,
          prim.transform,
          prim.shader,
          self.sdf_atlas,
          dr,
        )
      }
    }
  }

  let mut drawn_count = 0
  for d in drawn_map {
    if d {
      drawn_count = drawn_count + 1
    }
  }
  let culled_count = self.primitives.length() - drawn_count

  {
    frame_index: self.frame_counter,
    dirty_primitives_count: dirty_prims.length(),
    coalesced_dirty_rects_count: dirty_rects.length(),
    dirty_area_ratio: dirty_ratio,
    primitives_drawn: drawn_count,
    primitives_locally_culled: culled_count,
    pixels_shaded_in_frame: self.framebuffer.pixels_shaded_total - prev_shaded,
    subsamples_evaluated_in_frame: self.framebuffer.subsamples_tested_total -
    prev_subsamples,
    zero_copy_in_place_updates: self.vbo_arena.in_place_mutations -
    prev_in_place,
    active_sparse_tiles: self.sparse_grid.active_tile_count,
    stroke_clusters_count: self.stroke_clusterer.clusters.length(),
    topology_vertices: self.topology.vertices.length(),
    topology_half_edges: self.topology.half_edges.length(),
  }
}
