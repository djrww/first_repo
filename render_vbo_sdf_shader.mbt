///|
/// Flat Vertex Buffer Arena (連續平面頂點緩衝區 VBO/IBO),
/// Signed Distance Field Texture Atlas (SDF紋理), and
/// Programmable Vertex & Fragment Shader Pipeline (著色器).

///|
/// Normalized RGBA Color in [0.0, 1.0].
pub(all) struct ColorRgba {
  r : Double
  g : Double
  b : Double
  a : Double
} derive(Eq, Debug)

///|
pub extend ColorRgba with Eq::{equal, not_equal}

///|
///|
#deprecated("Use `Debug::to_repr` instead", skip_current_package=true)
#doc(hidden)
pub extend ColorRgba with @debug.Debug::{to_repr}

///|
/// Construct a normalized RGBA color.
pub fn ColorRgba::new(
  r : Double,
  g : Double,
  b : Double,
  a : Double,
) -> ColorRgba {
  {
    r: r.clamp(min=0.0, max=1.0),
    g: g.clamp(min=0.0, max=1.0),
    b: b.clamp(min=0.0, max=1.0),
    a: a.clamp(min=0.0, max=1.0),
  }
}

///|
/// Linearly interpolate between two RGBA colors `c0` and `c1` by `t in [0, 1]`.
pub fn ColorRgba::lerp(c0 : ColorRgba, c1 : ColorRgba, t : Double) -> ColorRgba {
  let ct = t.clamp(min=0.0, max=1.0)
  {
    r: c0.r + (c1.r - c0.r) * ct,
    g: c0.g + (c1.g - c0.g) * ct,
    b: c0.b + (c1.b - c0.b) * ct,
    a: c0.a + (c1.a - c0.a) * ct,
  }
}

///|
/// Porter-Duff SRC_OVER alpha blending of `src` over `dst`.
pub fn blend_src_over(src : ColorRgba, dst : ColorRgba) -> ColorRgba {
  let inv_sa = 1.0 - src.a
  let out_a = src.a + dst.a * inv_sa
  if out_a < tol_eps {
    return { r: 0.0, g: 0.0, b: 0.0, a: 0.0, }
  }
  {
    r: (src.r * src.a + dst.r * dst.a * inv_sa) / out_a,
    g: (src.g * src.a + dst.g * dst.a * inv_sa) / out_a,
    b: (src.b * src.a + dst.b * dst.a * inv_sa) / out_a,
    a: out_a,
  }
}

///|
/// Interleaved GPU Vertex attribute layout (stride = 8 Doubles in VBO):
/// (x, y) position, (u, v) texture/SDF coordinates, (r, g, b, a) vertex color.
pub(all) struct GpuVertex {
  x : Double
  y : Double
  u : Double
  v : Double
  color : ColorRgba
}

///|
/// Arena Buffer Slice Descriptor (緩衝區視圖):
/// A view into a contiguous sub-range of the shared VBO/IBO arena, addressed by offset and
/// length. Vertices are converted into the arena's flat float buffer once at upload time;
/// afterwards the slice is read in place and never re-copied per frame.
pub(all) struct ArenaBufferSlice {
  vbo_float_offset : Int // start index in raw_vbo_floats (stride = 8)
  vertex_count : Int
  ibo_index_offset : Int // start index in raw_ibo_indices
  index_count : Int // number of triangle indices (multiple of 3)
  stride : Int
  mut generation : Int
}

///|
/// Contiguous Vertex & Index Buffer Arena (頂點緩衝區 VBO + IBO).
/// Owns one flat interleaved float array plus one flat index array; slices are views into
/// them, and in-place updates rewrite the floats belonging to a slice.
pub(all) struct FlatVertexArena {
  raw_vbo_floats : Array[Double] // flat interleaved [x, y, u, v, r, g, b, a, ...]
  raw_ibo_indices : Array[Int] // flat triangle indices [i0, i1, i2, ...]
  mut arena_views_issued : Int
  mut in_place_mutations : Int
}

///|
/// Create a new Vertex & Index Buffer Arena.
pub fn FlatVertexArena::new() -> FlatVertexArena {
  {
    raw_vbo_floats: [],
    raw_ibo_indices: [],
    arena_views_issued: 0,
    in_place_mutations: 0,
  }
}

///|
/// Append a mesh into the contiguous VBO/IBO arena and return an `ArenaBufferSlice` view
/// into the arena memory. The vertices are unpacked into the flat buffer here (one
/// conversion at upload); the returned slice itself is a plain offset/length view.
pub fn FlatVertexArena::allocate_mesh(
  self : FlatVertexArena,
  vertices : Array[GpuVertex],
  local_indices : Array[Int],
) -> ArenaBufferSlice {
  let stride = 8
  let vbo_offset = self.raw_vbo_floats.length()
  let base_vertex_idx = vbo_offset / stride
  for vert in vertices {
    self.raw_vbo_floats.push(vert.x)
    self.raw_vbo_floats.push(vert.y)
    self.raw_vbo_floats.push(vert.u)
    self.raw_vbo_floats.push(vert.v)
    self.raw_vbo_floats.push(vert.color.r)
    self.raw_vbo_floats.push(vert.color.g)
    self.raw_vbo_floats.push(vert.color.b)
    self.raw_vbo_floats.push(vert.color.a)
  }
  let ibo_offset = self.raw_ibo_indices.length()
  for idx in local_indices {
    self.raw_ibo_indices.push(base_vertex_idx + idx)
  }
  self.arena_views_issued = self.arena_views_issued + 1
  {
    vbo_float_offset: vbo_offset,
    vertex_count: vertices.length(),
    ibo_index_offset: ibo_offset,
    index_count: local_indices.length(),
    stride,
    generation: 1,
  }
}

///|
/// Zero-copy in-place translation of all vertices inside `slice` directly inside
/// `raw_vbo_floats` without allocating or copying any vertex array.
pub fn FlatVertexArena::translate_slice_in_place(
  self : FlatVertexArena,
  slice : ArenaBufferSlice,
  dx : Double,
  dy : Double,
) -> ArenaBufferSlice {
  let mut offset = slice.vbo_float_offset
  for _i = 0; _i < slice.vertex_count; _i = _i + 1 {
    if offset + 1 < self.raw_vbo_floats.length() {
      self.raw_vbo_floats[offset] = self.raw_vbo_floats[offset] + dx
      self.raw_vbo_floats[offset + 1] = self.raw_vbo_floats[offset + 1] + dy
    }
    offset = offset + slice.stride
  }
  self.in_place_mutations = self.in_place_mutations + 1
  { ..slice, generation: slice.generation + 1, }
}

///|
/// Read a vertex by global index directly from the flat float buffer (O(1), no allocation).
pub fn FlatVertexArena::read_global_vertex(
  self : FlatVertexArena,
  global_vertex_idx : Int,
) -> GpuVertex {
  let base = global_vertex_idx * 8
  {
    x: self.raw_vbo_floats[base],
    y: self.raw_vbo_floats[base + 1],
    u: self.raw_vbo_floats[base + 2],
    v: self.raw_vbo_floats[base + 3],
    color: {
      r: self.raw_vbo_floats[base + 4],
      g: self.raw_vbo_floats[base + 5],
      b: self.raw_vbo_floats[base + 6],
      a: self.raw_vbo_floats[base + 7],
    },
  }
}

///|
/// Compute the tight AABB of a `ArenaBufferSlice` directly from the VBO arena without copying.
pub fn FlatVertexArena::compute_slice_aabb(
  self : FlatVertexArena,
  slice : ArenaBufferSlice,
) -> Aabb {
  if slice.vertex_count == 0 {
    return Aabb::new(0.0, 0.0, 0.0, 0.0)
  }
  let mut min_x = scan_infinity
  let mut min_y = scan_infinity
  let mut max_x = -scan_infinity
  let mut max_y = -scan_infinity
  let mut offset = slice.vbo_float_offset
  for _i = 0; _i < slice.vertex_count; _i = _i + 1 {
    let vx = self.raw_vbo_floats[offset]
    let vy = self.raw_vbo_floats[offset + 1]
    min_x = min_x.min(vx)
    min_y = min_y.min(vy)
    max_x = max_x.max(vx)
    max_y = max_y.max(vy)
    offset = offset + slice.stride
  }
  Aabb::new(min_x, min_y, max_x, max_y)
}

///|
/// Analytical SDF Primitive Shapes used to bake or evaluate Signed Distance Fields (SDF紋理).
pub(all) enum SdfShapeKind {
  SdfCircle(Vec2, Double) // (center, radius)
  SdfCapsule(Vec2, Vec2, Double) // (a, b, radius)
  SdfRoundedBox(Vec2, Vec2, Double) // (center, half_extents, corner_radius)
}

///|
/// Evaluate the exact Euclidean Signed Distance d(p) for an `SdfShapeKind`.
/// Negative inside the shape, zero on the boundary, positive outside.
pub fn eval_analytical_sdf(shape : SdfShapeKind, p : Vec2) -> Double {
  match shape {
    SdfCircle(c, r) => p.dist(c) - r
    SdfCapsule(a, b, r) => {
      let pa_x = p.x - a.x
      let pa_y = p.y - a.y
      let ba_x = b.x - a.x
      let ba_y = b.y - a.y
      let ba_dot = ba_x * ba_x + ba_y * ba_y
      let h = if ba_dot > tol_eps_tight {
        ((pa_x * ba_x + pa_y * ba_y) / ba_dot).clamp(min=0.0, max=1.0)
      } else {
        0.0
      }
      let dx = pa_x - ba_x * h
      let dy = pa_y - ba_y * h
      (dx * dx + dy * dy).sqrt() - r
    }
    SdfRoundedBox(c, half_ext, r) => {
      let qx = (p.x - c.x).abs() - (half_ext.x - r)
      let qy = (p.y - c.y).abs() - (half_ext.y - r)
      let out_x = qx.max(0.0)
      let out_y = qy.max(0.0)
      let outside_dist = (out_x * out_x + out_y * out_y).sqrt()
      let inside_dist = qx.max(qy).min(0.0)
      outside_dist + inside_dist - r
    }
  }
}

///|
/// Hermite smoothstep interpolation in [0.0, 1.0] for SDF anti-aliasing.
pub fn sdf_smoothstep(edge0 : Double, edge1 : Double, x : Double) -> Double {
  let denom = edge1 - edge0
  if denom.abs() < tol_eps_tight {
    return if x < edge0 { 0.0 } else { 1.0 }
  }
  let t = ((x - edge0) / denom).clamp(min=0.0, max=1.0)
  t * t * (3.0 - 2.0 * t)
}

///|
/// Signed Distance Field (SDF) Texture Atlas (SDF紋理圖集):
/// Stores precomputed distance field texels in UV space [0, 1]^2 and supports
/// sub-pixel bilinear interpolation for resolution-independent anti-aliased rendering.
pub(all) struct SdfTextureAtlas {
  width : Int
  height : Int
  texels : Array[Double] // width * height signed distances in normalized UV space
  mut bilinear_samples_count : Int
}

///|
/// Bake an SDF Texture Atlas of resolution `width x height` from a CSG union of analytical SDF shapes
/// defined in UV domain `[0.0, 1.0] x [0.0, 1.0]`.
pub fn SdfTextureAtlas::bake_from_shapes(
  width : Int,
  height : Int,
  shapes : Array[SdfShapeKind],
) -> SdfTextureAtlas {
  let w = width.max(4)
  let h = height.max(4)
  let texels = Array::make(w * h, 1.0)
  for y = 0; y < h; y = y + 1 {
    let v = (y.to_double() + 0.5) / h.to_double()
    for x = 0; x < w; x = x + 1 {
      let u = (x.to_double() + 0.5) / w.to_double()
      let pt : Vec2 = { x: u, y: v, }
      let mut min_d = ray_max_distance
      for s in shapes {
        let d = eval_analytical_sdf(s, pt)
        if d < min_d {
          min_d = d
        }
      }
      texels[y * w + x] = min_d
    }
  }
  { width: w, height: h, texels, bilinear_samples_count: 0, }
}

///|
/// Sample the SDF Texture Atlas at normalized coordinates `(u, v)` using sub-pixel
/// bilinear filtering.
pub fn SdfTextureAtlas::sample_bilinear(
  self : SdfTextureAtlas,
  u : Double,
  v : Double,
) -> Double {
  self.bilinear_samples_count = self.bilinear_samples_count + 1
  let cu = u.clamp(min=0.0, max=1.0)
  let cv = v.clamp(min=0.0, max=1.0)
  let fx = cu * (self.width - 1).to_double()
  let fy = cv * (self.height - 1).to_double()
  let x0 = fx.floor().to_int().clamp(min=0, max=self.width - 1)
  let y0 = fy.floor().to_int().clamp(min=0, max=self.height - 1)
  let x1 = (x0 + 1).min(self.width - 1)
  let y1 = (y0 + 1).min(self.height - 1)
  let tx = fx - x0.to_double()
  let ty = fy - y0.to_double()

  let d00 = self.texels[y0 * self.width + x0]
  let d10 = self.texels[y0 * self.width + x1]
  let d01 = self.texels[y1 * self.width + x0]
  let d11 = self.texels[y1 * self.width + x1]

  let top = d00 + (d10 - d00) * tx
  let bot = d01 + (d11 - d01) * tx
  top + (bot - top) * ty
}

///|
/// 2D Affine Transform Uniforms for the Programmable Vertex Shader.
pub(all) struct Affine2D {
  m00 : Double
  m01 : Double
  m10 : Double
  m11 : Double
  tx : Double
  ty : Double
}

///|
/// Identity 2D Affine Transform.
pub fn Affine2D::identity() -> Affine2D {
  { m00: 1.0, m01: 0.0, m10: 0.0, m11: 1.0, tx: 0.0, ty: 0.0, }
}

///|
/// Programmable Fragment Shader Programs (可編程像素/片段著色器).
pub(all) enum FragmentShaderProgram {
  FlatColorShader(ColorRgba)
  LinearGradientShader(Vec2, Vec2, ColorRgba, ColorRgba)
  SdfContourShader(ColorRgba, ColorRgba, Double, Double) // (fill, outline, feather, outline_width)
  ProceduralCheckerShader(ColorRgba, ColorRgba, Double)
}

///|
/// Execute Programmable Vertex Shader on `v` with `transform`.
pub fn execute_vertex_shader(v : GpuVertex, transform : Affine2D) -> GpuVertex {
  let sx = transform.m00 * v.x + transform.m01 * v.y + transform.tx
  let sy = transform.m10 * v.x + transform.m11 * v.y + transform.ty
  { ..v, x: sx, y: sy, }
}

///|
/// Execute Programmable Fragment Shader at screen position `frag_pos`, interpolated `uv`
/// and `vert_color`, optionally sampling the `sdf_atlas`.
pub fn execute_fragment_shader(
  program : FragmentShaderProgram,
  frag_pos : Vec2,
  uv : Vec2,
  vert_color : ColorRgba,
  sdf_atlas : SdfTextureAtlas,
) -> ColorRgba {
  match program {
    FlatColorShader(c) =>
      {
        r: c.r * vert_color.r,
        g: c.g * vert_color.g,
        b: c.b * vert_color.b,
        a: c.a * vert_color.a,
      }
    LinearGradientShader(p0, p1, c0, c1) => {
      let dx = p1.x - p0.x
      let dy = p1.y - p0.y
      let len_sq = dx * dx + dy * dy
      let t = if len_sq > tol_eps {
        ((frag_pos.x - p0.x) * dx + (frag_pos.y - p0.y) * dy) / len_sq
      } else {
        0.0
      }
      ColorRgba::lerp(c0, c1, t)
    }
    SdfContourShader(fill_col, outline_col, feather, outline_w) => {
      let dist = sdf_atlas.sample_bilinear(uv.x, uv.y)
      // Fill alpha: 1 inside (dist < 0), smooth transition across [-feather, +feather]
      let fill_alpha = 1.0 - sdf_smoothstep(-feather, feather, dist)
      // Outer boundary including outline_w
      let outer_alpha = 1.0 -
        sdf_smoothstep(outline_w - feather, outline_w + feather, dist)
      let base_rgb = ColorRgba::lerp(outline_col, fill_col, fill_alpha)
      {
        r: base_rgb.r,
        g: base_rgb.g,
        b: base_rgb.b,
        a: outer_alpha * fill_col.a,
      }
    }
    ProceduralCheckerShader(c_even, c_odd, cell_size) => {
      let s = cell_size.max(1.0)
      let cx = (frag_pos.x / s).floor().to_int()
      let cy = (frag_pos.y / s).floor().to_int()
      if ((cx + cy) & 1) == 0 {
        c_even
      } else {
        c_odd
      }
    }
  }
}
