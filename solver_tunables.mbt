///|
/// Central tunables for the solver and the rendering backend.
///
/// Every value below used to be an inline literal repeated across files (`1.0e18`,
/// `1.0e12`, `1.0e-9`, `+ 16.0`, `d = 6`, …). They are collected here so that the
/// numerical behaviour of the whole package can be inspected, justified and adjusted in
/// one place instead of being discovered by grepping for magic numbers.
///
/// Categories:
///   - sentinels: values standing in for "unbounded" / "never beaten yet",
///   - tolerances: comparison epsilons (each one documents *why* that magnitude),
///   - budgets: iteration limits that guarantee termination,
///   - layout constants: spatial indexing and embedding dimensions.

// ---------------------------------------------------------------------------
// Sentinels
// ---------------------------------------------------------------------------

///|
/// "No finite bound" in the arithmetic theory solver. Chosen so that a variable bound
/// never overflows when multiplied by a coefficient of the order of 1e3, while staying
/// far below the point where `x + 1.0 == x` rounding makes bound propagation useless.
let arith_infinity : Double = 1.0e15

///|
/// Half-width of the "effectively unbounded" interval used by the interval-evaluation and
/// CDN helpers when no finite box is available (`InnerSemigroupElem::neutral`,
/// `interval_eval_poly`). It is *not* the default variable domain — that role belongs to
/// `arith_default_lower_bound` / `arith_default_upper_bound`.
let arith_initial_bound : Double = 1.0e12

///|
/// Initial accumulator for "smallest / largest value seen so far" scans over geometry
/// (AABB extents, ray parameters, triangle optima). Large enough that any real geometry
/// value beats it, and finite so that a scan over an empty set stays a valid number.
let scan_infinity : Double = 1.0e18

///|
/// "No shape is closer than this" sentinel used when baking the SDF texture atlas from a
/// CSG union of shapes. It is deliberately finite so the bake stays representable; any real
/// signed distance is smaller. (This package contains no ray marcher, so this value is not a
/// ray-marching limit.)
let sdf_bake_distance_sentinel : Double = 1.0e9

///|
/// Lower end of the default interval assigned to an arithmetic variable that never receives
/// an explicit `set_var_domain` call. Problems whose variables live outside this interval
/// must declare their own domains; the default is deliberately finite and tight so that a
/// missing declaration cannot silently create an unbounded objective.
let arith_default_lower_bound : Double = 0.0

///|
/// Upper end of the default arithmetic variable interval (see `arith_default_lower_bound`).
let arith_default_upper_bound : Double = 100.0

// ---------------------------------------------------------------------------
// Tolerances
// ---------------------------------------------------------------------------

///|
/// General comparison tolerance for floating-point equality / satisfaction checks on
/// values that have passed through a handful of arithmetic operations.
let tol_eps : Double = 1.0e-9

///|
/// Tight tolerance for geometric degeneracy tests (parallel denominators, zero-length
/// normals). Below this, the quantity is treated as exactly zero.
let tol_eps_tight : Double = 1.0e-12

///|
/// Flattening / normalisation tolerance for curves and meshes, where the acceptable
/// error is a fraction of a pixel rather than of a bound.
let tol_eps_mesh : Double = 1.0e-6

///|
/// A reduced polynomial whose constant term is larger than this is treated as a
/// non-zero constant (so it decides a relation on its whole variety) rather than as
/// numerically vanishing. Larger than `tol_eps` because coefficients come from
/// ring-lifted reductions that accumulate rounding.
let poly_nonzero_tol : Double = 1.0e-6

// ---------------------------------------------------------------------------
// Budgets (termination guarantees)
// ---------------------------------------------------------------------------

///|
/// Per-conflict share of the arithmetic propagation step budget.
let arith_step_budget_per_conflict : Int = 10

///|
/// Constant part of the arithmetic propagation step budget.
let arith_step_budget_base : Int = 500

///|
/// Maximum number of fixpoint rounds of the interval bound-propagation pass.
let arith_propagation_round_limit : Int = 512

///|
/// Maximum number of projection-repair / improvement rounds used to repair a candidate
/// witness into a certified one.
let arith_witness_round_limit : Int = 64

///|
/// Maximum number of polynomial reduction steps performed by the cylindrical algebraic
/// covering before it gives up on a generator.
let poly_reduction_step_limit : Int = 1000000

///|
/// Capacity of the SVM support-vector ring buffer.
let default_support_vector_capacity : Int = 32

// ---------------------------------------------------------------------------
// Spatial indexing / rendering layout
// ---------------------------------------------------------------------------

///|
/// Default fan-out of the dynamic R-tree (entries per node).
let rtree_default_fanout : Int = 4

///|
/// Default tile size of the sparse spatial hash grid, in pixels.
let spatial_default_tile_size : Double = 32.0

///|
/// Extra area, in square pixels, allowed when merging two dirty rectangles. Prevents a
/// few stray thin rectangles from being merged into one huge repaint.
let dirty_coalesce_area_slack : Double = 16.0

///|
/// Number of buckets in the sparse spatial hash grid (hash-table size, not a capacity).
let spatial_grid_bucket_count : Int = 64

///|
/// Distance, in pixels, under which stroke endpoints are considered one cluster joint.
let stroke_cluster_radius : Double = 24.0

///|
/// Default resolution of the SDF texture atlas baked at engine start-up.
let sdf_atlas_default_width : Int = 32
let sdf_atlas_default_height : Int = 32

// ---------------------------------------------------------------------------
// GNN / SVM search heuristics
// ---------------------------------------------------------------------------

///|
/// Embedding dimension per variable and per clause in the OMT graph neural network.
let gnn_embed_dim : Int = 6

///|
/// Mixing weight of the SVM margin inside the neural branching utility score.
let gnn_svm_mix : Double = 0.25

// ---------------------------------------------------------------------------
// LRB branching heuristic
// ---------------------------------------------------------------------------

///|
/// Initial EMA learning rate of a fresh LRB variable.
let lrb_ema_initial : Double = 0.15

///|
/// Weight of the LRB score in the fused variable-selection score
/// (`0.70 * LRB + 0.30 * GNN/SVM`).
let lrb_fuse_lrb_weight : Double = 0.70

///|
/// Weight of the GNN/SVM score in the fused variable-selection score.
let lrb_fuse_gnn_weight : Double = 0.30

///|
/// Locality decay applied to the learning rate of not-yet-assigned variables on conflict.
let lrb_locality_decay : Double = 0.95

// ---------------------------------------------------------------------------
// Vertex buffer layout
// ---------------------------------------------------------------------------

///|
/// Number of interleaved `Double` slots per vertex in the flat VBO
/// (x, y, u, v, r, g, b, a).
let gpu_vertex_stride : Int = 8
