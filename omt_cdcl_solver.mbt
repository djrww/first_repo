///|
/// High-Level Benchmark & Scenario Orchestrator for the Self-Developed
/// OMT + GNN + SVM + HPA *Closure + Kleisli + BBF + LRB + Hybrid-6 + QAP + CAC + CDCL(T) Solver.

///|
/// Scenario 1: Lazy SMT + LRA + LIA + EUF (HPA *Closure & Kleisli Unification) + OMT.
/// Solves a hybrid EUF + LIA/LRA + Boolean optimization problem:
/// - Boolean vars 1..4 with objective weights [0, 6.0, 2.0, 3.0, 8.0]
/// - Arithmetic integer vars x_0, x_1 in Z with objective 2*x_0 + 3*x_1
/// - Clauses:
///   (v1 v v2), (v2 v v3), (~v1 v ~v4)
/// - EUF terms: a, b, f(a), f(b), f(f(a)), f(f(b))
///   If v1 is True, asserts a == b AND f(f(a)) != f(f(b)) -> triggers HPA *Closure EUF conflict!
///   Hence CDCL(T) learns ~v1 via EUF congruence axiom, forcing v2 = True!
/// - LIA constraints guarded by v2:
///   x_0 >= 1.4 (tightened by LIA to x_0 >= 2)
///   x_1 >= 2.1 (tightened by LIA to x_1 >= 3)
///   x_0 + x_1 >= 5
pub fn run_lazy_smt_lra_lia_euf_omt_scenario() -> OmtSolveResult {
  let bool_weights : Array[Double] = [0.0, 6.0, 2.0, 3.0, 8.0]
  let arith_weights : Array[Double] = [2.0, 3.0]
  let is_int : Array[Bool] = [true, true]
  let solver = LazySmtOmtSolver::new(4, 2, is_int, bool_weights, arith_weights)

  // Intern EUF terms into HPA *Closure DAG
  let t_a = solver.hpa.intern_term(Var("a", 1))
  let t_b = solver.hpa.intern_term(Var("b", 2))
  let t_fa = solver.hpa.intern_term(App("f", [t_a]))
  let t_fb = solver.hpa.intern_term(App("f", [t_b]))
  let t_ffa = solver.hpa.intern_term(App("f", [t_fa]))
  let t_ffb = solver.hpa.intern_term(App("f", [t_fb]))

  // Link v1 and v2 in OMT-GNN EUF congruence graph
  solver.gnn.add_euf_congruence_edge(1, 2)
  solver.euf_var_pairs.push((1, 2))

  // When v1 is True: a == b (via Kleisli + HPA) AND f(f(a)) != f(f(b)) -> EUF *Closure conflict!
  solver.add_euf_constraint(mk_lit(1, true), t_a, t_b, true, true)
  solver.add_euf_constraint(mk_lit(1, true), t_ffa, t_ffb, false, false)

  // CNF clauses
  let _ = solver.add_clause(
    [mk_lit(1, true), mk_lit(2, true)],
    false,
    ProblemInput,
  )
  let _ = solver.add_clause(
    [mk_lit(2, true), mk_lit(3, true)],
    false,
    ProblemInput,
  )
  let _ = solver.add_clause(
    [mk_lit(1, false), mk_lit(4, false)],
    false,
    ProblemInput,
  )

  // LIA / LRA constraints guarded by v2 = True
  solver.lra_lia.set_var_domain(0, 0.0, 20.0)
  solver.lra_lia.set_var_domain(1, 0.0, 20.0)
  solver.lra_lia.add_constraint(
    mk_lit(2, true),
    { coeffs: [(0, 1.0)], constant: 0.0, },
    Ge,
    1.4, // LIA tightens x_0 >= ceil(1.4) = 2
    true,
  )
  solver.lra_lia.add_constraint(
    mk_lit(2, true),
    { coeffs: [(1, 1.0)], constant: 0.0, },
    Ge,
    2.1, // LIA tightens x_1 >= ceil(2.1) = 3
    true,
  )
  solver.lra_lia.add_constraint(
    mk_lit(2, true),
    { coeffs: [(0, 1.0), (1, 1.0)], constant: 0.0, },
    Ge,
    5.0,
    true,
  )

  // Register Dual-Layer CDN mappings
  solver.cdn.register_arith_mapping(2, true, 0, true, 2.0, 4.0)
  solver.cdn.register_arith_mapping(2, true, 1, true, 3.0, 9.0)
  solver.cdn.register_euf_mapping(1, true, t_a, t_b)

  solver.solve_omt(100)
}

///|
/// Scenario 2: QAP Incremental Discrete Pruning + Dual-Layer CDN + Cooperative LRB Hybrid-6.
/// Solves a 3x3 Facility-Location Quadratic Assignment Problem (9 Boolean vars x_{i,k}):
///   Facility 0..2 assigned to Location 0..2.
///   Linear + Quadratic Flow-Distance objective minimized via QAP Incremental Discrete Pruner
///   and Cooperative LRB Hybrid-6 Dynamic Lower Bound.
pub fn run_qap_lrb_hybrid6_scenario() -> OmtSolveResult {
  let n = 3
  let num_vars = n * n // vars 1..9
  let bool_weights = Array::make(num_vars + 1, 0.0)
  let solver = LazySmtOmtSolver::new(num_vars, 0, [], bool_weights, [])

  let flow : Array[Array[Double]] = [
    [0.0, 2.0, 1.0],
    [2.0, 0.0, 3.0],
    [1.0, 3.0, 0.0],
  ]
  let dist : Array[Array[Double]] = [
    [0.0, 1.0, 4.0],
    [1.0, 0.0, 2.0],
    [4.0, 2.0, 0.0],
  ]
  let linear_cost : Array[Array[Double]] = [
    [1.0, 5.0, 8.0],
    [6.0, 2.0, 7.0],
    [9.0, 6.0, 3.0],
  ]
  let qap = QapIncrementalPruner::new(n, 1, flow, dist, linear_cost)
  solver.attach_qap_pruner(qap)

  solver.solve_omt(200)
}

///|
/// Scenario 3: Ring-Lifted Cylindrical Algebraic Covering (CAC) Ideal Reduction &
/// Homomorphic Conservation Ideal + Surjective Axiom Invariant Verification.
pub fn run_cac_ideal_and_conservation_scenario() -> (Double, Bool, Bool, Int) {
  // 1. Construct polynomial ring Q[x_0, x_1]
  // Ideal generators: g_1 = x_0^2 - x_1 - 1, g_2 = x_1 - 3
  // Under I = <g_1, g_2>, x_0^2 reduces to 4!
  // Let f = x_0^2 + 2*x_1 + 5. Modulo <g_1, g_2>, f reduces to 4 + 6 + 5 = 15.
  let g1 : MultivariatePoly = {
    num_vars: 2,
    terms: [
      { coeff: 1.0, exponents: [2, 0], },
      { coeff: -1.0, exponents: [0, 1], },
      { coeff: -1.0, exponents: [0, 0], },
    ],
  }
  let g2 : MultivariatePoly = {
    num_vars: 2,
    terms: [
      { coeff: 1.0, exponents: [0, 1], },
      { coeff: -3.0, exponents: [0, 0], },
    ],
  }
  let f : MultivariatePoly = {
    num_vars: 2,
    terms: [
      { coeff: 1.0, exponents: [2, 0], },
      { coeff: 2.0, exponents: [0, 1], },
      { coeff: 5.0, exponents: [0, 0], },
    ],
  }
  let reduced = reduce_poly_modulo_ideal(f, [g1, g2])
  let reduced_const = reduced.eval([0.0, 0.0])

  // 2. Verify Ring-Lifted CAC conflict extraction when reduced polynomial violates constraint
  let cac = CylindricalAlgebraicCovering::new(2)
  cac.add_ideal_generator(g1)
  cac.add_ideal_generator(g2)
  // Require f(x_0, x_1) <= 10.0 guarded by literal +1 (impossible since f == 15 mod I!)
  cac.add_constraint(f, Le, 10.0, 1)
  let cac_conflict = cac.check_cylindrical_covering(
    [0.0, 0.0],
    [-5.0, -5.0],
    [5.0, 5.0],
    0,
  )
  let cac_detected_infeasible = match cac_conflict {
    Some(c) => c.lits.length() == 1 && c.lits[0] == -1
    None => false
  }

  // 3. Verify Homomorphic Conservation Ideal on resolution (x_1 v x_2) and (~x_1 v x_3) => (x_2 v x_3)
  let ideal = HomomorphicConservationIdeal::new(3)
  let c1 = Clause::new(0, [1, 2], false, 2, ProblemInput)
  let c2 = Clause::new(1, [-1, 3], false, 2, ProblemInput)
  let cres = Clause::new(2, [2, 3], true, 2, UipResolution(2, 1))
  let resolution_conserved = ideal.verify_resolution_conservation(c1, c2, cres)

  (
    reduced_const,
    cac_detected_infeasible,
    resolution_conserved,
    cac.ideal_reductions_count,
  )
}

///|
/// Scenario 4: LRA-Feasible vs. LIA-Infeasible Integrality Cut Separation +
/// Superposed Exhaustive Upper-Bound Axiom Projection.
/// - Boolean var 1 selects branch A: x_0 >= 2.2 AND x_0 <= 2.8
///   (LRA-feasible at x_0 = 2.5, but LIA-infeasible over Z since ceil(2.2)=3 > floor(2.8)=2!)
/// - Boolean var 2 selects branch B: x_0 >= 4.0 AND x_0 <= 6.0 (LIA-feasible at x_0 = 4)
/// - Clause: (v1 v v2)
/// - Objective: minimize 1*v1 + 3*v2 + 2*x_0
///   Even though v1 has lower Boolean cost (1 < 3), LIA Integrality Cut refutes v1=True
///   and forces v2=True, x_0=4, yielding optimal objective = 3 + 2*4 = 11.0!
pub fn run_lra_vs_lia_integrality_cut_scenario() -> OmtSolveResult {
  let bool_weights : Array[Double] = [0.0, 1.0, 3.0]
  let arith_weights : Array[Double] = [2.0]
  let solver = LazySmtOmtSolver::new(2, 1, [true], bool_weights, arith_weights)
  let _ = solver.add_clause(
    [mk_lit(1, true), mk_lit(2, true)],
    false,
    ProblemInput,
  )
  solver.lra_lia.set_var_domain(0, 0.0, 10.0)
  // Branch A (v1 = True): 2.2 <= x_0 <= 2.8 (no integer solution!)
  solver.lra_lia.add_constraint(
    mk_lit(1, true),
    { coeffs: [(0, 1.0)], constant: 0.0, },
    Ge,
    2.2,
    true,
  )
  solver.lra_lia.add_constraint(
    mk_lit(1, true),
    { coeffs: [(0, 1.0)], constant: 0.0, },
    Le,
    2.8,
    true,
  )
  // Branch B (v2 = True): 4.0 <= x_0 <= 6.0 (integer optimal x_0 = 4)
  solver.lra_lia.add_constraint(
    mk_lit(2, true),
    { coeffs: [(0, 1.0)], constant: 0.0, },
    Ge,
    4.0,
    true,
  )
  solver.lra_lia.add_constraint(
    mk_lit(2, true),
    { coeffs: [(0, 1.0)], constant: 0.0, },
    Le,
    6.0,
    true,
  )
  solver.solve_omt(100)
}

///|
/// Scenario 5: End-to-End Vector & Incremental Raster Rendering System Benchmark.
/// Exercises:
/// - Vector Incremental Topology (DCEL faces + planar intersecting segment auto-splitting)
/// - Fine-Grained Reactivity (Signal -> Computed -> Primitive invalidation)
/// - R-Tree Spatial Index (Guttman quadratic split + local range culling)
/// - Sparse Spatial Grid (Morton Z-order tile hashing)
/// - Stroke Clustering (RDP polyline simplification + spatial-directional clustering)
/// - Dirty Rectangle Detection & Coalescing
/// - Zero-Copy VBO/IBO Arena & In-Place Sub-Buffer Mutation
/// - SDF Texture Atlas (Bilinear sampling + smoothstep contour shader)
/// - 4x RGSS Anti-Aliased Full & Local Scissor Rasterization
/// Returns `(frame1_metrics, frame2_incremental_metrics, topo_splits, sdf_samples)`.
pub fn run_incremental_rendering_system_scenario() -> (
  FrameRenderMetrics,
  FrameRenderMetrics,
  Int,
  Int,
) {
  let engine = IncrementalRenderEngine::new(128, 128, 16.0)

  // 1. Add 4 Vector Quads across different regions of the 128x128 canvas
  // Quad 0: Top-left SDF anti-aliased badge
  let _ = engine.add_vector_quad(
    8.0,
    8.0,
    28.0,
    28.0,
    ColorRgba::new(0.20, 0.75, 0.95, 1.0),
    SdfContourShader(
      ColorRgba::new(0.15, 0.65, 0.95, 1.0),
      ColorRgba::new(0.95, 0.98, 1.0, 1.0),
      0.04,
      0.06,
    ),
  )
  // Quad 1: Top-right Linear Gradient panel
  let _ = engine.add_vector_quad(
    84.0,
    10.0,
    118.0,
    36.0,
    ColorRgba::new(1.0, 1.0, 1.0, 1.0),
    LinearGradientShader(
      { x: 84.0, y: 10.0, },
      { x: 118.0, y: 36.0, },
      ColorRgba::new(0.95, 0.35, 0.25, 0.95),
      ColorRgba::new(0.98, 0.75, 0.20, 0.95),
    ),
  )
  // Quad 2: Bottom-left Procedural Checkerboard panel
  let _ = engine.add_vector_quad(
    10.0,
    84.0,
    42.0,
    116.0,
    ColorRgba::new(1.0, 1.0, 1.0, 1.0),
    ProceduralCheckerShader(
      ColorRgba::new(0.25, 0.85, 0.55, 0.90),
      ColorRgba::new(0.10, 0.35, 0.25, 0.90),
      4.0,
    ),
  )
  // Quad 3: Center Flat Color widget
  let _ = engine.add_vector_quad(
    48.0,
    48.0,
    68.0,
    68.0,
    ColorRgba::new(0.85, 0.30, 0.90, 0.90),
    FlatColorShader(ColorRgba::new(0.85, 0.30, 0.90, 0.90)),
  )

  // 2. Add 4 Freehand Vector Strokes (2 crossing strokes in Cluster 0, 2 nearby strokes in Cluster 1)
  // Crossing strokes in [12..32, 12..32] also trigger incremental planar intersection splitting!
  let stroke_a : Array[StrokePoint] = [
    { pos: { x: 12.0, y: 12.0, }, pressure: 0.8, timestamp: 0.0, },
    { pos: { x: 20.0, y: 20.1, }, pressure: 0.9, timestamp: 1.0, },
    { pos: { x: 32.0, y: 32.0, }, pressure: 0.8, timestamp: 2.0, },
  ]
  let stroke_b : Array[StrokePoint] = [
    { pos: { x: 12.0, y: 32.0, }, pressure: 0.7, timestamp: 3.0, },
    { pos: { x: 32.0, y: 12.0, }, pressure: 0.9, timestamp: 4.0, },
  ]
  let _ = engine.add_clustered_vector_stroke(
    stroke_a,
    2.5,
    ColorRgba::new(1.0, 0.90, 0.30, 0.95),
  )
  let _ = engine.add_clustered_vector_stroke(
    stroke_b,
    2.5,
    ColorRgba::new(1.0, 0.60, 0.20, 0.95),
  )

  // Second stroke cluster in bottom-right [88..116, 90..98]
  let stroke_c : Array[StrokePoint] = [
    { pos: { x: 88.0, y: 90.0, }, pressure: 0.8, timestamp: 5.0, },
    { pos: { x: 102.0, y: 90.2, }, pressure: 0.8, timestamp: 6.0, },
    { pos: { x: 116.0, y: 90.0, }, pressure: 0.8, timestamp: 7.0, },
  ]
  let stroke_d : Array[StrokePoint] = [
    { pos: { x: 88.0, y: 98.0, }, pressure: 0.8, timestamp: 8.0, },
    { pos: { x: 116.0, y: 98.0, }, pressure: 0.8, timestamp: 9.0, },
  ]
  let _ = engine.add_clustered_vector_stroke(
    stroke_c,
    2.5,
    ColorRgba::new(0.40, 0.95, 0.80, 0.95),
  )
  let _ = engine.add_clustered_vector_stroke(
    stroke_d,
    2.5,
    ColorRgba::new(0.30, 0.80, 0.95, 0.95),
  )

  // 3. Frame 1: Initial Scene Render
  let frame1 = engine.render_incremental_frame()

  // 4. Frame 2: Fine-Grained Reactive Update on ONLY Primitive 0 (Top-left SDF badge moves by +4, +3)
  engine.set_primitive_translation_reactive(0, 4.0, 3.0)
  let frame2 = engine.render_incremental_frame()

  (
    frame1,
    frame2,
    engine.topology.incremental_splits,
    engine.sdf_atlas.bilinear_samples_count,
  )
}
