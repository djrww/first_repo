///|
/// Blackbox Integration Tests for the Self-Developed OMT + GNN + SVM +
/// HPA *Closure + Kleisli + BBF + VSIDS + Conflict Graph + Hybrid-6 + QAP + CDCL(T) Solver,
/// the SMT-LIB 2 front-end and the LRA / LIA compliance examples.

///|
test "scenario_1_lazy_smt_lra_lia_euf_omt_end_to_end" {
  let res = @omt_cdcl_solver.run_lazy_smt_lra_lia_euf_omt_scenario()
  assert_eq(res.satisfiable, true)
  // Optimal assignment:
  // v1 = False (forced by EUF HPA *Closure conflict a==b & f(f(a))!=f(f(b)))
  // v2 = True (weight 2.0), v3 = False (weight 0), v4 = False (weight 0)
  // LIA integer tightening: x_0 = 2 (weight 2*2=4), x_1 = 3 (weight 3*3=9)
  // Total optimal objective = 2.0 + 4.0 + 9.0 = 15.0
  assert_eq(res.optimal_objective, 15.0)
  assert_eq(res.best_bool_model[1], @omt_cdcl_solver.False)
  assert_eq(res.best_bool_model[2], @omt_cdcl_solver.True)
  assert_eq(res.best_arith_model[0], 2.0)
  assert_eq(res.best_arith_model[1], 3.0)
  assert_eq(res.conservation_ideal_verified, true)
  assert_true(res.bbf_snapshots_taken >= 1)
  assert_true(res.surjective_axiom_certified_clauses >= 3)
}

///|
test "scenario_2_qap_incremental_discrete_pruning_and_hybrid6" {
  let res = @omt_cdcl_solver.run_qap_hybrid6_scenario()
  assert_eq(res.satisfiable, true)
  // Identity permutation (0->0, 1->1, 2->2):
  // Linear cost = C[0][0] + C[1][1] + C[2][2] = 1 + 2 + 3 = 6
  // Quadratic flow-distance cost =
  //   2*(F[0][1]*D[0][1] + F[0][2]*D[0][2] + F[1][2]*D[1][2])
  //   = 2*(2*1 + 1*4 + 3*2) = 2*(2 + 4 + 6) = 24
  // Total optimal QAP objective = 6 + 24 = 30.0
  assert_eq(res.optimal_objective, 30.0)
  assert_eq(res.conservation_ideal_verified, true)
  assert_true(res.surjective_axiom_certified_clauses >= 24)
}

///|
test "scenario_3_smtlib_lra_lia_compliance_examples" {
  let report = @omt_cdcl_solver.run_lra_lia_compliance_scenario()
  // Every example must parse, be solved to a definite verdict, and match its expectation.
  assert_true(report.contains("examples matched their expected verdict"))
  assert_true(!report.contains("MISMATCH"))
  assert_true(!report.contains("PARSE ERROR"))
}

///|
test "scenario_3b_smtlib_frontend_parses_scripts_and_skips_unknown_commands" {
  let text = "(set-logic QF_LIA)\n(declare-const x Int)\n(push 1)\n(assert (>= x 2))\n(check-sat)\n(exit)"
  let problem = @omt_cdcl_solver.parse_smtlib(text).unwrap()
  assert_eq(problem.logic, "QF_LIA")
  assert_eq(problem.num_arith_vars, 1)
  assert_eq(problem.num_bool_vars, 0)
  assert_eq(problem.assertions.length(), 1)
  // `push` is not modelled by this front-end and must be reported instead of ignored.
  assert_eq(problem.unsupported_commands.length(), 1)
  assert_eq(problem.unsupported_commands[0], "push")
  // A hard error (unknown symbol / unsupported sort) yields `None`, never a bogus problem.
  assert_true(@omt_cdcl_solver.parse_smtlib("(declare-const y Foo)").is_none())
  assert_true(@omt_cdcl_solver.parse_smtlib("(assert (>= z 1))").is_none())
}

///|
test "cdclt_solver_verdicts_and_conflict_graph_scenario" {
  let sat = @omt_cdcl_solver.solve_smtlib_text(
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (>= x 5))\n(assert (<= x 9))\n(check-sat)",
    200,
  ).unwrap()
  assert_eq(sat.satisfiable, true)
  assert_eq(sat.unknown, false)
  assert_eq(sat.arith_model[0], 5.0)

  let unsat = @omt_cdcl_solver.solve_smtlib_text(
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (* 2 x) 1))\n(check-sat)",
    200,
  ).unwrap()
  assert_eq(unsat.satisfiable, false)
  assert_eq(unsat.unknown, false)

  // The backtracking example exercises decisions, a learnt clause and the conflict path.
  let (report, svg) = @omt_cdcl_solver.run_conflict_graph_scenario()
  assert_true(report.contains("expected unsat"))
  assert_true(report.contains("graph verify"))
  assert_true(svg.contains("<svg"))
  assert_true(svg.contains("CDCL(T) implication graph"))
}

///|
test "scenario_4_lra_vs_lia_integrality_cut_separation" {
  let res = @omt_cdcl_solver.run_lra_vs_lia_integrality_cut_scenario()
  assert_eq(res.satisfiable, true)
  // v1 = False (refuted by LIA cut on 2.2 <= x_0 <= 2.8), v2 = True (weight 3), x_0 = 4 (weight 2*4=8) => 11.0
  assert_eq(res.optimal_objective, 11.0)
  assert_eq(res.best_bool_model[1], @omt_cdcl_solver.False)
  assert_eq(res.best_bool_model[2], @omt_cdcl_solver.True)
  assert_eq(res.best_arith_model[0], 4.0)
  assert_eq(res.conservation_ideal_verified, true)
}

///|
test "scenario_5_incremental_rendering_system_end_to_end" {
  let (f1, f2, topo_splits, sdf_samples) = @omt_cdcl_solver.run_incremental_rendering_system_scenario()
  // Frame 1: Full initial render of all 8 primitives (4 quads + 4 strokes grouped into 2 clusters)
  assert_eq(f1.frame_index, 1)
  assert_eq(f1.primitives_drawn, 8)
  assert_eq(f1.stroke_clusters_count, 2)
  assert_true(f1.pixels_shaded_in_frame > 1500)

  // Frame 2: Fine-grained reactive update of ONLY Primitive 0
  assert_eq(f2.frame_index, 2)
  assert_eq(f2.dirty_primitives_count, 1)
  assert_eq(f2.coalesced_dirty_rects_count, 1)
  assert_eq(f2.in_place_buffer_updates, 1)
  assert_true(f2.dirty_area_ratio < 0.10)
  assert_true(f2.primitives_locally_culled >= 5)
  assert_true(f2.pixels_shaded_in_frame < f1.pixels_shaded_in_frame / 2)

  // Planar topology auto-split crossing strokes & SDF atlas sampled
  assert_true(topo_splits >= 1)
  assert_true(sdf_samples > 100)
}
