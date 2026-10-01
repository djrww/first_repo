///|
/// Blackbox Integration Tests for the Self-Developed OMT + GNN + SVM +
/// HPA *Closure + Kleisli + BBF + LRB + Hybrid-6 + QAP + CAC + CDCL(T) Lazy SMT Solver.

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
test "scenario_2_qap_incremental_discrete_pruning_and_lrb_hybrid6" {
  let res = @omt_cdcl_solver.run_qap_lrb_hybrid6_scenario()
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
test "scenario_3_cac_ring_ideal_reduction_and_conservation_invariant" {
  let (reduced_val, cac_infeasible, conserved, reductions) = @omt_cdcl_solver.run_cac_ideal_and_conservation_scenario()
  assert_eq(reduced_val, 15.0)
  assert_eq(cac_infeasible, true)
  assert_eq(conserved, true)
  assert_true(reductions >= 1)
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
