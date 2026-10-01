///|
/// Whitebox Unit Tests for Internal Invariants, Semigroup/Monoid Laws,
/// HPA *Closure, Kleisli Unification, OMT-GNN, SVM Kernels, VSIDS, QAP, the implication
/// graph and the polynomial / ideal-reduction algebra.

///|
test "outer_monoid_and_inner_semigroup_cdn_homomorphism" {
  let cdn = DualLayerCDN::new(4, 2)
  cdn.register_arith_mapping(1, true, 0, true, 3.0, 5.0)
  cdn.register_arith_mapping(2, true, 1, false, 8.0, 7.0)

  let e = OuterMonoidElem::identity(4)
  let a = OuterMonoidElem::identity(4)
  a.values[1] = True
  let b = OuterMonoidElem::identity(4)
  b.values[2] = True

  // Verify identity law: e (+) a == a
  let ea = outer_monoid_compose(e, a)
  assert_eq(ea.values[1], True)
  assert_eq(ea.has_conflict, false)

  // Verify CDN homomorphism: Phi(a (+) b) == Phi(a) (x) Phi(b)
  let ab = outer_monoid_compose(a, b)
  let phi_ab = cdn.map_outer_to_inner(ab)
  let phi_a = cdn.map_outer_to_inner(a)
  let phi_b = cdn.map_outer_to_inner(b)
  let composed_inner = inner_semigroup_compose(phi_a, phi_b)

  assert_eq(phi_ab.lower_bounds[0], composed_inner.lower_bounds[0])
  assert_eq(phi_ab.upper_bounds[1], composed_inner.upper_bounds[1])
  assert_eq(phi_ab.qap_lower_bound, composed_inner.qap_lower_bound)
}

///|
test "hpa_star_closure_and_kleisli_unification_graph" {
  let hpa = HpaCongruenceClosure::new()
  let t_x = hpa.intern_term(Var("x", 1))
  let t_y = hpa.intern_term(Var("y", 2))
  let t_fx = hpa.intern_term(App("f", [t_x]))
  let t_fy = hpa.intern_term(App("f", [t_y]))
  let t_ffx = hpa.intern_term(App("f", [t_fx]))
  let t_ffy = hpa.intern_term(App("f", [t_fy]))

  let kleisli = KleisliUnificationGraph::new(hpa)
  let unify_res = kleisli.unify_kleisli(t_x, t_y, 1)
  assert_true(unify_res is None)

  // Propagate *Closure: x == y ==> f(x) == f(y) ==> f(f(x)) == f(f(y))
  let conflict = hpa.propagate_star_closure()
  assert_true(conflict is None)
  assert_eq(hpa.are_congruent(t_ffx, t_ffy), true)

  // Now assert disequality f(f(x)) != f(f(y)) guarded by literal 2
  hpa.assert_neq(t_ffx, t_ffy, 2)
  let conflict2 = hpa.propagate_star_closure()
  assert_true(conflict2 is Some(_))

  // Verify occurs-check detects cyclic unification x == f(x)
  let cyclic = kleisli.unify_kleisli(t_y, t_fy, 3)
  assert_true(cyclic is Some(_))
}

///|
test "omt_gnn_and_svm_rkhs_kernel_mapping" {
  let c1 = Clause::new(0, [1, 2], false, 2, ProblemInput)
  let c2 = Clause::new(1, [-1, 3], false, 2, ProblemInput)
  let weights : Array[Double] = [0.0, 5.0, 1.0, 2.0]
  let gnn = OmtGnn::new(3, [c1, c2], weights)
  gnn.add_euf_congruence_edge(1, 2)
  let activity_scores : Array[Double] = [0.0, 0.4, 0.2, 0.3]
  gnn.forward_message_passing([c1, c2], activity_scores, 3)

  let svm = SvmKernelMapper::new(HybridOmtEuf(0.5, 0.3), 1.0)
  svm.fit_online_sample(gnn.var_embeddings[1], -1.0)
  svm.fit_online_sample(gnn.var_embeddings[2], 1.0)

  let bscore = gnn.predict_branch_score(2, svm)
  assert_true(bscore > 0.0 && bscore < 1.0)
  let rkhs = svm.rkhs_spectral_margin_norm()
  assert_true(rkhs > 0.0)
}

///|
test "vsids_activity_decay_phase_saving_and_hybrid6_bounds" {
  let vsids = VsidsOracle::new(4)
  assert_eq(vsids.activity_of(1), 0.0)
  assert_eq(vsids.is_phase_known(1), false)
  vsids.on_assign(1, true)
  assert_eq(vsids.is_phase_known(1), true)
  assert_eq(vsids.saved_phase_of(1), true)
  vsids.on_conflict([1, 2])
  // Bumped by the decayed increment (1.0 / 0.95 > 1.0); non-participants stay at 0.
  assert_true(vsids.activity_of(1) > vsids_var_inc_initial)
  assert_true(vsids.activity_of(2) > vsids_var_inc_initial)
  assert_eq(vsids.activity_of(3), 0.0)
  assert_true(vsids.var_inc > vsids_var_inc_initial)
  // The highest-activity unassigned variable is selected (variable 1 is already assigned).
  let vals : Array[TruthVal] = [Unassigned, True, Unassigned, Unassigned, Unassigned]
  assert_eq(vsids.select_branch_var(vals).unwrap(), 2)
  // Normalised activities are the GNN feature and stay inside [0, 1].
  let norm = vsids.normalized_activity_scores()
  assert_eq(norm[2], 1.0)
  assert_true(norm[3] >= 0.0 && norm[3] <= 1.0)
  // Explicit phase hints (used by the OMT incumbent and the optimality lemma engine).
  vsids.hint_phase(3, true)
  assert_eq(vsids.saved_phase_of(3), true)

  let h6 = Hybrid6DynamicLowerBound::new()
  let gnn = OmtGnn::new(4, [], [0.0, 2.0, 3.0, 1.0, 4.0])
  let svm = SvmKernelMapper::new(RbfGaussian(0.5), 1.0)
  let fused = h6.update_and_fuse(
    vals,
    [0.0, 2.0, 3.0, 1.0, 4.0],
    [1.2, 2.1],
    [5.0, 6.0],
    [2.0, 3.0],
    [true, true],
    12.0,
    [(1, 3)],
    gnn,
    svm,
  )
  // LB2 uses ceil(1.2)=2, ceil(2.1)=3 => 2*2 + 3*3 + 2(v1=True) = 15.0
  assert_eq(fused, 15.0)
  assert_eq(h6.should_prune(14.0), true)
}

///|
test "spoly_and_surjective_axiom_upper_bound_projection" {
  // f = x_0^2 * x_1 - 1, g = x_0 * x_1^2 - x_0
  // S(f, g) = x_1 * f - x_0 * g = x_0^2 - x_1
  let f : MultivariatePoly = {
    num_vars: 2,
    terms: [
      { coeff: 1.0, exponents: [2, 1], },
      { coeff: -1.0, exponents: [0, 0], },
    ],
  }
  let g : MultivariatePoly = {
    num_vars: 2,
    terms: [
      { coeff: 1.0, exponents: [1, 2], },
      { coeff: -1.0, exponents: [1, 0], },
    ],
  }
  let s = compute_spoly(f, g)
  // Evaluate S(f, g) at (x_0 = 3, x_1 = 2): 3^2 - 2 = 7
  assert_eq(s.eval([3.0, 2.0]), 7.0)

  // Multivariate division: reducing a polynomial by itself, and (x_0^2 - 1) by (x_0 - 1),
  // both leave the zero polynomial in the ideal quotient.
  assert_eq(reduce_poly_modulo_ideal(f, [f]).terms.length(), 0)
  let xsq_minus_1 : MultivariatePoly = {
    num_vars: 1,
    terms: [
      { coeff: 1.0, exponents: [2], },
      { coeff: -1.0, exponents: [0], },
    ],
  }
  let x_minus_1 : MultivariatePoly = {
    num_vars: 1,
    terms: [
      { coeff: 1.0, exponents: [1], },
      { coeff: -1.0, exponents: [0], },
    ],
  }
  assert_eq(reduce_poly_modulo_ideal(xsq_minus_1, [x_minus_1]).terms.length(), 0)

  let proj = SurjectiveAxiomProjector::new()
  let projected_clauses = proj.project_upper_bound_clauses(
    [0.0, 4.0, 5.0, 9.0],
    8.5,
    10,
  )
  // v3 (weight 9.0 >= 8.5) gets unit clause [-3]; pair (v1, v2) (4+5=9 >= 8.5) gets binary clause [-1, -2]
  assert_eq(projected_clauses.length(), 2)
  assert_eq(proj.upper_bound_projections, 2)
  // The per-category coverage counters are now readable, and every projected clause is
  // certified exactly once (all of them carry AxiomOrigin::OptimalBoundLemma).
  let coverage = proj.schema_coverage_report()
  assert_eq(coverage.length(), 8)
  assert_eq(coverage[7], 2) // OptimalBoundLemma category
  assert_eq(proj.certified_clause_count(), 2)
}

///|
test "shared_1uip_analysis_returns_asserting_literal_and_backtrack_level" {
  // c0 = (1 v 2) is the reason for literal 2 at level 1; c1 = (-2) is the conflict.
  let c0 = Clause::new(0, [1, 2], false, 2, ProblemInput)
  let c1 = Clause::new(1, [-2], false, 1, ProblemInput)
  let clauses = [c0, c1]
  let trail : Array[Int] = [-1, 2]
  let var_level : Array[Int] = [0, 1, 1]
  let var_reason : Array[Int] = [0, -1, 0]
  let (learnt, bt_level, lbd, participating, reason_vars) = analyze_conflict_1uip_from_trail(
    2, 1, trail, var_level, var_reason, clauses, [-2],
  )
  // The single current-level literal of the conflict is its own first UIP.
  assert_eq(learnt.length(), 1)
  assert_eq(learnt[0], -2)
  assert_eq(bt_level, 0)
  assert_eq(lbd, 1)
  assert_eq(participating.length(), 1)
  assert_eq(participating[0], 2)
  assert_eq(reason_vars.length(), 0)
}

///|
test "distinct_decision_levels_certifies_clause_lbd" {
  let var_level : Array[Int] = [0, 3, 3, 1, 2]
  assert_eq(distinct_decision_levels([-2, -3], var_level), 2)
  assert_eq(distinct_decision_levels([2, -2], var_level), 1)
  assert_eq(distinct_decision_levels([1, -2, -3], var_level), 2)
  assert_eq(distinct_decision_levels([1], var_level), 1)
  assert_eq(distinct_decision_levels([], var_level), 1)
}

///|
test "implication_graph_records_and_verifies_a_conflict" {
  let graph = ImplicationGraph::new(3)
  // var 1 = True (decision), var 2 = False (implied by c0 = (-1 v -2) as -2 = not 1 ...):
  // the assigned literals are 1 and -2, so the reason clause literal -1 must be looked up
  // through its negation (1).
  let c0 = Clause::new(0, [-1, -2], false, 2, ProblemInput)
  let _ = graph.record_decision(1, 1)
  let _ = graph.record_implication(-2, 1, 0, [1])
  assert_eq(graph.node_of(1) >= 0, true)
  assert_eq(graph.node_of(-2) >= 0, true)
  // Conflict clause c1 = (2) is falsified by -2; it is justified by the node of -2.
  let values : Array[TruthVal] = [Unassigned, True, False, Unassigned]
  graph.record_conflict([2])
  assert_eq(graph.all_lits_justified([2], values), true)
  assert_eq(graph.all_lits_justified([1], values), false)
  assert_eq(graph.verify(), true)
  assert_eq(graph.decisions, 1)
  assert_eq(graph.implications, 1)
  let svg = graph.to_svg()
  assert_true(svg.contains("<svg"))
  assert_true(svg.contains("CDCL(T) implication graph"))
}

///|
test "vector_incremental_topology_and_fine_grained_reactive_dag" {
  let topo = VectorTopologyGraph::new(0.01)
  // Insert two crossing segments (0,0)->(10,10) and (0,10)->(10,0); intersection at (5,5)
  let _ = topo.insert_segment_incremental(
    { x: 0.0, y: 0.0, },
    { x: 10.0, y: 10.0, },
    1,
  )
  let _ = topo.insert_segment_incremental(
    { x: 0.0, y: 10.0, },
    { x: 10.0, y: 0.0, },
    2,
  )
  // 5 vertices: (0,0), (10,10), (0,10), (10,0), and intersection (5,5)
  assert_eq(topo.vertices.length(), 5)
  assert_eq(topo.incremental_splits, 1)
  assert_eq(topo.active_undirected_edge_count(), 4)

  // Fine-grained reactive graph
  let rg = FineGrainedReactiveGraph::new()
  let s0 = rg.create_signal(10.0, 0)
  let s1 = rg.create_signal(20.0, 1)
  let _ = rg.create_computed(ComputedSum, [s0], 0)
  let _ = rg.create_computed(ComputedScale(2.0), [s1], 1)
  let _ = rg.propagate_dirty() // clear initial creation dirty flags

  // Mutate only s0 -> only primitive 0 should be invalidated
  rg.set_signal(s0, 15.0)
  let dirty_prims = rg.propagate_dirty()
  assert_eq(dirty_prims.length(), 1)
  assert_eq(dirty_prims[0], 0)
}

///|
test "rtree_sparse_grid_stroke_clustering_and_dirty_rect_coalescing" {
  let rtree = RTree::new(4)
  for i = 0; i < 10; i = i + 1 {
    let base = (i * 20).to_double()
    rtree.insert(i, Aabb::new(base, base, base + 10.0, base + 10.0))
  }
  // Query box [0, 0, 35, 35] only hits primitives 0 and 1
  let hits = rtree.query_aabb(Aabb::new(0.0, 0.0, 35.0, 35.0))
  assert_eq(hits.length(), 2)

  // Sparse grid Morton encoding & tile query
  let grid = SparseSpatialGrid::new(16.0, 32)
  grid.insert_primitive(42, Aabb::new(18.0, 18.0, 30.0, 30.0))
  let ghits = grid.query_primitives_in_rect(Aabb::new(16.0, 16.0, 31.0, 31.0))
  assert_eq(ghits.length(), 1)
  assert_eq(ghits[0], 42)

  // Dirty rect coalescing
  let dt = DirtyRectTracker::new(200.0, 200.0, 1.25)
  dt.mark_dirty_aabb(Aabb::new(10.0, 10.0, 30.0, 30.0))
  dt.mark_dirty_aabb(Aabb::new(20.0, 20.0, 40.0, 40.0)) // overlaps -> merges
  dt.mark_dirty_aabb(Aabb::new(150.0, 150.0, 170.0, 170.0)) // far away -> stays separate
  let coalesced = dt.coalesce_dirty_regions()
  assert_eq(coalesced.length(), 2)
}

///|
test "zero_copy_vbo_arena_sdf_atlas_and_shaders" {
  let arena = FlatVertexArena::new()
  let col = ColorRgba::new(0.2, 0.6, 1.0, 1.0)
  let verts : Array[GpuVertex] = [
    { x: 0.0, y: 0.0, u: 0.0, v: 0.0, color: col, },
    { x: 10.0, y: 0.0, u: 1.0, v: 0.0, color: col, },
    { x: 10.0, y: 10.0, u: 1.0, v: 1.0, color: col, },
  ]
  let slice = arena.allocate_mesh(verts, [0, 1, 2])
  let moved_slice = arena.translate_slice_in_place(slice, 5.0, 7.0)
  let aabb = arena.compute_slice_aabb(moved_slice)
  assert_eq(aabb.min_x, 5.0)
  assert_eq(aabb.max_x, 15.0)
  assert_eq(aabb.min_y, 7.0)
  assert_eq(aabb.max_y, 17.0)

  let sdf = SdfTextureAtlas::bake_from_shapes(16, 16, [
    SdfCircle({ x: 0.5, y: 0.5, }, 0.3),
  ])
  // Center (0.5, 0.5) is inside circle => negative signed distance
  assert_true(sdf.sample_bilinear(0.5, 0.5) < 0.0)
  // Corner (0.0, 0.0) is outside circle => positive signed distance
  assert_true(sdf.sample_bilinear(0.0, 0.0) > 0.0)
}
