///|
/// Whitebox Unit Tests for Internal Invariants, Semigroup/Monoid Laws,
/// HPA *Closure, Kleisli Unification, OMT-GNN, SVM Kernels, LRB, QAP, and CAC Ideal Reduction.

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
  let lrb_scores : Array[Double] = [0.0, 0.4, 0.2, 0.3]
  gnn.forward_message_passing([c1, c2], lrb_scores, 3)

  let svm = SvmKernelMapper::new(HybridOmtEuf(0.5, 0.3), 1.0)
  svm.fit_online_sample(gnn.var_embeddings[1], -1.0)
  svm.fit_online_sample(gnn.var_embeddings[2], 1.0)

  let bscore = gnn.predict_branch_score(2, svm)
  assert_true(bscore > 0.0 && bscore < 1.0)
  let rkhs = svm.rkhs_spectral_margin_norm()
  assert_true(rkhs > 0.0)
}

///|
test "lrb_erwa_reason_side_locality_and_hybrid6_bounds" {
  let lrb = LrbBrancher::new(4)
  lrb.on_assign(1, true)
  lrb.on_assign(2, false)
  let vals : Array[TruthVal] = [Unassigned, True, False, Unassigned, Unassigned]
  lrb.on_conflict([1], [2], vals)
  lrb.on_unassign(1)
  lrb.on_unassign(2)
  assert_true(lrb.ema_lr[1] > 0.15)
  assert_true(lrb.ema_lr[3] < 0.15) // decayed by 0.95 locality factor

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
  // certified exactly once (all of them carry AxiomOrigin::LrbOptimalLemma).
  let coverage = proj.schema_coverage_report()
  assert_eq(coverage.length(), 9)
  assert_eq(coverage[8], 2) // LrbOptimalLemma category
  assert_eq(proj.certified_clause_count(), 2)
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
