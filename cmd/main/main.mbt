///|
/// Main CLI Runner for the Self-Developed OMT + GNN + SVM + HPA *Closure +
/// Kleisli + BBF + LRB + Hybrid-6 + QAP + CAC + CDCL(T) Lazy SMT Solver.
fn main {
  println(
    "================================================================================",
  )
  println(
    "  MoonBit Self-Developed OMT + GNN + CDCL(T) + Lazy SMT Unified Solver Engine",
  )
  println(
    "================================================================================",
  )

  // 1. Run Scenario 1: Lazy SMT + LRA + LIA + EUF (HPA *Closure & Kleisli) + OMT
  let res1 = @lib.run_lazy_smt_lra_lia_euf_omt_scenario()
  println(
    "\n[1] Lazy SMT + CDCL(T) + LRA + LIA + EUF (HPA *Closure & Kleisli) + OMT:",
  )
  println("    - Satisfiable                    : \{res1.satisfiable}")
  println("    - Optimal Objective Value        : \{res1.optimal_objective}")
  println(
    "    - Best Arithmetic Witness (x0,x1): (\{res1.best_arith_model[0]}, \{res1.best_arith_model[1]})",
  )
  println(
    "    - CDCL(T) Conflicts / Decisions  : \{res1.total_conflicts} / \{res1.total_decisions}",
  )
  println("    - BCP + Theory Propagations      : \{res1.total_propagations}")
  println(
    "    - EUF HPA *Closure Classes       : \{res1.euf_congruence_classes}",
  )
  println(
    "    - BBF Distributed Snapshots/Rest.: \{res1.bbf_snapshots_taken} / \{res1.bbf_restorations}",
  )
  println(
    "    - Conservation Ideal Verified    : \{res1.conservation_ideal_verified}",
  )
  println(
    "    - Surjective Axiom Clauses Cert. : \{res1.surjective_axiom_certified_clauses}",
  )

  // 2. Run Scenario 2: QAP Incremental Discrete Pruning + Dual-Layer CDN + LRB Hybrid-6
  let res2 = @lib.run_qap_lrb_hybrid6_scenario()
  println(
    "\n[2] Inner-Outer Semigroup Dual-Layer CDN + QAP Incremental Discrete Pruning + LRB Hybrid-6:",
  )
  println("    - Satisfiable                    : \{res2.satisfiable}")
  println("    - Optimal 3x3 QAP Objective      : \{res2.optimal_objective}")
  println("    - Hybrid-6 Fused Lower Bound     : \{res2.hybrid6_final_lb}")
  println("    - QAP Pruned Branches            : \{res2.qap_pruned_branches}")
  println(
    "    - CDCL(T) Conflicts / Decisions  : \{res2.total_conflicts} / \{res2.total_decisions}",
  )
  println(
    "    - Conservation Ideal Verified    : \{res2.conservation_ideal_verified}",
  )
  println(
    "    - Surjective Axiom Clauses Cert. : \{res2.surjective_axiom_certified_clauses}",
  )

  // 3. Run Scenario 3: Ring-Lifted CAC Ideal Reduction & Conservation Invariant
  let (reduced_val, cac_infeasible, conserved, reductions) = @lib.run_cac_ideal_and_conservation_scenario()
  println(
    "\n[3] Ring-Lifted Cylindrical Algebraic Covering (CAC) Ideal Reduction & Homomorphic Ideal:",
  )
  println("    - Polynomial f mod <g1, g2> Val  : \{reduced_val}")
  println("    - CAC Fiber Covering Conflict    : \{cac_infeasible}")
  println("    - Ideal Reductions Executed      : \{reductions}")
  println("    - Resolution Ideal Conservation  : \{conserved}")

  // 4. Run Scenario 4: LRA vs. LIA Integrality Cut Separation + OMT
  let res4 = @lib.run_lra_vs_lia_integrality_cut_scenario()
  println("\n[4] Lazy SMT + LRA vs. LIA Integrality Cut Separation + OMT:")
  println("    - Satisfiable                    : \{res4.satisfiable}")
  println("    - Optimal LIA Objective Value    : \{res4.optimal_objective}")
  println("    - Optimal Integer Witness (x0)   : \{res4.best_arith_model[0]}")
  println(
    "    - Conservation Ideal Verified    : \{res4.conservation_ideal_verified}",
  )

  // 5. Run Scenario 5: Vector & Incremental Raster Rendering System
  let (f1, f2, topo_splits, sdf_samples) = @lib.run_incremental_rendering_system_scenario()
  println(
    "\n[5] Vector & Incremental Raster Rendering System (Full vs. Incremental Frame):",
  )
  println(
    "    - Topology Vertices / Half-Edges : \{f2.topology_vertices} / \{f2.topology_half_edges} (Auto-Splits: \{topo_splits})",
  )
  println(
    "    - Stroke Clusters / Sparse Tiles : \{f2.stroke_clusters_count} / \{f2.active_sparse_tiles}",
  )
  println(
    "    - Frame 1 (Initial) Drawn/Shaded : \{f1.primitives_drawn} prims, \{f1.pixels_shaded_in_frame} px shaded",
  )
  println(
    "    - Frame 2 (Reactive) Dirty Prims : \{f2.dirty_primitives_count} (Coalesced Dirty Rects: \{f2.coalesced_dirty_rects_count})",
  )
  println("    - Frame 2 Dirty Area Ratio       : \{f2.dirty_area_ratio}")
  println(
    "    - Frame 2 Drawn vs. Local Culled : \{f2.primitives_drawn} drawn / \{f2.primitives_locally_culled} locally culled",
  )
  println(
    "    - Frame 2 Local Pixels Shaded    : \{f2.pixels_shaded_in_frame} px (4x RGSS Subsamples: \{f2.subsamples_evaluated_in_frame})",
  )
  println(
    "    - Zero-Copy VBO In-Place Patches : \{f2.zero_copy_in_place_updates}",
  )
  println("    - SDF Bilinear Texture Samples   : \{sdf_samples}")
  println(
    "================================================================================",
  )
}
