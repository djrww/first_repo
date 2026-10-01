///|
/// Cooperative LRB (Learning Rate Branching),
/// Hybrid 6-Dynamic Lower-Bound Incremental Discrete Pruning,
/// QAP (Quadratic Assignment Problem) Incremental Discrete Pruner,
/// and Deep-Fusion Adaptive LRB Incremental Optimal Solution Lemma Engine.

///|
/// LRB (Learning Rate Branching) heuristic state with ERWA, Reason-Side Rate,
/// Locality Decay, and GNN-SVM Hybrid Fusion.
pub(all) struct LrbBrancher {
  num_vars : Int
  mut alpha : Double // Step-size alpha decaying from 0.40 -> 0.06
  mut total_conflicts : Int
  ema_lr : Array[Double] // 1-indexed EMA learning rate q_v
  assigned_at : Array[Int] // conflict count when v was assigned
  participated : Array[Int] // conflict participations since v was assigned
  reason_side : Array[Int] // reason-side participations since v was assigned
  saved_phase : Array[Bool] // phase saving / neural optimal phase
  phase_valid : Array[Bool] // whether saved_phase holds an actually observed phase
}

///|
/// Initial LRB step size.
let lrb_alpha_start : Double = 0.40

///|
/// Lower bound of the LRB step size.
let lrb_alpha_floor : Double = 0.06

///|
/// Number of conflicts over which the step size decays linearly from start to floor.
let lrb_alpha_decay_conflicts : Int = 2000

///|
/// Create and initialize a new LrbBrancher for `num_vars` Boolean variables.
pub fn LrbBrancher::new(num_vars : Int) -> LrbBrancher {
  let ema_lr = Array::make(num_vars + 1, 0.15)
  let assigned_at = Array::make(num_vars + 1, 0)
  let participated = Array::make(num_vars + 1, 0)
  let reason_side = Array::make(num_vars + 1, 0)
  let saved_phase = Array::make(num_vars + 1, false)
  let phase_valid = Array::make(num_vars + 1, false)
  {
    num_vars,
    alpha: lrb_alpha_start,
    total_conflicts: 0,
    ema_lr,
    assigned_at,
    participated,
    reason_side,
    saved_phase,
    phase_valid,
  }
}

///|
/// Notify LRB that variable `v` has been assigned polarity `phase`.
pub fn LrbBrancher::on_assign(
  self : LrbBrancher,
  v : Int,
  phase : Bool,
) -> Unit {
  if v >= 1 && v <= self.num_vars {
    self.assigned_at[v] = self.total_conflicts
    self.participated[v] = 0
    self.reason_side[v] = 0
    self.saved_phase[v] = phase
    self.phase_valid[v] = true
  }
}

///|
/// Notify LRB that variable `v` has been unassigned during backtracking/backjumping.
/// Updates `ema_lr[v]` using Exponential Recency Weighted Average (ERWA).
pub fn LrbBrancher::on_unassign(self : LrbBrancher, v : Int) -> Unit {
  if v >= 1 && v <= self.num_vars {
    let interval = self.total_conflicts - self.assigned_at[v]
    if interval > 0 {
      let r = (
          self.participated[v].to_double() +
          0.5 * self.reason_side[v].to_double()
        ) /
        interval.to_double()
      let clamped_r = r.clamp(min=0.0, max=1.0)
      self.ema_lr[v] = (1.0 - self.alpha) * self.ema_lr[v] +
        self.alpha * clamped_r
    }
  }
}

///|
/// Notify LRB of a CDCL(T) conflict: updates step-size alpha, increments participation
/// and reason-side counters, and applies locality decay (0.95) to unassigned variables.
pub fn LrbBrancher::on_conflict(
  self : LrbBrancher,
  conflict_vars : Array[Int],
  reason_vars : Array[Int],
  assigned_vals : Array[TruthVal],
) -> Unit {
  self.total_conflicts = self.total_conflicts + 1
  // Bounded linear step-size schedule: reach the floor within `lrb_alpha_decay_conflicts`
  // conflicts, so the learning rate adapts on a realistic horizon.
  let progress = (self.total_conflicts.to_double() / lrb_alpha_decay_conflicts.to_double()).min(
    1.0,
  )
  self.alpha = lrb_alpha_floor +
    (lrb_alpha_start - lrb_alpha_floor) * (1.0 - progress)
  for v in conflict_vars {
    if v >= 1 && v <= self.num_vars {
      self.participated[v] = self.participated[v] + 1
      // Immediate ERWA boost for conflict variables still assigned
      self.ema_lr[v] = (1.0 - self.alpha) * self.ema_lr[v] + self.alpha * 1.0
    }
  }
  for rv in reason_vars {
    if rv >= 1 && rv <= self.num_vars {
      self.reason_side[rv] = self.reason_side[rv] + 1
    }
  }
  for v = 1; v <= self.num_vars; v = v + 1 {
    if v < assigned_vals.length() && assigned_vals[v] == Unassigned {
      self.ema_lr[v] = self.ema_lr[v] * 0.95
    }
  }
}

///|
/// Select the highest-scoring unassigned literal using Cooperative LRB + GNN + SVM.
pub fn LrbBrancher::select_branch_literal(
  self : LrbBrancher,
  assigned_vals : Array[TruthVal],
  gnn : OmtGnn,
  svm : SvmKernelMapper,
) -> Int? {
  let mut best_var = -1
  let mut best_score = -scan_infinity
  for v = 1; v <= self.num_vars; v = v + 1 {
    let is_unassigned = if v < assigned_vals.length() {
      assigned_vals[v] == Unassigned
    } else {
      true
    }
    if is_unassigned {
      let lrb_score = self.ema_lr[v]
      let gnn_svm_score = gnn.predict_branch_score(v, svm)
      let hybrid_score = 0.70 * lrb_score + 0.30 * gnn_svm_score
      if hybrid_score > best_score {
        best_score = hybrid_score
        best_var = v
      }
    }
  }
  if best_var == -1 {
    return None
  }
  // Phase saving is only trusted for variables whose phase has actually been observed;
  // otherwise the GNN polarity prediction is used instead of the fabricated `false` default.
  let pol = if self.phase_valid[best_var] {
    self.saved_phase[best_var]
  } else {
    gnn.predict_optimal_polarity(best_var)
  }
  Some(mk_lit(best_var, pol))
}

///|
/// 6-Tuple Dynamic Lower Bound State for Cooperative LRB Hybrid-6 Incremental Discrete Pruning
/// (協同LRB混合6動態下邊界增量離散剪枝).
pub(all) struct Hybrid6DynamicLowerBound {
  mut lb1_lra_relaxation : Double // 1. Continuous LRA bound
  mut lb2_lia_integrality : Double // 2. Integer LIA rounding / cut bound
  mut lb3_qap_gilmore_lawler : Double // 3. QAP Gilmore-Lawler assignment bound
  mut lb4_svm_rkhs_margin : Double // 4. Calibrated SVM RKHS spectral margin bound
  mut lb5_euf_congruence_partition : Double // 5. EUF equivalence class forced-equality bound
  mut lb6_gnn_neural_calibrated : Double // 6. GNN calibrated neural lower bound
  mut fused_lower_bound : Double // Supremum of the 6 admissible dynamic lower bounds
  mut prune_triggered_count : Int
}

///|
/// Create a new Hybrid-6 Dynamic Lower-Bound tracker.
pub fn Hybrid6DynamicLowerBound::new() -> Hybrid6DynamicLowerBound {
  {
    lb1_lra_relaxation: 0.0,
    lb2_lia_integrality: 0.0,
    lb3_qap_gilmore_lawler: 0.0,
    lb4_svm_rkhs_margin: 0.0,
    lb5_euf_congruence_partition: 0.0,
    lb6_gnn_neural_calibrated: 0.0,
    fused_lower_bound: 0.0,
    prune_triggered_count: 0,
  }
}

///|
/// Recompute all 6 dynamic lower-bound components and fuse them into the admissible
/// supremum used for incremental discrete pruning. LB4/LB6 are calibrated so that they can
/// only ever raise the fused bound up to the sound components, never above them.
pub fn Hybrid6DynamicLowerBound::update_and_fuse(
  self : Hybrid6DynamicLowerBound,
  assigned_vals : Array[TruthVal],
  bool_obj_weights : Array[Double],
  arith_lb : Array[Double],
  arith_ub : Array[Double],
  arith_obj_weights : Array[Double],
  is_integer : Array[Bool],
  qap_gl_bound : Double,
  euf_congruence_pairs : Array[(Int, Int)],
  gnn : OmtGnn,
  svm : SvmKernelMapper,
) -> Double {
  // Compute Boolean fixed + lower potential
  let mut bool_lb = 0.0
  for v = 1; v < bool_obj_weights.length(); v = v + 1 {
    let w = bool_obj_weights[v]
    let val = if v < assigned_vals.length() {
      assigned_vals[v]
    } else {
      Unassigned
    }
    match val {
      True => bool_lb = bool_lb + w
      False => ()
      Unassigned => if w < 0.0 { bool_lb = bool_lb + w }
    }
  }

  // 1. LB1: LRA continuous relaxation lower bound
  let mut lra_part = 0.0
  for i = 0
      i < arith_obj_weights.length() &&
     i < arith_lb.length() &&
     i < arith_ub.length()
      i = i + 1 {
    let c = arith_obj_weights[i]
    if c >= 0.0 {
      lra_part = lra_part + c * arith_lb[i]
    } else {
      lra_part = lra_part + c * arith_ub[i]
    }
  }
  self.lb1_lra_relaxation = bool_lb + lra_part

  // 2. LB2: LIA integrality tightened lower bound.
  // Only variables that are actually declared integer are rounded; rounding a real
  // variable would over-estimate the bound and could prune away the true optimum.
  let mut lia_part = 0.0
  for i = 0
      i < arith_obj_weights.length() &&
     i < arith_lb.length() &&
     i < arith_ub.length()
      i = i + 1 {
    let c = arith_obj_weights[i]
    let is_int_var = i < is_integer.length() && is_integer[i]
    let ilb = if is_int_var { arith_lb[i].ceil() } else { arith_lb[i] }
    let iub = if is_int_var { arith_ub[i].floor() } else { arith_ub[i] }
    if c >= 0.0 {
      lia_part = lia_part + c * ilb
    } else {
      lia_part = lia_part + c * iub
    }
  }
  // Each per-variable term is already the exact minimum over that variable's integral
  // domain, so no unsound blanket ceiling is applied to the fused expression.
  self.lb2_lia_integrality = bool_lb + lia_part

  // 3. LB3: QAP Gilmore-Lawler lower bound
  self.lb3_qap_gilmore_lawler = qap_gl_bound.max(self.lb1_lra_relaxation)

  // 4. LB4: SVM RKHS spectral margin bound (calibrated below sound LB2/LB3)
  let rkhs_norm = svm.rkhs_spectral_margin_norm()
  let base_sound = self.lb2_lia_integrality.max(self.lb3_qap_gilmore_lawler)
  self.lb4_svm_rkhs_margin = (self.lb1_lra_relaxation + 0.05 * rkhs_norm).min(
    base_sound,
  )

  // 5. LB5: EUF Congruence Partition lower bound (coupled equal variables)
  let mut euf_coupled_bonus = 0.0
  for pair in euf_congruence_pairs {
    let (u, v) = pair
    if u >= 1 &&
      u < assigned_vals.length() &&
      v >= 1 &&
      v < assigned_vals.length() {
      let vu = assigned_vals[u]
      let vv = assigned_vals[v]
      let wu = if u < bool_obj_weights.length() {
        bool_obj_weights[u]
      } else {
        0.0
      }
      let wv = if v < bool_obj_weights.length() {
        bool_obj_weights[v]
      } else {
        0.0
      }
      if vu == True && vv == Unassigned && wv > 0.0 {
        euf_coupled_bonus = euf_coupled_bonus + wv
      } else if vv == True && vu == Unassigned && wu > 0.0 {
        euf_coupled_bonus = euf_coupled_bonus + wu
      }
    }
  }
  self.lb5_euf_congruence_partition = self.lb1_lra_relaxation +
    euf_coupled_bonus

  // 6. LB6: GNN Calibrated Neural Value Lower Bound
  let sound_sup = self.lb1_lra_relaxation
    .max(self.lb2_lia_integrality)
    .max(self.lb3_qap_gilmore_lawler)
    .max(self.lb5_euf_congruence_partition)
  self.lb6_gnn_neural_calibrated = gnn.predict_calibrated_lower_bound(
    assigned_vals, sound_sup,
  )

  self.fused_lower_bound = sound_sup
    .max(self.lb4_svm_rkhs_margin)
    .max(self.lb6_gnn_neural_calibrated)
  self.fused_lower_bound
}

///|
/// Check if the current branch can be pruned under Incremental Discrete Pruning.
pub fn Hybrid6DynamicLowerBound::should_prune(
  self : Hybrid6DynamicLowerBound,
  incumbent_ub : Double,
) -> Bool {
  if self.fused_lower_bound >= incumbent_ub - tol_eps {
    self.prune_triggered_count = self.prune_triggered_count + 1
    true
  } else {
    false
  }
}

///|
/// QAP (Quadratic Assignment Problem) Incremental Discrete Pruner (QAP 增量離散剪枝).
/// Minimizes sum_{i,j,k,l} F_{i,j} D_{k,l} x_{i,k} x_{j,l} + sum_{i,k} C_{i,k} x_{i,k}.
pub(all) struct QapIncrementalPruner {
  n : Int
  base_var : Int
  flow : Array[Array[Double]] // N x N
  dist : Array[Array[Double]] // N x N
  linear_cost : Array[Array[Double]] // N x N
  mut pruned_branches : Int
}

///|
/// Construct a QAP Incremental Discrete Pruner for an N x N instance.
pub fn QapIncrementalPruner::new(
  n : Int,
  base_var : Int,
  flow : Array[Array[Double]],
  dist : Array[Array[Double]],
  linear_cost : Array[Array[Double]],
) -> QapIncrementalPruner {
  { n, base_var, flow, dist, linear_cost, pruned_branches: 0, }
}

///|
/// Map facility `i` (0..n-1) and location `k` (0..n-1) to its Boolean variable ID.
pub fn QapIncrementalPruner::var_of(
  self : QapIncrementalPruner,
  i : Int,
  k : Int,
) -> Int {
  self.base_var + i * self.n + k
}

///|
/// The `(facility, location, variable)` triples whose QAP Boolean variable is currently
/// assigned `True`. Location extraction, feasibility checking and the blocking clause all
/// need exactly this walk over the n x n variable matrix, so it lives in one place.
fn QapIncrementalPruner::assigned_true_vars(
  self : QapIncrementalPruner,
  assigned_vals : Array[TruthVal],
) -> Array[(Int, Int, Int)] {
  let out : Array[(Int, Int, Int)] = []
  for i = 0; i < self.n; i = i + 1 {
    for k = 0; k < self.n; k = k + 1 {
      let v = self.var_of(i, k)
      if v < assigned_vals.length() && assigned_vals[v] == True {
        out.push((i, k, v))
      }
    }
  }
  out
}

///|
/// Compute the incremental Gilmore-Lawler style discrete lower bound under the
/// current partial Boolean assignment `assigned_vals`.
pub fn QapIncrementalPruner::compute_incremental_lower_bound(
  self : QapIncrementalPruner,
  assigned_vals : Array[TruthVal],
) -> Double {
  let n = self.n
  if n == 0 {
    return 0.0
  }
  let assigned_loc = Array::make(n, -1)
  let loc_used = Array::make(n, false)
  for triple in self.assigned_true_vars(assigned_vals) {
    let (i, k, _v) = triple
    assigned_loc[i] = k
    loc_used[k] = true
  }

  let mut committed_cost = 0.0
  // 1. Exact linear + quadratic cost among already-assigned facilities
  for i = 0; i < n; i = i + 1 {
    let ki = assigned_loc[i]
    if ki != -1 {
      committed_cost = committed_cost + self.linear_cost[i][ki]
      for j = 0; j < n; j = j + 1 {
        let kj = assigned_loc[j]
        if kj != -1 {
          committed_cost = committed_cost + self.flow[i][j] * self.dist[ki][kj]
        }
      }
    }
  }

  // 2. For each unassigned facility i, compute minimum possible incremental cost
  // over all non-falsified and unused locations k.
  let mut completion_lb = 0.0
  for i = 0; i < n; i = i + 1 {
    if assigned_loc[i] == -1 {
      let mut best_for_i = arith_infinity
      let mut any_feasible_k = false
      for k = 0; k < n; k = k + 1 {
        let v = self.var_of(i, k)
        let is_falsified = v < assigned_vals.length() &&
          assigned_vals[v] == False
        if !loc_used[k] && !is_falsified {
          any_feasible_k = true
          let mut cost_ik = self.linear_cost[i][k] +
            self.flow[i][i] * self.dist[k][k]
          // Interaction with already-assigned facilities j
          for j = 0; j < n; j = j + 1 {
            let kj = assigned_loc[j]
            if kj != -1 {
              cost_ik = cost_ik +
                self.flow[i][j] * self.dist[k][kj] +
                self.flow[j][i] * self.dist[kj][k]
            } else if j != i {
              // Lower bound on interaction with unassigned facility j
              let mut min_dist_kl = arith_infinity
              for l = 0; l < n; l = l + 1 {
                if l != k && !loc_used[l] {
                  if self.dist[k][l] < min_dist_kl {
                    min_dist_kl = self.dist[k][l]
                  }
                }
              }
              if min_dist_kl < 1.0e14 {
                cost_ik = cost_ik + self.flow[i][j] * min_dist_kl
              }
            }
          }
          if cost_ik < best_for_i {
            best_for_i = cost_ik
          }
        }
      }
      if any_feasible_k {
        completion_lb = completion_lb + best_for_i
      } else {
        // No feasible location left for facility i -> infeasible partial assignment!
        return arith_infinity
      }
    }
  }
  committed_cost + completion_lb
}

///|
/// Evaluate the exact QAP objective for a complete assignment, or return None if incomplete/invalid.
pub fn QapIncrementalPruner::evaluate_complete_assignment(
  self : QapIncrementalPruner,
  assigned_vals : Array[TruthVal],
) -> Double? {
  let n = self.n
  if n == 0 {
    return Some(0.0)
  }
  let perm = Array::make(n, -1)
  let used = Array::make(n, false)
  let count_per_facility = Array::make(n, 0)
  for triple in self.assigned_true_vars(assigned_vals) {
    let (i, k, _v) = triple
    // Two facilities on the same location is not a permutation: reject it here instead
    // of relying on the injected assignment CNF to rule it out.
    if used[k] {
      return None
    }
    perm[i] = k
    used[k] = true
    count_per_facility[i] = count_per_facility[i] + 1
  }
  for i = 0; i < n; i = i + 1 {
    if count_per_facility[i] != 1 {
      return None
    }
  }
  for k = 0; k < n; k = k + 1 {
    if !used[k] {
      return None
    }
  }
  let mut total = 0.0
  for i = 0; i < n; i = i + 1 {
    let ki = perm[i]
    total = total + self.linear_cost[i][ki]
    for j = 0; j < n; j = j + 1 {
      let kj = perm[j]
      total = total + self.flow[i][j] * self.dist[ki][kj]
    }
  }
  Some(total)
}

///|
/// If the QAP incremental lower bound meets or exceeds `incumbent_ub`,
/// synthesize a certified QAP Discrete Pruning Clause blocking the active partial assignment.
pub fn QapIncrementalPruner::try_generate_pruning_clause(
  self : QapIncrementalPruner,
  assigned_vals : Array[TruthVal],
  incumbent_ub : Double,
  next_clause_id : Int,
) -> Clause? {
  if self.n == 0 {
    return None
  }
  let lb = self.compute_incremental_lower_bound(assigned_vals)
  if lb < incumbent_ub - tol_eps {
    return None
  }
  let blocking_lits : Array[Int] = []
  for triple in self.assigned_true_vars(assigned_vals) {
    let (_i, _k, v) = triple
    blocking_lits.push(mk_lit(v, false))
  }
  if blocking_lits.length() == 0 {
    return None
  }
  self.pruned_branches = self.pruned_branches + 1
  Some(
    Clause::new(
      next_clause_id,
      blocking_lits,
      true,
      blocking_lits.length(),
      QapDiscretePruneAxiom(self.pruned_branches),
    ),
  )
}

///|
/// Incumbent-tracking lemma engine (最優解引理引擎).
/// Records the best objective found so far and emits a blocking clause over the incumbent
/// assignment: either the positive-cost literals alone when they already explain the bound,
/// or the full assignment block. The clause is a valid no-better-solution lemma; it is not a
/// minimal explanation and does not do any LRB-specific reasoning beyond phase saving.
pub(all) struct AdaptiveOptimalLemmaEngine {
  mut best_objective : Double
  mut has_incumbent : Bool
  best_assignment : Array[TruthVal]
  mut best_arith_assignment : Array[Double]
  generated_lemmas : Array[Clause]
}

///|
/// Create a new AdaptiveOptimalLemmaEngine.
pub fn AdaptiveOptimalLemmaEngine::new(
  num_vars : Int,
) -> AdaptiveOptimalLemmaEngine {
  {
    best_objective: arith_infinity,
    has_incumbent: false,
    best_assignment: Array::make(num_vars + 1, Unassigned),
    best_arith_assignment: [],
    generated_lemmas: [],
  }
}

///|
/// Record an improving incumbent `obj_val` and synthesize the blocking clause described on
/// the struct: any re-derivation of this assignment cannot improve the objective.
pub fn AdaptiveOptimalLemmaEngine::record_incumbent_and_synthesize_lemma(
  self : AdaptiveOptimalLemmaEngine,
  assigned_vals : Array[TruthVal],
  arith_witness : Array[Double],
  bool_obj_weights : Array[Double],
  obj_val : Double,
  lrb : LrbBrancher,
  next_clause_id : Int,
) -> Clause? {
  if obj_val >= self.best_objective - tol_eps {
    return None
  }
  self.best_objective = obj_val
  self.has_incumbent = true
  for i = 0
      i < assigned_vals.length() && i < self.best_assignment.length()
      i = i + 1 {
    self.best_assignment[i] = assigned_vals[i]
  }
  self.best_arith_assignment = arith_witness.copy()

  // Check if all weights are non-negative and positive-cost True variables alone account for obj_val
  let pos_lits : Array[Int] = []
  let mut pos_sum = 0.0
  let mut has_neg_weight = false
  for v = 1
      v < assigned_vals.length() && v < bool_obj_weights.length()
      v = v + 1 {
    let w = bool_obj_weights[v]
    if w < 0.0 {
      has_neg_weight = true
    }
    match assigned_vals[v] {
      True =>
        if w > 0.0 {
          pos_lits.push(mk_lit(v, false))
          pos_sum = pos_sum + w
          lrb.saved_phase[v] = false
        } else if w < 0.0 {
          lrb.saved_phase[v] = true
        }
      False => if w < 0.0 { lrb.saved_phase[v] = true }
      Unassigned => ()
    }
  }

  let lemma_lits : Array[Int] = if !has_neg_weight &&
    arith_witness.length() == 0 &&
    pos_lits.length() > 0 &&
    pos_sum >= obj_val - tol_eps {
    pos_lits
  } else {
    let full_block : Array[Int] = []
    for v = 1; v < assigned_vals.length(); v = v + 1 {
      match assigned_vals[v] {
        True => full_block.push(mk_lit(v, false))
        False => full_block.push(mk_lit(v, true))
        Unassigned => ()
      }
    }
    full_block
  }
  if lemma_lits.length() == 0 {
    return None
  }
  let scaled_bound = (obj_val * 100.0).to_int()
  let lemma = Clause::new(
    next_clause_id,
    lemma_lits,
    true,
    lemma_lits.length().min(4),
    LrbOptimalLemma(scaled_bound),
  )
  self.generated_lemmas.push(lemma)
  Some(lemma)
}
