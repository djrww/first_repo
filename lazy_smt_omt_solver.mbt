///|
/// Unified Lazy SMT + CDCL(T) + LRA + LIA + EUF + OMT Solver Engine
/// integrating HPA *Closure, Kleisli Unification Graph, BBF Distributed Snapshots,
/// OMT-GNN, SVM Kernel Mapper, Cooperative LRB + Hybrid-6 Dynamic Lower Bound,
/// QAP Incremental Discrete Pruning, Ring-Lifted CAC Ideal Reduction, and
/// Homomorphic Conservation Ideal & Surjective Axiom Invariant Projection.

///|
/// Guarded LRA / LIA linear constraint attached to a Boolean literal.
pub(all) struct GuardedArithConstraint {
  guard_lit : Int // 0 if unconditional, otherwise active when guard_lit is True
  term : LinearTerm
  op : ArithOp
  rhs : Double
  is_lia : Bool
}

///|
/// Guarded EUF / Kleisli equality or disequality attached to a Boolean literal.
pub(all) struct GuardedEufConstraint {
  guard_lit : Int
  lhs_term : Int
  rhs_term : Int
  is_eq : Bool
  use_kleisli : Bool
}

///|
/// LRA (Linear Real Arithmetic) + LIA (Linear Integer Arithmetic) Theory Solver.
pub(all) struct LraLiaTheorySolver {
  num_arith_vars : Int
  base_lb : Array[Double]
  base_ub : Array[Double]
  cur_lb : Array[Double]
  cur_ub : Array[Double]
  lb_reason : Array[Int] // guard_lit that established cur_lb[i]
  ub_reason : Array[Int] // guard_lit that established cur_ub[i]
  is_integer : Array[Bool]
  witness : Array[Double]
  /// Set only when `witness` has been certified to satisfy every active guarded constraint.
  mut witness_certified : Bool
  mut propagation_rounds : Int
  mut witness_repair_rounds : Int
  mut witness_improvement_rounds : Int
  constraints : Array[GuardedArithConstraint]
  mut farkas_conflicts : Int
  mut lia_cuts : Int
}

///|
/// Create a new LRA + LIA Theory Solver.
pub fn LraLiaTheorySolver::new(
  num_arith_vars : Int,
  is_integer : Array[Bool],
) -> LraLiaTheorySolver {
  let base_lb = Array::make(num_arith_vars, 0.0)
  let base_ub = Array::make(num_arith_vars, 100.0)
  let cur_lb = Array::make(num_arith_vars, 0.0)
  let cur_ub = Array::make(num_arith_vars, 100.0)
  let lb_reason = Array::make(num_arith_vars, 0)
  let ub_reason = Array::make(num_arith_vars, 0)
  let witness = Array::make(num_arith_vars, 0.0)
  {
    num_arith_vars,
    base_lb,
    base_ub,
    cur_lb,
    cur_ub,
    lb_reason,
    ub_reason,
    is_integer: is_integer.copy(),
    witness,
    witness_certified: false,
    propagation_rounds: 0,
    witness_repair_rounds: 0,
    witness_improvement_rounds: 0,
    constraints: [],
    farkas_conflicts: 0,
    lia_cuts: 0,
  }
}

///|
/// Set base domain interval `[lb, ub]` for arithmetic variable `v`.
pub fn LraLiaTheorySolver::set_var_domain(
  self : LraLiaTheorySolver,
  v : Int,
  lb : Double,
  ub : Double,
) -> Unit {
  if v >= 0 && v < self.num_arith_vars {
    self.base_lb[v] = lb
    self.base_ub[v] = ub
    self.cur_lb[v] = lb
    self.cur_ub[v] = ub
  }
}

///|
/// Add a guarded LRA or LIA constraint.
pub fn LraLiaTheorySolver::add_constraint(
  self : LraLiaTheorySolver,
  guard_lit : Int,
  term : LinearTerm,
  op : ArithOp,
  rhs : Double,
  is_lia : Bool,
) -> Unit {
  self.constraints.push({ guard_lit, term, op, rhs, is_lia, })
}

///|
/// Check whether `lit` evaluates to True under `values`.
pub fn is_lit_true(lit : Int, values : Array[TruthVal]) -> Bool {
  if lit == 0 {
    return true
  }
  let v = lit_var(lit)
  if v < 1 || v >= values.length() {
    return false
  }
  match (values[v], lit > 0) {
    (True, true) => true
    (False, false) => true
    _ => false
  }
}

///|
/// Check whether `lit` evaluates to False under `values`.
pub fn is_lit_false(lit : Int, values : Array[TruthVal]) -> Bool {
  if lit == 0 {
    return false
  }
  let v = lit_var(lit)
  if v < 1 || v >= values.length() {
    return false
  }
  match (values[v], lit > 0) {
    (True, false) => true
    (False, true) => true
    _ => false
  }
}

///|
/// Push unique negated literal `-r` into `conflict_lits` if `r != 0`.
fn push_conflict_reason(conflict_lits : Array[Int], r : Int) -> Unit {
  if r == 0 {
    return
  }
  let neg_r = lit_neg(r)
  for x in conflict_lits {
    if x == neg_r {
      return
    }
  }
  conflict_lits.push(neg_r)
}

///|
/// Numeric tolerance used by every arithmetic bound comparison.
// tol_eps now lives in solver_tunables.mbt as `tol_eps`



///|
/// Round a `Double` to the nearest integer value, with halves going away from zero.
fn round_half_away(x : Double) -> Double {
  if x >= 0.0 {
    (x + 0.5).floor()
  } else {
    -((-x + 0.5).floor())
  }
}

///|
/// Check whether the linear constraint `term op rhs` holds exactly (up to `tol_eps`).
fn arith_constraint_satisfied(
  term : LinearTerm,
  op : ArithOp,
  rhs : Double,
  point : Array[Double],
) -> Bool {
  let v = term.eval(point)
  match op {
    Le => v <= rhs + tol_eps
    Ge => v >= rhs - tol_eps
    Lt => v <= rhs - tol_eps
    Gt => v >= rhs + tol_eps
    Eq => (v - rhs).abs() <= tol_eps
  }
}

///|
/// Violation magnitude of `term op rhs` at `point`; 0.0 when the constraint holds.
fn arith_constraint_violation(
  term : LinearTerm,
  op : ArithOp,
  rhs : Double,
  point : Array[Double],
) -> Double {
  let v = term.eval(point)
  match op {
    Le => (v - rhs).max(0.0)
    Ge => (rhs - v).max(0.0)
    Lt => (v - rhs + tol_eps).max(0.0)
    Gt => (rhs - v + tol_eps).max(0.0)
    Eq => (v - rhs).abs()
  }
}

///|
/// Try to tighten `cur_lb[v]` up to `bound`.
/// Returns 1 when tightened, 2 when the tightened bounds are contradictory, 0 otherwise.
fn LraLiaTheorySolver::tighten_lower(
  self : LraLiaTheorySolver,
  v : Int,
  bound : Double,
  reason : Int,
) -> Int {
  if bound <= self.cur_lb[v] + tol_eps {
    return 0
  }
  self.cur_lb[v] = bound
  self.lb_reason[v] = reason
  if self.cur_lb[v] > self.cur_ub[v] + tol_eps {
    return 2
  }
  1
}

///|
/// Try to tighten `cur_ub[v]` down to `bound`.
/// Returns 1 when tightened, 2 when the tightened bounds are contradictory, 0 otherwise.
fn LraLiaTheorySolver::tighten_upper(
  self : LraLiaTheorySolver,
  v : Int,
  bound : Double,
  reason : Int,
) -> Int {
  if bound >= self.cur_ub[v] - tol_eps {
    return 0
  }
  self.cur_ub[v] = bound
  self.ub_reason[v] = reason
  if self.cur_lb[v] > self.cur_ub[v] + tol_eps {
    return 2
  }
  1
}

///|
/// Apply integer integrality tightening (ceil of the lower bound, floor of the upper bound)
/// to variable `v`. Returns 1 when tightened, 2 on an integrality contradiction, 0 otherwise.
fn LraLiaTheorySolver::apply_integrality(
  self : LraLiaTheorySolver,
  v : Int,
) -> Int {
  if !self.is_integer[v] {
    return 0
  }
  let int_lb = self.cur_lb[v].ceil()
  let int_ub = self.cur_ub[v].floor()
  if int_lb > int_ub + tol_eps {
    return 2
  }
  let mut changed = 0
  if int_lb > self.cur_lb[v] + tol_eps {
    self.cur_lb[v] = int_lb
    changed = 1
  }
  if int_ub < self.cur_ub[v] - tol_eps {
    self.cur_ub[v] = int_ub
    changed = 1
  }
  changed
}

///|
/// Build a theory conflict clause from the reasons recorded for variable `v`.
/// `integrality` selects the LIA integrality-cut axiom over the LRA Farkas axiom, so the
/// clause origin always reflects the actual cause of the conflict.
fn LraLiaTheorySolver::build_arith_conflict(
  self : LraLiaTheorySolver,
  guard_lit : Int,
  v : Int,
  integrality : Bool,
  next_clause_id : Int,
) -> Clause {
  let lits : Array[Int] = []
  push_conflict_reason(lits, guard_lit)
  push_conflict_reason(lits, self.lb_reason[v])
  push_conflict_reason(lits, self.ub_reason[v])
  let origin = if integrality {
    self.lia_cuts = self.lia_cuts + 1
    LiaIntegralityCut(v)
  } else {
    self.farkas_conflicts = self.farkas_conflicts + 1
    LraFarkasAxiom(self.farkas_conflicts)
  }
  Clause::new(next_clause_id, lits, true, lits.length().max(1), origin)
}

///|
/// Certify the current witness: inside the propagated bounds, integral for integer
/// variables, and satisfying every active guarded constraint exactly.
pub fn LraLiaTheorySolver::is_witness_certified(
  self : LraLiaTheorySolver,
  values : Array[TruthVal],
) -> Bool {
  for v = 0; v < self.num_arith_vars; v = v + 1 {
    if self.witness[v] < self.cur_lb[v] - tol_eps ||
      self.witness[v] > self.cur_ub[v] + tol_eps {
      return false
    }
    if self.is_integer[v] &&
      (self.witness[v] - round_half_away(self.witness[v])).abs() > tol_eps {
      return false
    }
  }
  for c in self.constraints {
    if is_lit_true(c.guard_lit, values) &&
      !arith_constraint_satisfied(c.term, c.op, c.rhs, self.witness) {
      return false
    }
  }
  true
}

///|
/// Tentatively move `witness[v]` to `x`; the move is kept only when the whole witness stays
/// certified against every active guarded constraint.
fn LraLiaTheorySolver::try_witness_value(
  self : LraLiaTheorySolver,
  values : Array[TruthVal],
  v : Int,
  x : Double,
) -> Bool {
  let saved = self.witness[v]
  self.witness[v] = x
  if self.is_witness_certified(values) {
    true
  } else {
    self.witness[v] = saved
    false
  }
}

///|
/// Compute an objective-directed arithmetic witness, repair it against violated active
/// constraints, then improve it coordinate-wise while preserving exact feasibility.
/// `witness_certified` is set only when the final point satisfies every active constraint,
/// so an unverifiable point is never reported as an arithmetic solution.
fn LraLiaTheorySolver::compute_certified_witness(
  self : LraLiaTheorySolver,
  values : Array[TruthVal],
  arith_obj_weights : Array[Double],
) -> Unit {
  // 1. Objective-preferred starting point inside the propagated bounds
  for v = 0; v < self.num_arith_vars; v = v + 1 {
    let w = if v < arith_obj_weights.length() {
      arith_obj_weights[v]
    } else {
      0.0
    }
    self.witness[v] = if w >= 0.0 { self.cur_lb[v] } else { self.cur_ub[v] }
  }
  // 2. Projection repair: repeatedly correct the most violated active constraint
  let mut round = 0
  while round < arith_witness_round_limit {
    round = round + 1
    let mut worst_violation = tol_eps
    let mut worst_idx = -1
    let mut idx = 0
    for c in self.constraints {
      if is_lit_true(c.guard_lit, values) {
        let violation = arith_constraint_violation(
          c.term, c.op, c.rhs, self.witness,
        )
        if violation > worst_violation {
          worst_violation = violation
          worst_idx = idx
        }
      }
      idx = idx + 1
    }
    if worst_idx < 0 {
      break
    }
    let c = self.constraints[worst_idx]
    let activity = c.term.eval(self.witness)
    let needed = match c.op {
      Le | Lt => -(activity - c.rhs)
      Ge | Gt => c.rhs - activity
      Eq =>
        if activity > c.rhs {
          -(activity - c.rhs)
        } else {
          c.rhs - activity
        }
    }
    let mut best_j = -1
    let mut best_abs_coeff = 0.0
    let mut best_target = 0.0
    for pair in c.term.coeffs {
      let (j, a) = pair
      if j < 0 || j >= self.num_arith_vars || a.abs() <= tol_eps {
        continue
      }
      let target = (self.witness[j] + needed / a).clamp(
        min=self.cur_lb[j],
        max=self.cur_ub[j],
      )
      let snapped = if self.is_integer[j] {
        round_half_away(target)
      } else {
        target
      }
      let clamped = snapped.clamp(min=self.cur_lb[j], max=self.cur_ub[j])
      if (clamped - self.witness[j]).abs() > tol_eps &&
        a.abs() > best_abs_coeff {
        best_abs_coeff = a.abs()
        best_j = j
        best_target = clamped
      }
    }
    if best_j < 0 {
      break
    }
    self.witness[best_j] = best_target
    self.witness_repair_rounds = round
  }
  // 3. Coordinate-wise objective improvement, keeping the witness exactly feasible
  let mut pass = 0
  let mut improved = true
  while improved && pass < arith_witness_round_limit {
    improved = false
    pass = pass + 1
    for v = 0; v < self.num_arith_vars; v = v + 1 {
      let w = if v < arith_obj_weights.length() {
        arith_obj_weights[v]
      } else {
        0.0
      }
      let target = if w >= 0.0 { self.cur_lb[v] } else { self.cur_ub[v] }
      let start = self.witness[v]
      if (target - start).abs() <= tol_eps {
        continue
      }
      if self.try_witness_value(values, v, target) {
        improved = true
        continue
      }
      // Binary search the furthest feasible step towards the objective-preferred bound
      let mut lo = start
      let mut hi = target
      for _i = 0; _i < 48; _i = _i + 1 {
        let mid = 0.5 * (lo + hi)
        let snapped = if self.is_integer[v] { round_half_away(mid) } else { mid }
        let clamped = snapped.clamp(min=self.cur_lb[v], max=self.cur_ub[v])
        if (clamped - start).abs() <= tol_eps {
          break
        } else if self.try_witness_value(values, v, clamped) {
          lo = clamped
          improved = true
        } else {
          hi = clamped
        }
      }
    }
  }
  self.witness_improvement_rounds = pass
  self.witness_certified = self.is_witness_certified(values)
}

///|
/// Execute LRA + LIA bound propagation to a fixpoint, integer integrality tightening, and
/// sound interval-based infeasibility detection.
/// Returns `Some(conflict_clause)` only when the active guarded constraints are provably
/// inconsistent, or `None` otherwise. The candidate arithmetic witness is always certified
/// against every active constraint before `witness_certified` is set.
pub fn LraLiaTheorySolver::propagate_and_check(
  self : LraLiaTheorySolver,
  values : Array[TruthVal],
  arith_obj_weights : Array[Double],
  next_clause_id : Int,
) -> Clause? {
  // Reset bounds to base domain
  for i = 0; i < self.num_arith_vars; i = i + 1 {
    self.cur_lb[i] = self.base_lb[i]
    self.cur_ub[i] = self.base_ub[i]
    self.lb_reason[i] = 0
    self.ub_reason[i] = 0
  }
  self.witness_certified = false
  self.propagation_rounds = 0
  self.witness_repair_rounds = 0
  self.witness_improvement_rounds = 0

  // Iterative bound propagation over every active guarded constraint until fixpoint.
  // Every derived bound is a necessary condition of the active constraints and of the
  // current variable domains, so each contradiction detected here is a sound theory lemma.
  let mut round = 0
  let mut changed = true
  while changed && round < arith_propagation_round_limit {
    changed = false
    round = round + 1
    for c in self.constraints {
      if !is_lit_true(c.guard_lit, values) {
        continue
      }
      let rhs = c.rhs - c.term.constant
      for pair in c.term.coeffs {
        let (vj, aj) = pair
        if vj < 0 || vj >= self.num_arith_vars || aj.abs() <= tol_eps {
          continue
        }
        // Interval bounds of the remaining terms of this constraint
        let mut min_rest = 0.0
        let mut max_rest = 0.0
        for other in c.term.coeffs {
          let (vi, ai) = other
          if vi == vj || vi < 0 || vi >= self.num_arith_vars {
            continue
          }
          if ai >= 0.0 {
            min_rest = min_rest + ai * self.cur_lb[vi]
            max_rest = max_rest + ai * self.cur_ub[vi]
          } else {
            min_rest = min_rest + ai * self.cur_ub[vi]
            max_rest = max_rest + ai * self.cur_lb[vi]
          }
        }
        // `aj * x_j` is bounded above by `rhs - min_rest` and below by `rhs - max_rest`
        if c.op == Le || c.op == Lt || c.op == Eq {
          let mut upper = rhs - min_rest
          if c.op == Lt {
            upper = upper - tol_eps
          }
          let status = if aj > 0.0 {
            self.tighten_upper(vj, upper / aj, c.guard_lit)
          } else {
            self.tighten_lower(vj, upper / aj, c.guard_lit)
          }
          if status == 2 {
            // An integer variable whose bounds became contradictory is separated by the
            // integrality cut, an integer-free variable by the real-relaxation (Farkas) axiom.
            return Some(
              self.build_arith_conflict(
                c.guard_lit, vj, self.is_integer[vj], next_clause_id,
              ),
            )
          } else if status == 1 {
            changed = true
          }
        }
        if c.op == Ge || c.op == Gt || c.op == Eq {
          let mut lower = rhs - max_rest
          if c.op == Gt {
            lower = lower + tol_eps
          }
          let status = if aj > 0.0 {
            self.tighten_lower(vj, lower / aj, c.guard_lit)
          } else {
            self.tighten_upper(vj, lower / aj, c.guard_lit)
          }
          if status == 2 {
            return Some(
              self.build_arith_conflict(
                c.guard_lit, vj, self.is_integer[vj], next_clause_id,
              ),
            )
          } else if status == 1 {
            changed = true
          }
        }
        let int_status = self.apply_integrality(vj)
        if int_status == 2 {
          return Some(
            self.build_arith_conflict(c.guard_lit, vj, true, next_clause_id),
          )
        } else if int_status == 1 {
          changed = true
        }
      }
    }
  }

  // Final integrality sweep so integer bounds are tightened even when no constraint
  // touched the variable during the last propagation round.
  for v = 0; v < self.num_arith_vars; v = v + 1 {
    let int_status = self.apply_integrality(v)
    if int_status == 2 {
      return Some(self.build_arith_conflict(0, v, true, next_clause_id))
    }
  }
  self.propagation_rounds = round

  // Certify an arithmetic witness against every active constraint
  self.compute_certified_witness(values, arith_obj_weights)
  None
}

///|
/// Complete OMT + Lazy SMT + CDCL(T) Solve Result and Verification Telemetry.
pub(all) struct OmtSolveResult {
  satisfiable : Bool
  optimal_objective : Double
  best_bool_model : Array[TruthVal]
  best_arith_model : Array[Double]
  total_conflicts : Int
  total_decisions : Int
  total_propagations : Int
  hybrid6_final_lb : Double
  qap_pruned_branches : Int
  euf_congruence_classes : Int
  bbf_snapshots_taken : Int
  bbf_restorations : Int
  cac_ideal_reductions : Int
  conservation_ideal_verified : Bool
  surjective_axiom_certified_clauses : Int
  /// Clauses that failed origin/hash certification. Non-zero means the surjective-axiom
  /// claim does not hold for this run.
  axiom_certification_failures : Int
  /// Certified-clause count per `AxiomOrigin` category (9 categories, declaration order).
  axiom_schema_coverage : Array[Int]
}

///|
/// Unified Self-Developed OMT + GNN + SVM + HPA *Closure + Kleisli + BBF +
/// LRB + Hybrid-6 + QAP + CAC + CDCL(T) Lazy SMT Solver.
pub(all) struct LazySmtOmtSolver {
  num_vars : Int
  num_arith_vars : Int
  clauses : Array[Clause]
  values : Array[TruthVal] // 1-indexed
  trail : Array[Int] // chronological stack of assigned literals
  trail_lim : Array[Int] // decision level boundaries in trail
  var_level : Array[Int] // decision level of each variable
  var_reason : Array[Int] // clause index in `clauses` or -1 for decision
  bool_obj_weights : Array[Double] // 1-indexed Boolean objective weights
  arith_obj_weights : Array[Double] // 0-indexed arithmetic objective weights
  cdn : DualLayerCDN
  hpa : HpaCongruenceClosure
  kleisli : KleisliUnificationGraph
  euf_constraints : Array[GuardedEufConstraint]
  euf_var_pairs : Array[(Int, Int)]
  bbf : BbfSnapshotManager
  gnn : OmtGnn
  svm : SvmKernelMapper
  lrb : LrbBrancher
  hybrid6 : Hybrid6DynamicLowerBound
  mut qap : QapIncrementalPruner
  /// Number of times the 1-UIP learnt-clause invariant check failed (must stay 0).
  mut learnt_invariant_failures : Int
  /// Number of complete Boolean models rejected because the arithmetic witness could not
  /// be certified against the guarded arithmetic constraints.
  mut uncertified_witness_rejections : Int
  /// Number of clauses whose origin/hash certification failed (must stay 0 for the
  /// surjective-axiom claim to hold).
  mut axiom_certification_failures : Int
  opt_lemma_engine : AdaptiveOptimalLemmaEngine
  cac : CylindricalAlgebraicCovering
  conservation_ideal : HomomorphicConservationIdeal
  axiom_projector : SurjectiveAxiomProjector
  lra_lia : LraLiaTheorySolver
  mut total_decisions : Int
  mut total_propagations : Int
}

///|
/// Construct a new Unified `LazySmtOmtSolver`.
pub fn LazySmtOmtSolver::new(
  num_vars : Int,
  num_arith_vars : Int,
  is_integer_arith : Array[Bool],
  bool_obj_weights : Array[Double],
  arith_obj_weights : Array[Double],
) -> LazySmtOmtSolver {
  let hpa = HpaCongruenceClosure::new()
  let kleisli = KleisliUnificationGraph::new(hpa)
  let gnn = OmtGnn::new(num_vars, [], bool_obj_weights)
  let svm = SvmKernelMapper::new(HybridOmtEuf(0.5, 0.25), 1.0)
  let qap = QapIncrementalPruner::new(0, 1, [], [], [])
  {
    num_vars,
    num_arith_vars,
    clauses: [],
    values: Array::make(num_vars + 1, Unassigned),
    trail: [],
    trail_lim: [],
    var_level: Array::make(num_vars + 1, 0),
    var_reason: Array::make(num_vars + 1, -1),
    bool_obj_weights: bool_obj_weights.copy(),
    arith_obj_weights: arith_obj_weights.copy(),
    cdn: DualLayerCDN::new(num_vars, num_arith_vars),
    hpa,
    kleisli,
    euf_constraints: [],
    euf_var_pairs: [],
    bbf: BbfSnapshotManager::new(),
    gnn,
    svm,
    lrb: LrbBrancher::new(num_vars),
    hybrid6: Hybrid6DynamicLowerBound::new(),
    qap,
    learnt_invariant_failures: 0,
    uncertified_witness_rejections: 0,
      axiom_certification_failures: 0,
    opt_lemma_engine: AdaptiveOptimalLemmaEngine::new(num_vars),
    cac: CylindricalAlgebraicCovering::new(num_arith_vars),
    conservation_ideal: HomomorphicConservationIdeal::new(num_vars),
    axiom_projector: SurjectiveAxiomProjector::new(),
    lra_lia: LraLiaTheorySolver::new(num_arith_vars, is_integer_arith),
    total_decisions: 0,
    total_propagations: 0,
  }
}

///|
/// Return the current CDCL decision level.
pub fn LazySmtOmtSolver::decision_level(self : LazySmtOmtSolver) -> Int {
  self.trail_lim.length()
}

///|
/// Add a CNF clause to the solver and certify its origin in the Surjective Axiom Projector.
pub fn LazySmtOmtSolver::add_clause(
  self : LazySmtOmtSolver,
  lits : Array[Int],
  learnt : Bool,
  origin : AxiomOrigin,
) -> Int {
  self.add_clause_with_lbd(lits, learnt, lits.length().max(1), origin)
}

///|
/// Add a CNF clause with an explicit LBD (Literal Block Distance).
/// Conflict analysis computes the exact LBD, which must not be overwritten by the clause
/// length: LBD drives both clause activity bookkeeping and the GNN clause embeddings.
pub fn LazySmtOmtSolver::add_clause_with_lbd(
  self : LazySmtOmtSolver,
  lits : Array[Int],
  learnt : Bool,
  lbd : Int,
  origin : AxiomOrigin,
) -> Int {
  let id = self.clauses.length()
  let c = Clause::new(id, lits, learnt, lbd.max(1), origin)
  // Hash/origin certification is a real check: a clause that fails it is still added (it is
  // soundly derivable), but the failure is counted so the surjectivity claim stays honest.
  if !self.axiom_projector.certify_clause_origin(c) {
    self.axiom_certification_failures = self.axiom_certification_failures + 1
  }
  self.clauses.push(c)
  id
}

///|
/// Add a guarded EUF / Kleisli constraint to the solver.
pub fn LazySmtOmtSolver::add_euf_constraint(
  self : LazySmtOmtSolver,
  guard_lit : Int,
  lhs_term : Int,
  rhs_term : Int,
  is_eq : Bool,
  use_kleisli : Bool,
) -> Unit {
  self.euf_constraints.push({
    guard_lit,
    lhs_term,
    rhs_term,
    is_eq,
    use_kleisli,
  })
}

///|
/// Attach a QAP Incremental Discrete Pruner and automatically inject its
/// decoupled Dual-Layer CDN assignment CNF clauses.
pub fn LazySmtOmtSolver::attach_qap_pruner(
  self : LazySmtOmtSolver,
  qap : QapIncrementalPruner,
) -> Unit {
  self.qap = qap
  if qap.n > 0 {
    let qap_clauses = generate_qap_assignment_cnf(
      qap.n,
      qap.base_var,
      self.clauses.length(),
    )
    for c in qap_clauses {
      let _ = self.add_clause(c.lits, false, ProblemInput)
    }
  }
}

///|
/// Enqueue literal `lit` at the current decision level with `reason_clause_idx`.
fn LazySmtOmtSolver::enqueue_lit(
  self : LazySmtOmtSolver,
  lit : Int,
  reason_clause_idx : Int,
) -> Bool {
  let v = lit_var(lit)
  let pol = lit_sign(lit)
  if v < 1 || v > self.num_vars {
    return false
  }
  match self.values[v] {
    Unassigned => {
      self.values[v] = if pol { True } else { False }
      self.var_level[v] = self.decision_level()
      self.var_reason[v] = reason_clause_idx
      self.trail.push(lit)
      self.lrb.on_assign(v, pol)
      self.total_propagations = self.total_propagations + 1
      true
    }
    True => pol
    False => !pol
  }
}

///|
/// Backjump to `target_level`, restoring Boolean trail and BBF Distributed Snapshot state.
pub fn LazySmtOmtSolver::backjump(
  self : LazySmtOmtSolver,
  target_level : Int,
) -> Unit {
  if target_level >= self.decision_level() {
    return
  }
  let target_trail_len = self.trail_lim[target_level]
  while self.trail.length() > target_trail_len {
    match self.trail.pop() {
      Some(lit) => {
        let v = lit_var(lit)
        self.lrb.on_unassign(v)
        self.values[v] = Unassigned
        self.var_level[v] = 0
        self.var_reason[v] = -1
      }
      None => break
    }
  }
  while self.trail_lim.length() > target_level {
    let _ = self.trail_lim.pop()
  }
  let _ = self.bbf.restore_to_level(
    target_level,
    self.hpa,
    self.lra_lia.cur_lb,
    self.lra_lia.cur_ub,
  )
}

///|
/// Boolean Constraint Propagation (BCP) over all active clauses.
/// Returns `Some(conflict_clause_idx)` if a clause is falsified, or `None` at fixpoint.
pub fn LazySmtOmtSolver::bcp_propagate(self : LazySmtOmtSolver) -> Int? {
  let mut changed = true
  while changed {
    changed = false
    for ci = 0; ci < self.clauses.length(); ci = ci + 1 {
      let c = self.clauses[ci]
      let mut satisfied = false
      let mut unassigned_count = 0
      let mut last_unassigned_lit = 0
      for lit in c.lits {
        if is_lit_true(lit, self.values) {
          satisfied = true
          break
        } else if !is_lit_false(lit, self.values) {
          unassigned_count = unassigned_count + 1
          last_unassigned_lit = lit
        }
      }
      if !satisfied {
        if unassigned_count == 0 {
          return Some(ci)
        } else if unassigned_count == 1 {
          let ok = self.enqueue_lit(last_unassigned_lit, ci)
          if !ok {
            return Some(ci)
          }
          self.bbf.record_channel_message(0, 1, last_unassigned_lit, 0.0)
          changed = true
        }
      }
    }
  }
  None
}

///|
/// 1-UIP Conflict Analysis with LBD (Literal Block Distance) and Homomorphic Conservation check.
/// Returns `(learnt_lits, backtrack_level, lbd, participating_vars, reason_vars)`.
pub fn LazySmtOmtSolver::analyze_conflict_1uip(
  self : LazySmtOmtSolver,
  conflict_clause : Clause,
) -> (Array[Int], Int, Int, Array[Int], Array[Int]) {
  let cur_level = self.decision_level()
  if cur_level == 0 {
    return ([], 0, 1, [], [])
  }
  let seen = Array::make(self.num_vars + 1, false)
  let learnt : Array[Int] = [0] // placeholder for 1-UIP asserting literal at index 0
  let participating_vars : Array[Int] = []
  let reason_vars : Array[Int] = []
  let mut path_c = 0
  let mut resolvent_steps = 0

  // Initialize from conflict_clause
  for lit in conflict_clause.lits {
    let v = lit_var(lit)
    if v >= 1 && v <= self.num_vars && !seen[v] {
      seen[v] = true
      participating_vars.push(v)
      if self.var_level[v] == cur_level {
        path_c = path_c + 1
      } else if self.var_level[v] > 0 {
        learnt.push(lit)
      }
    }
  }

  // Traverse trail backward to find First UIP
  let mut trail_idx = self.trail.length() - 1
  let mut uip_lit = 0
  while path_c > 0 && trail_idx >= 0 {
    let p = self.trail[trail_idx]
    trail_idx = trail_idx - 1
    let pv = lit_var(p)
    if seen[pv] && self.var_level[pv] == cur_level {
      path_c = path_c - 1
      if path_c == 0 {
        uip_lit = lit_neg(p)
        break
      }
      let r_idx = self.var_reason[pv]
      if r_idx >= 0 && r_idx < self.clauses.length() {
        resolvent_steps = resolvent_steps + 1
        let reason_clause = self.clauses[r_idx]
        for rlit in reason_clause.lits {
          let rv = lit_var(rlit)
          if rv != pv && rv >= 1 && rv <= self.num_vars {
            if !seen[rv] {
              seen[rv] = true
              participating_vars.push(rv)
              reason_vars.push(rv)
              if self.var_level[rv] == cur_level {
                path_c = path_c + 1
              } else if self.var_level[rv] > 0 {
                learnt.push(rlit)
              }
            }
          }
        }
      } else {
        // Decision variable reached with no reason clause
        uip_lit = lit_neg(p)
        break
      }
    }
  }

  if uip_lit == 0 {
    // Fallback: negate active decision literals in conflict_clause
    let fallback : Array[Int] = []
    for lit in conflict_clause.lits {
      fallback.push(lit)
    }
    return (
      fallback,
      (cur_level - 1).max(0),
      fallback.length(),
      participating_vars,
      reason_vars,
    )
  }

  learnt[0] = uip_lit
  // Compute backtrack level (highest level among learnt[1..]) and LBD
  let mut bt_level = 0
  let mut max_idx = 1
  let level_marks : Array[Int] = []
  for i = 0; i < learnt.length(); i = i + 1 {
    let lv = self.var_level[lit_var(learnt[i])]
    let mut lv_seen = false
    for m in level_marks {
      if m == lv {
        lv_seen = true
      }
    }
    if !lv_seen {
      level_marks.push(lv)
    }
    if i >= 1 && lv > bt_level {
      bt_level = lv
      max_idx = i
    }
  }
  if learnt.length() > 2 && max_idx != 1 {
    let tmp = learnt[1]
    learnt[1] = learnt[max_idx]
    learnt[max_idx] = tmp
  }
  let lbd = level_marks.length().max(1)
  let _ = resolvent_steps
  (learnt, bt_level, lbd, participating_vars, reason_vars)
}

///|
/// Run all Lazy SMT Theory Solvers (EUF HPA *Closure, Kleisli Unification,
/// LRA/LIA Simplex-Bound Propagation, CAC Ideal Reduction, Dual-Layer CDN,
/// QAP Incremental Pruner, and Hybrid-6 Dynamic Lower Bound).
/// Returns `Some(theory_conflict_clause)` if any theory or bound check fails.
pub fn LazySmtOmtSolver::check_lazy_theories(
  self : LazySmtOmtSolver,
) -> Clause? {
  // 1. Reset and run EUF HPA *Closure + Kleisli Unification Graph for active literals
  for i = 0; i < self.hpa.terms.length(); i = i + 1 {
    self.hpa.parent[i] = i
    self.hpa.rank[i] = 0
    self.hpa.use_list[i] = []
  }
  for i = 0; i < self.hpa.terms.length(); i = i + 1 {
    match self.hpa.terms[i] {
      App(_, args) =>
        for arg in args {
          if arg >= 0 && arg < self.hpa.use_list.length() {
            self.hpa.use_list[arg].push(i)
          }
        }
      _ => ()
    }
  }
  self.hpa.pending_merges.clear()
  self.hpa.proof_edges.clear()
  self.hpa.disequalities.clear()
  self.kleisli.subst_map.clear()

  for ec in self.euf_constraints {
    if is_lit_true(ec.guard_lit, self.values) {
      if ec.is_eq {
        if ec.use_kleisli {
          match
            self.kleisli.unify_kleisli(ec.lhs_term, ec.rhs_term, ec.guard_lit) {
            Some(kl_conflict) =>
              return Some(
                Clause::new(
                  self.clauses.length(),
                  kl_conflict,
                  true,
                  kl_conflict.length().max(1),
                  KleisliUnificationAxiom(ec.lhs_term),
                ),
              )
            None => ()
          }
        } else {
          self.hpa.assert_eq(ec.lhs_term, ec.rhs_term, ec.guard_lit)
        }
      } else {
        self.hpa.assert_neq(ec.lhs_term, ec.rhs_term, ec.guard_lit)
      }
    }
  }

  match self.hpa.propagate_star_closure() {
    Some(euf_conflict_lits) =>
      return Some(
        Clause::new(
          self.clauses.length(),
          euf_conflict_lits,
          true,
          euf_conflict_lits.length().max(1),
          EufCongruenceAxiom(0, 1),
        ),
      )
    None => ()
  }

  // 2. Run LRA + LIA Theory Solver
  match
    self.lra_lia.propagate_and_check(
      self.values,
      self.arith_obj_weights,
      self.clauses.length(),
    ) {
    Some(arith_conflict) => return Some(arith_conflict)
    None => ()
  }

  // 3. Run Ring-Lifted Cylindrical Algebraic Covering (CAC) Ideal Reduction
  match
    self.cac.check_cylindrical_covering(
      self.lra_lia.witness,
      self.lra_lia.cur_lb,
      self.lra_lia.cur_ub,
      self.clauses.length(),
    ) {
    Some(cac_conflict) => return Some(cac_conflict)
    None => ()
  }

  // 4. Evaluate QAP Incremental Discrete Pruner & Hybrid-6 Dynamic Lower Bound
  let qap_lb = self.qap.compute_incremental_lower_bound(self.values)
  let _ = self.hybrid6.update_and_fuse(
    self.values,
    self.bool_obj_weights,
    self.lra_lia.cur_lb,
    self.lra_lia.cur_ub,
    self.arith_obj_weights,
    self.lra_lia.is_integer,
    qap_lb,
    self.euf_var_pairs,
    self.gnn,
    self.svm,
  )

  if self.opt_lemma_engine.has_incumbent {
    let ub = self.opt_lemma_engine.best_objective
    // Check QAP incremental discrete pruning first
    match
      self.qap.try_generate_pruning_clause(
        self.values,
        ub,
        self.clauses.length(),
      ) {
      Some(qap_clause) => return Some(qap_clause)
      None => ()
    }
    // Check Hybrid-6 dynamic lower bound pruning
    if self.hybrid6.should_prune(ub) {
      let blocking : Array[Int] = []
      for lit in self.trail {
        blocking.push(lit_neg(lit))
      }
      if blocking.length() > 0 {
        return Some(
          Clause::new(
            self.clauses.length(),
            blocking,
            true,
            blocking.length().min(4),
            LrbOptimalLemma((ub * 100.0).to_int()),
          ),
        )
      }
    }
  }
  None
}

///|
/// Evaluate total OMT objective (Boolean linear objective + Arithmetic objective + QAP objective)
/// at a complete assignment.
pub fn LazySmtOmtSolver::evaluate_total_objective(
  self : LazySmtOmtSolver,
) -> Double {
  let mut total = 0.0
  for v = 1; v <= self.num_vars && v < self.bool_obj_weights.length(); v = v + 1 {
    if self.values[v] == True {
      total = total + self.bool_obj_weights[v]
    }
  }
  for i = 0
      i < self.num_arith_vars && i < self.arith_obj_weights.length()
      i = i + 1 {
    total = total + self.arith_obj_weights[i] * self.lra_lia.witness[i]
  }
  if self.qap.n > 0 {
    match self.qap.evaluate_complete_assignment(self.values) {
      Some(qap_cost) => total = total + qap_cost
      None => ()
    }
  }
  total
}

///|
/// Handle a conflict clause (either from BCP or Theory Solver) inside the CDCL(T) loop.
/// Returns `false` if conflict is at decision level 0 (search space exhausted / UNSAT).
fn LazySmtOmtSolver::handle_conflict(
  self : LazySmtOmtSolver,
  conflict_clause : Clause,
) -> Bool {
  // Certify the conflict clause origin; count failures instead of discarding the result.
  if !self.axiom_projector.certify_clause_origin(conflict_clause) {
    self.axiom_certification_failures = self.axiom_certification_failures + 1
  }
  if self.decision_level() == 0 {
    return false
  }
  let (learnt_lits, bt_level, lbd, part_vars, reason_vars) = self.analyze_conflict_1uip(
    conflict_clause,
  )
  self.lrb.on_conflict(part_vars, reason_vars, self.values)

  // Feed negative sample (y = -1.0) to OMT-SVM Kernel Mapper
  if part_vars.length() > 0 {
    let v0 = part_vars[0]
    if v0 >= 1 && v0 <= self.num_vars {
      self.svm.fit_online_sample(self.gnn.var_embeddings[v0], -1.0)
    }
  }

  if learnt_lits.length() == 0 {
    return false
  }
  let learnt_clause = Clause::new(
    self.clauses.length(),
    learnt_lits,
    true,
    lbd,
    UipResolution(part_vars.length(), self.decision_level()),
  )
  // Verify the 1-UIP learnt-clause invariant under the pre-backjump assignment: every
  // literal of a sound 1-UIP clause is falsified before backjumping. When the check fails
  // the clause is not trusted, so the solver falls back to chronological backtracking
  // rather than learning a clause whose entailment cannot be justified.
  if !self.conservation_ideal.verify_learnt_clause_blocks(
    learnt_clause,
    self.values,
  ) {
    self.learnt_invariant_failures = self.learnt_invariant_failures + 1
    let parent_level = (self.decision_level() - 1).max(0)
    self.backjump(parent_level)
    if parent_level == 0 {
      return false
    }
    return true
  }
  self.backjump(bt_level)
  let new_cid = self.add_clause_with_lbd(
    learnt_clause.lits,
    true,
    learnt_clause.lbd,
    learnt_clause.origin,
  )
  if learnt_clause.lits.length() == 1 {
    if !self.enqueue_lit(learnt_clause.lits[0], new_cid) {
      return false
    }
  } else {
    let _ = self.enqueue_lit(learnt_clause.lits[0], new_cid)
  }
  true
}

///|
/// Execute the full Self-Developed OMT + GNN + SVM + CDCL(T) + Lazy SMT Optimization Loop.
pub fn LazySmtOmtSolver::solve_omt(
  self : LazySmtOmtSolver,
  max_conflicts : Int,
) -> OmtSolveResult {
  // Initial GNN message passing warm-up over input CNF & EUF graph
  self.gnn.forward_message_passing(self.clauses, self.lrb.ema_lr, 2)
  let _ = self.bbf.capture_snapshot(
    0,
    0,
    self.hpa,
    self.lra_lia.cur_lb,
    self.lra_lia.cur_ub,
    self.opt_lemma_engine.best_objective,
  )

  let mut search_active = true
  let mut steps = 0
  let max_steps = max_conflicts * arith_step_budget_per_conflict +
    arith_step_budget_base
  while search_active &&
        self.lrb.total_conflicts < max_conflicts &&
        steps < max_steps {
    steps = steps + 1
    // 1. Outer CDCL Boolean Constraint Propagation
    match self.bcp_propagate() {
      Some(conflict_cid) => {
        let conflict_clause = self.clauses[conflict_cid]
        if !self.handle_conflict(conflict_clause) {
          search_active = false
          break
        }
        continue
      }
      None => ()
    }

    // 2. Inner Lazy SMT Theory Propagation & Hybrid-6 / QAP Pruning Check
    match self.check_lazy_theories() {
      Some(theory_conflict_clause) => {
        if !self.handle_conflict(theory_conflict_clause) {
          search_active = false
          break
        }
        continue
      }
      None => ()
    }

    // 3. Periodically refresh OMT-GNN embeddings with LRB conflict learning rates
    if self.lrb.total_conflicts > 0 && self.lrb.total_conflicts % 8 == 0 {
      self.gnn.forward_message_passing(self.clauses, self.lrb.ema_lr, 1)
    }

    // 4. Select next unassigned variable via Cooperative LRB + GNN + SVM
    match self.lrb.select_branch_literal(self.values, self.gnn, self.svm) {
      Some(branch_lit) => {
        self.total_decisions = self.total_decisions + 1
        self.trail_lim.push(self.trail.length())
        let _ = self.enqueue_lit(branch_lit, -1)
        let _ = self.bbf.capture_snapshot(
          self.decision_level(),
          self.trail.length(),
          self.hpa,
          self.lra_lia.cur_lb,
          self.lra_lia.cur_ub,
          self.opt_lemma_engine.best_objective,
        )
      }
      None => {
        // Complete Boolean model found. Before recording it as a solution, require that the
        // arithmetic witness has been certified against every active guarded constraint;
        // an unverifiable witness is never reported as an optimal solution.
        if !self.lra_lia.witness_certified {
          self.uncertified_witness_rejections = self.uncertified_witness_rejections + 1
          if self.decision_level() == 0 {
            search_active = false
            break
          }
          let block_lits : Array[Int] = []
          for lit in self.trail {
            block_lits.push(lit_neg(lit))
          }
          self.backjump(0)
          let _ = self.add_clause(
            block_lits,
            true,
            LraFarkasAxiom(self.lra_lia.farkas_conflicts),
          )
          continue
        }
        let obj = self.evaluate_total_objective()
        // Feed positive sample (y = +1.0) to OMT-SVM Kernel Mapper
        if self.num_vars >= 1 {
          self.svm.fit_online_sample(self.gnn.var_embeddings[1], 1.0)
        }
        match
          self.opt_lemma_engine.record_incumbent_and_synthesize_lemma(
            self.values,
            self.lra_lia.witness,
            self.bool_obj_weights,
            obj,
            self.lrb,
            self.clauses.length(),
          ) {
          Some(opt_lemma) => {
            // Also project Superposed Exhaustive Upper-Bound clauses if pure Boolean objective
            if self.qap.n == 0 && self.num_arith_vars == 0 {
              let ub_clauses = self.axiom_projector.project_upper_bound_clauses(
                self.bool_obj_weights,
                obj,
                self.clauses.length(),
              )
              for ubc in ub_clauses {
                let _ = self.add_clause(ubc.lits, true, ubc.origin)
              }
            }
            // Backtrack to level 0 and add the optimality-improving lemma to search for strictly better solutions
            self.backjump(0)
            let cid = self.add_clause(opt_lemma.lits, true, opt_lemma.origin)
            if opt_lemma.lits.length() == 1 {
              if !self.enqueue_lit(opt_lemma.lits[0], cid) {
                search_active = false
                break
              }
            }
          }
          None => {
            // Block current complete assignment to continue or finish
            if self.decision_level() == 0 {
              search_active = false
              break
            }
            let block_lits : Array[Int] = []
            for lit in self.trail {
              block_lits.push(lit_neg(lit))
            }
            self.backjump(0)
            let _ = self.add_clause(
              block_lits,
              true,
              LrbOptimalLemma((obj * 100.0).to_int()),
            )
          }
        }
      }
    }
  }

  // Final Homomorphic Conservation Ideal verification on the optimal model (if SAT)
  let sat = self.opt_lemma_engine.has_incumbent
  let orig_clauses : Array[Clause] = []
  for c in self.clauses {
    if !c.learnt {
      orig_clauses.push(c)
    }
  }
  let conserved = if sat {
    self.conservation_ideal.verify_all_clauses_conserved(
      orig_clauses,
      self.opt_lemma_engine.best_assignment,
    )
  } else {
    true
  }

  // Count distinct EUF congruence classes
  let mut euf_classes = 0
  for i = 0; i < self.hpa.terms.length(); i = i + 1 {
    if self.hpa.find(i) == i {
      euf_classes = euf_classes + 1
    }
  }

  {
    satisfiable: sat,
    optimal_objective: if sat {
      self.opt_lemma_engine.best_objective
    } else {
      arith_infinity
    },
    best_bool_model: self.opt_lemma_engine.best_assignment.copy(),
    best_arith_model: self.opt_lemma_engine.best_arith_assignment.copy(),
    total_conflicts: self.lrb.total_conflicts,
    total_decisions: self.total_decisions,
    total_propagations: self.total_propagations,
    hybrid6_final_lb: self.hybrid6.fused_lower_bound,
    qap_pruned_branches: self.qap.pruned_branches,
    euf_congruence_classes: euf_classes,
    bbf_snapshots_taken: self.bbf.total_snapshots_taken,
    bbf_restorations: self.bbf.total_restorations,
    cac_ideal_reductions: self.cac.ideal_reductions_count,
    conservation_ideal_verified: conserved,
    surjective_axiom_certified_clauses: self.axiom_projector.certified_clause_count(),
    axiom_certification_failures: self.axiom_certification_failures,
    axiom_schema_coverage: self.axiom_projector.schema_coverage_report(),
  }
}
