///|
/// Core Algebraic, Logical, and Category-Theoretic Types for the
/// Self-Developed OMT + GNN + CDCL(T) + Lazy SMT Solver.

///|
/// Truth value in three-valued CDCL(T) Boolean abstraction.
pub(all) enum TruthVal {
  True
  False
  Unassigned
} derive(Eq, Debug)

///|
pub extend TruthVal with Eq::{equal, not_equal}

///|
#deprecated("Use `Debug::to_repr` instead", skip_current_package=true)
#doc(hidden)
pub extend TruthVal with @debug.Debug::{to_repr}

///|
/// Arithmetic comparison operators for LRA / LIA / Polynomial constraints.
pub(all) enum ArithOp {
  Le
  Ge
  Eq
  Lt
  Gt
} derive(Eq)

///|
pub extend ArithOp with Eq::{equal, not_equal}

///|
/// Axiom origin tag certifying the CDCL(T) Clause Surjective Axiom Invariant.
/// Every clause in the solver is surjectively traced back to either a problem
/// constraint or a specific theory/resolution axiom schema.
pub(all) enum AxiomOrigin {
  ProblemInput
  UipResolution(Int, Int) // (num_resolvents, decision_level)
  EufCongruenceAxiom(Int, Int) // (term_lhs, term_rhs)
  KleisliUnificationAxiom(Int) // (unification_step_id)
  LraFarkasAxiom(Int) // (farkas_certificate_id)
  LiaIntegralityCut(Int) // (arith_var_id)
  QapDiscretePruneAxiom(Int) // (qap_node_level)
  CacIdealReductionAxiom(Int) // (cad_cell_level)
  LrbOptimalLemma(Int) // (scaled_bound_int)
} derive(Eq)

///|
pub extend AxiomOrigin with Eq::{equal, not_equal}

///|
/// Construct a signed DIMACS-style literal from variable ID (1-based) and polarity.
pub fn mk_lit(var_id : Int, positive : Bool) -> Int {
  if positive {
    var_id
  } else {
    -var_id
  }
}

///|
/// Extract 1-based variable ID from a signed literal.
pub fn lit_var(lit : Int) -> Int {
  if lit >= 0 {
    lit
  } else {
    -lit
  }
}

///|
/// Return true if the literal has positive polarity.
pub fn lit_sign(lit : Int) -> Bool {
  lit > 0
}

///|
/// Negate a signed literal.
pub fn lit_neg(lit : Int) -> Int {
  -lit
}

///|
/// CNF Clause with LBD (Literal Block Distance), activity, axiom origin,
/// and homomorphic conservation invariant hash.
pub(all) struct Clause {
  id : Int
  lits : Array[Int]
  mut activity : Double
  mut lbd : Int
  learnt : Bool
  origin : AxiomOrigin
  conservation_hash : Int
}

///|
/// Compute an algebraic conservation hash for a clause under Boolean ring
/// Z_p[x_1..x_n] / <x_i^2 - x_i> to track Homomorphic Conservation Ideal membership.
pub fn compute_clause_conservation_hash(lits : Array[Int]) -> Int {
  // Sort-invariant symmetric polynomial hash over literals
  let mut sum_acc = 1000003
  let mut xor_acc = 0x5A5A5A5A
  let mut prod_acc = 1
  for lit in lits {
    let v = lit_var(lit)
    let encoded = if lit > 0 { v * 257 + 13 } else { v * 257 + 131 }
    sum_acc = (sum_acc + encoded * encoded) % 1000000007
    xor_acc = xor_acc ^ (encoded * 0x45D9F3B)
    prod_acc = prod_acc * (encoded % 997 + 3) % 1000000007
  }
  (sum_acc ^ xor_acc ^ prod_acc) & 0x7FFFFFFF
}

///|
/// Create a new certified Clause.
pub fn Clause::new(
  id : Int,
  lits : Array[Int],
  learnt : Bool,
  lbd : Int,
  origin : AxiomOrigin,
) -> Clause {
  {
    id,
    lits,
    activity: 1.0,
    lbd,
    learnt,
    origin,
    conservation_hash: compute_clause_conservation_hash(lits),
  }
}

///|
/// EUF & Kleisli Term DAG node.
pub(all) enum Term {
  Var(String, Int) // (symbol_name, variable_id)
  IntConst(Int)
  RealConst(Double)
  App(String, Array[Int]) // (uninterpreted_func_name, arg_term_ids)
} derive(Eq)

///|
pub extend Term with Eq::{equal, not_equal}

///|
/// Linear arithmetic expression: sum_i coeff_i * x_{var_i} + constant.
pub(all) struct LinearTerm {
  coeffs : Array[(Int, Double)]
  constant : Double
}

///|
/// Evaluate a LinearTerm given variable assignments.
pub fn LinearTerm::eval(
  self : LinearTerm,
  assignment : Array[Double],
) -> Double {
  let mut acc = self.constant
  for pair in self.coeffs {
    let (v, c) = pair
    if v >= 0 && v < assignment.length() {
      acc = acc + c * assignment[v]
    }
  }
  acc
}

///|
/// Theory Atom linking Boolean abstraction variables to EUF, LRA, LIA, and CAC theories.
pub(all) enum TheoryAtom {
  EufEq(Int, Int) // term_id_1 == term_id_2
  EufNeq(Int, Int) // term_id_1 != term_id_2
  LraConstraint(LinearTerm, ArithOp, Double) // linear real constraint
  LiaConstraint(LinearTerm, ArithOp, Int) // linear integer constraint
  PolyConstraint(Int, ArithOp, Double) // polynomial index in CAC ring
}

///|
/// Outer Monoid Element (M_outer, (+), e_outer) for Boolean partial assignments
/// in the Inner-Outer Semigroup Dual-Layer CDN.
pub(all) struct OuterMonoidElem {
  num_vars : Int
  values : Array[TruthVal] // 1-indexed (size = num_vars + 1)
  has_conflict : Bool
  conflict_var : Int
}

///|
/// Identity element e_outer of the Outer Monoid.
pub fn OuterMonoidElem::identity(num_vars : Int) -> OuterMonoidElem {
  let values = Array::make(num_vars + 1, Unassigned)
  { num_vars, values, has_conflict: false, conflict_var: 0, }
}

///|
/// Monoid composition (a (+) b) in M_outer.
/// Satisfies associativity and identity; conflicting assignments map to the absorbing conflict state.
pub fn outer_monoid_compose(
  a : OuterMonoidElem,
  b : OuterMonoidElem,
) -> OuterMonoidElem {
  let n = if a.num_vars > b.num_vars { a.num_vars } else { b.num_vars }
  if a.has_conflict {
    return a
  }
  if b.has_conflict {
    return b
  }
  let merged = Array::make(n + 1, Unassigned)
  let mut conflict = false
  let mut cvar = 0
  for i = 1; i <= n; i = i + 1 {
    let va = if i < a.values.length() { a.values[i] } else { Unassigned }
    let vb = if i < b.values.length() { b.values[i] } else { Unassigned }
    match (va, vb) {
      (Unassigned, x) => merged[i] = x
      (x, Unassigned) => merged[i] = x
      (True, True) => merged[i] = True
      (False, False) => merged[i] = False
      _ => {
        conflict = true
        cvar = i
      }
    }
  }
  { num_vars: n, values: merged, has_conflict: conflict, conflict_var: cvar, }
}

///|
/// Inner Semigroup Element (S_inner, (x)) representing theory interval bounds,
/// EUF equivalence class merges, and QAP objective lower bound contribution.
pub(all) struct InnerSemigroupElem {
  num_arith_vars : Int
  lower_bounds : Array[Double]
  upper_bounds : Array[Double]
  euf_merges : Array[(Int, Int)]
  qap_lower_bound : Double
  infeasible : Bool
}

///|
/// Neutral element of Inner Semigroup S_inner.
pub fn InnerSemigroupElem::neutral(num_arith_vars : Int) -> InnerSemigroupElem {
  let lb = Array::make(num_arith_vars, -1.0e12)
  let ub = Array::make(num_arith_vars, 1.0e12)
  {
    num_arith_vars,
    lower_bounds: lb,
    upper_bounds: ub,
    euf_merges: [],
    qap_lower_bound: 0.0,
    infeasible: false,
  }
}

///|
/// Semigroup composition (s1 (x) s2) in S_inner:
/// Intersects arithmetic interval bounds, concatenates EUF merges, and aggregates QAP lower bounds.
pub fn inner_semigroup_compose(
  s1 : InnerSemigroupElem,
  s2 : InnerSemigroupElem,
) -> InnerSemigroupElem {
  let n = if s1.num_arith_vars > s2.num_arith_vars {
    s1.num_arith_vars
  } else {
    s2.num_arith_vars
  }
  let lb = Array::make(n, -1.0e12)
  let ub = Array::make(n, 1.0e12)
  let mut infeas = s1.infeasible || s2.infeasible
  for i = 0; i < n; i = i + 1 {
    let l1 = if i < s1.lower_bounds.length() {
      s1.lower_bounds[i]
    } else {
      -1.0e12
    }
    let l2 = if i < s2.lower_bounds.length() {
      s2.lower_bounds[i]
    } else {
      -1.0e12
    }
    let u1 = if i < s1.upper_bounds.length() {
      s1.upper_bounds[i]
    } else {
      1.0e12
    }
    let u2 = if i < s2.upper_bounds.length() {
      s2.upper_bounds[i]
    } else {
      1.0e12
    }
    lb[i] = l1.max(l2)
    ub[i] = u1.min(u2)
    if lb[i] > ub[i] + 1.0e-9 {
      infeas = true
    }
  }
  let merges : Array[(Int, Int)] = []
  for m in s1.euf_merges {
    merges.push(m)
  }
  for m in s2.euf_merges {
    merges.push(m)
  }
  let qap_lb = s1.qap_lower_bound.max(s2.qap_lower_bound)
  {
    num_arith_vars: n,
    lower_bounds: lb,
    upper_bounds: ub,
    euf_merges: merges,
    qap_lower_bound: qap_lb,
    infeasible: infeas,
  }
}

///|
/// Dual-Layer CDN (Conflict-Driven / Constraint-Dependency Network)
/// decoupling Outer Monoid Boolean assignments to Inner Semigroup theory states
/// and generating QAP assignment CNF clauses.
pub(all) struct DualLayerCDN {
  num_bool_vars : Int
  num_arith_vars : Int
  // Maps (bool_var, polarity_is_pos) -> (arith_var, is_lower_bound, bound_val, qap_cost_delta)
  var_theory_effects : Array[(Int, Bool, Int, Bool, Double, Double)]
  euf_var_effects : Array[(Int, Bool, Int, Int)]
}

///|
/// Construct a DualLayerCDN instance.
pub fn DualLayerCDN::new(
  num_bool_vars : Int,
  num_arith_vars : Int,
) -> DualLayerCDN {
  {
    num_bool_vars,
    num_arith_vars,
    var_theory_effects: [],
    euf_var_effects: [],
  }
}

///|
/// Register a decoupled CDN mapping rule from a Boolean literal to an arithmetic bound & QAP cost delta.
pub fn DualLayerCDN::register_arith_mapping(
  self : DualLayerCDN,
  bool_var : Int,
  positive : Bool,
  arith_var : Int,
  is_lower : Bool,
  bound_val : Double,
  qap_delta : Double,
) -> Unit {
  self.var_theory_effects.push(
    (bool_var, positive, arith_var, is_lower, bound_val, qap_delta),
  )
}

///|
/// Register a decoupled CDN mapping rule from a Boolean literal to an EUF equality merge.
pub fn DualLayerCDN::register_euf_mapping(
  self : DualLayerCDN,
  bool_var : Int,
  positive : Bool,
  t1 : Int,
  t2 : Int,
) -> Unit {
  self.euf_var_effects.push((bool_var, positive, t1, t2))
}

///|
/// Homomorphic mapping Phi_CDN : M_outer -> S_inner.
/// Satisfies Phi(a (+) b) == Phi(a) (x) Phi(b) on conflict-free states.
pub fn DualLayerCDN::map_outer_to_inner(
  self : DualLayerCDN,
  outer : OuterMonoidElem,
) -> InnerSemigroupElem {
  let inner = InnerSemigroupElem::neutral(self.num_arith_vars)
  if outer.has_conflict {
    return { ..inner, infeasible: true, }
  }
  let mut max_qap_lb = 0.0
  let mut infeas = false
  for rule in self.var_theory_effects {
    let (bvar, pos, avar, is_lb, bval, qdelta) = rule
    if bvar > 0 && bvar < outer.values.length() {
      let active = match (outer.values[bvar], pos) {
        (True, true) => true
        (False, false) => true
        _ => false
      }
      if active && avar >= 0 && avar < self.num_arith_vars {
        if is_lb {
          inner.lower_bounds[avar] = inner.lower_bounds[avar].max(bval)
        } else {
          inner.upper_bounds[avar] = inner.upper_bounds[avar].min(bval)
        }
        if inner.lower_bounds[avar] > inner.upper_bounds[avar] + 1.0e-9 {
          infeas = true
        }
        if qdelta > max_qap_lb {
          max_qap_lb = qdelta
        }
      }
    }
  }
  for erule in self.euf_var_effects {
    let (bvar, pos, t1, t2) = erule
    if bvar > 0 && bvar < outer.values.length() {
      let active = match (outer.values[bvar], pos) {
        (True, true) => true
        (False, false) => true
        _ => false
      }
      if active {
        inner.euf_merges.push((t1, t2))
      }
    }
  }
  { ..inner, qap_lower_bound: max_qap_lb, infeasible: infeas, }
}

///|
/// Generate decoupled QAP Assignment CNF clauses for an N x N facility-location assignment problem.
/// Variable x_{i,k} (0 <= i < n, 0 <= k < n) is mapped to Boolean variable `base_var + i * n + k`.
/// Enforces:
/// 1. Row At-Least-One (each facility i assigned to >= 1 location k)
/// 2. Row At-Most-One (each facility i assigned to <= 1 location k)
/// 3. Column At-Least-One (each location k receives >= 1 facility i)
/// 4. Column At-Most-One (each location k receives <= 1 facility i)
pub fn generate_qap_assignment_cnf(
  n : Int,
  base_var : Int,
  start_clause_id : Int,
) -> Array[Clause] {
  let clauses : Array[Clause] = []
  let mut cid = start_clause_id
  let var_at = fn(i : Int, k : Int) -> Int { base_var + i * n + k }

  // 1. Row ALO & 2. Row AMO
  for i = 0; i < n; i = i + 1 {
    let row_alo : Array[Int] = []
    for k = 0; k < n; k = k + 1 {
      row_alo.push(mk_lit(var_at(i, k), true))
      for k2 = k + 1; k2 < n; k2 = k2 + 1 {
        let amo : Array[Int] = [
          mk_lit(var_at(i, k), false),
          mk_lit(var_at(i, k2), false),
        ]
        clauses.push(Clause::new(cid, amo, false, 2, ProblemInput))
        cid = cid + 1
      }
    }
    clauses.push(Clause::new(cid, row_alo, false, n, ProblemInput))
    cid = cid + 1
  }

  // 3. Column ALO & 4. Column AMO
  for k = 0; k < n; k = k + 1 {
    let col_alo : Array[Int] = []
    for i = 0; i < n; i = i + 1 {
      col_alo.push(mk_lit(var_at(i, k), true))
      for i2 = i + 1; i2 < n; i2 = i2 + 1 {
        let amo : Array[Int] = [
          mk_lit(var_at(i, k), false),
          mk_lit(var_at(i2, k), false),
        ]
        clauses.push(Clause::new(cid, amo, false, 2, ProblemInput))
        cid = cid + 1
      }
    }
    clauses.push(Clause::new(cid, col_alo, false, n, ProblemInput))
    cid = cid + 1
  }
  clauses
}
