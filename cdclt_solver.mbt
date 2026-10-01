///|
/// A small, self-contained CDCL(T) solver for the SMT-LIB front-end.
///
/// This is the "plain" solver next to the OMT engine: it takes a parsed
/// `SmtProblem`, Tseitin-encodes the Boolean structure, hands every linear arithmetic
/// atom to the LRA/LIA theory solver, and runs a standard CDCL loop (VSIDS branching,
/// 1-UIP learning through the shared analysis in `conflict_graph.mbt`, theory checks after
/// propagation and after every decision). It does not optimise; it answers `check-sat`.
///
/// The implication graph is recorded during the search and exported as an SVG diagram.

///|
/// Linear arithmetic atom handed to the theory solver: under `guard` the relation
/// `term op rhs` must hold.
pub(all) struct SmtAtom {
  guard : Int
  term : LinearTerm
  op : ArithOp
  rhs : Double
  /// True when every variable of the term is declared `Int`.
  is_lia : Bool
}

///|
/// The logical complement of an arithmetic relation (used to encode `not` exactly).
fn negate_arith_op(op : ArithOp) -> ArithOp {
  match op {
    Le => Gt
    Lt => Ge
    Ge => Lt
    Gt => Le
    Eq => Eq
  }
}

fn smt_zero_term() -> LinearTerm {
  { coeffs: [], constant: 0.0 }
}

fn smt_add_terms(a : LinearTerm, b : LinearTerm) -> LinearTerm {
  let coeffs : Array[(Int, Double)] = []
  for pair in a.coeffs {
    coeffs.push(pair)
  }
  for pair in b.coeffs {
    coeffs.push(pair)
  }
  { coeffs, constant: a.constant + b.constant }
}

fn smt_scale_term(t : LinearTerm, k : Double) -> LinearTerm {
  let coeffs : Array[(Int, Double)] = []
  for pair in t.coeffs {
    let (v, c) = pair
    coeffs.push((v, c * k))
  }
  { coeffs, constant: t.constant * k }
}

fn smt_sub_terms(a : LinearTerm, b : LinearTerm) -> LinearTerm {
  smt_add_terms(a, smt_scale_term(b, -1.0))
}

///|
/// Combine repeated variable coefficients and drop those that vanish, so the bound
/// propagation sees each variable exactly once per constraint.
fn smt_merge_term(t : LinearTerm) -> LinearTerm {
  let vars : Array[Int] = []
  let acc : Array[Double] = []
  for pair in t.coeffs {
    let (v, c) = pair
    let mut idx = -1
    for i = 0; i < vars.length(); i = i + 1 {
      if vars[i] == v {
        idx = i
      }
    }
    if idx < 0 {
      vars.push(v)
      acc.push(c)
    } else {
      acc[idx] = acc[idx] + c
    }
  }
  let out : Array[(Int, Double)] = []
  for i = 0; i < vars.length(); i = i + 1 {
    if acc[i].abs() > tol_eps {
      out.push((vars[i], acc[i]))
    }
  }
  { coeffs: out, constant: t.constant }
}

///|
/// Tseitin encoder: turns parsed expressions into CNF clauses over Boolean variables and
/// theory atoms over arithmetic variables.
struct TseitinEncoder {
  problem : SmtProblem
  clauses : Array[Array[Int]]
  atoms : Array[SmtAtom]
  mut next_var : Int
  mut true_lit : Int
  mut false_lit : Int
  errors : Array[String]
}

fn TseitinEncoder::new(problem : SmtProblem) -> TseitinEncoder {
  {
    problem,
    clauses: [],
    atoms: [],
    next_var: problem.num_bool_vars + 1,
    true_lit: 0,
    false_lit: 0,
    errors: [],
  }
}

fn TseitinEncoder::fresh(self : TseitinEncoder) -> Int {
  let v = self.next_var
  self.next_var = self.next_var + 1
  v
}

fn TseitinEncoder::lit_true(self : TseitinEncoder) -> Int {
  if self.true_lit == 0 {
    self.true_lit = self.fresh()
    self.clauses.push([self.true_lit])
  }
  self.true_lit
}

fn TseitinEncoder::lit_false(self : TseitinEncoder) -> Int {
  if self.false_lit == 0 {
    self.false_lit = self.fresh()
    self.clauses.push([lit_neg(self.false_lit)])
  }
  self.false_lit
}

fn TseitinEncoder::tseitin_and(self : TseitinEncoder, lits : Array[Int]) -> Int {
  let a = self.fresh()
  if lits.length() == 0 {
    // Empty conjunction is true
    self.clauses.push([a])
    return a
  }
  for l in lits {
    self.clauses.push([lit_neg(a), l])
  }
  let big : Array[Int] = [a]
  for l in lits {
    big.push(lit_neg(l))
  }
  self.clauses.push(big)
  a
}

fn TseitinEncoder::tseitin_or(self : TseitinEncoder, lits : Array[Int]) -> Int {
  let a = self.fresh()
  if lits.length() == 0 {
    self.clauses.push([lit_neg(a)])
    return a
  }
  for l in lits {
    self.clauses.push([a, lit_neg(l)])
  }
  let big : Array[Int] = [lit_neg(a)]
  for l in lits {
    big.push(l)
  }
  self.clauses.push(big)
  a
}

fn TseitinEncoder::is_lia_term(self : TseitinEncoder, t : LinearTerm) -> Bool {
  for pair in t.coeffs {
    let (v, _c) = pair
    if v < 0 || v >= self.problem.num_arith_vars || !self.problem.is_integer[v] {
      return false
    }
  }
  true
}

///|
/// Linearise an arithmetic expression into a `LinearTerm`. Multiplication is accepted only
/// with one constant operand; anything else is a hard error (this front-end models linear
/// arithmetic only).
fn TseitinEncoder::linearize(self : TseitinEncoder, e : SmtExpr) -> LinearTerm? {
  match e {
    SmtNumLit(d) => Some({ coeffs: [], constant: d })
    SmtBoolLit(_) => {
      self.errors.push("Boolean literal used inside an arithmetic term")
      None
    }
    SmtSymRef(i) => {
      let d = self.problem.decls[i]
      if d.arith_index >= 0 {
        Some({ coeffs: [(d.arith_index, 1.0)], constant: 0.0 })
      } else {
        self.errors.push("Boolean symbol \{d.name} used inside an arithmetic term")
        None
      }
    }
    SmtApply(op, args) => {
      if op == "+" {
        let mut acc = smt_zero_term()
        for a in args {
          match self.linearize(a) {
            Some(t) => acc = smt_add_terms(acc, t)
            None => return None
          }
        }
        Some(smt_merge_term(acc))
      } else if op == "-" {
        if args.length() == 1 {
          match self.linearize(args[0]) {
            Some(t) => Some(smt_scale_term(t, -1.0))
            None => None
          }
        } else if args.length() == 2 {
          match (self.linearize(args[0]), self.linearize(args[1])) {
            (Some(a), Some(b)) => Some(smt_merge_term(smt_sub_terms(a, b)))
            _ => None
          }
        } else {
          self.errors.push("unsupported arity for -")
          None
        }
      } else if op == "*" {
        if args.length() != 2 {
          self.errors.push("unsupported arity for *")
          return None
        }
        let mut const_factor = 0.0
        let mut other : SmtExpr? = None
        for i = 0; i < 2; i = i + 1 {
          match args[i] {
            SmtNumLit(d) => const_factor = d
            _ => other = Some(args[i])
          }
        }
        match other {
          Some(oe) =>
            match self.linearize(oe) {
              Some(t) => Some(smt_scale_term(t, const_factor))
              None => None
            }
          None => {
            self.errors.push("non-linear multiplication (both operands are expressions)")
            None
          }
        }
      } else {
        self.errors.push("unsupported arithmetic operator \{op}")
        None
      }
    }
  }
}

///|
/// Allocate a literal for `term op rhs` and register *both* directions with the theory
/// solver, so the negation of the returned literal is always meaningful: the literal is
/// true exactly when the relation holds.
fn TseitinEncoder::atom_lit(
  self : TseitinEncoder,
  term : LinearTerm,
  op : ArithOp,
  rhs : Double,
) -> Int {
  let g = self.fresh()
  let lia = self.is_lia_term(term)
  self.atoms.push({ guard: g, term, op, rhs, is_lia: lia })
  if op != Eq {
    self.atoms.push({
      guard: lit_neg(g),
      term,
      op: negate_arith_op(op),
      rhs,
      is_lia: lia,
    })
  }
  g
}

///|
/// Allocate a literal `g` with `g ↔ term = rhs`. The negative direction `¬g → term ≠ rhs`
/// is encoded by a case split (`h_lo`, `h_hi`) whose literals guard the strict inequalities,
/// with `g ∨ h_lo ∨ h_hi`, `¬g ∨ ¬h_lo`, `¬g ∨ ¬h_hi` tying the split to `g`.
fn TseitinEncoder::atom_eq_lit(
  self : TseitinEncoder,
  term : LinearTerm,
  rhs : Double,
) -> Int {
  let g = self.fresh()
  let lia = self.is_lia_term(term)
  self.atoms.push({ guard: g, term, op: Le, rhs, is_lia: lia })
  self.atoms.push({ guard: g, term, op: Ge, rhs, is_lia: lia })
  let h_lo = self.fresh()
  let h_hi = self.fresh()
  self.clauses.push([g, h_lo, h_hi])
  self.clauses.push([lit_neg(g), lit_neg(h_lo)])
  self.clauses.push([lit_neg(g), lit_neg(h_hi)])
  if lia {
    self.atoms.push({
      guard: h_lo,
      term,
      op: Le,
      rhs: rhs - 1.0,
      is_lia: true,
    })
    self.atoms.push({
      guard: h_hi,
      term,
      op: Ge,
      rhs: rhs + 1.0,
      is_lia: true,
    })
  } else {
    self.atoms.push({ guard: h_lo, term, op: Lt, rhs, is_lia: false })
    self.atoms.push({ guard: h_hi, term, op: Gt, rhs, is_lia: false })
  }
  g
}

///|
/// Whether the expression is Boolean-sorted (used to route `=` to the Boolean or the
/// arithmetic encoding).
fn TseitinEncoder::expr_is_boolean(self : TseitinEncoder, e : SmtExpr) -> Bool {
  match e {
    SmtBoolLit(_) => true
    SmtNumLit(_) => false
    SmtSymRef(i) => self.problem.decls[i].bool_var > 0
    SmtApply(op, _) =>
      op == "and" ||
      op == "or" ||
      op == "not" ||
      op == "=>" ||
      op == "=" ||
      op == "<" ||
      op == "<=" ||
      op == ">" ||
      op == ">="
  }
}

///|
/// Lower an expression to a literal with the requested polarity. The returned literal is a
/// genuine Boolean variable whose theory constraints make it equivalent to the expression,
/// so negating it is always sound.
fn TseitinEncoder::lower(
  self : TseitinEncoder,
  e : SmtExpr,
  positive : Bool,
) -> Int {
  match e {
    SmtBoolLit(b) => if b == positive { self.lit_true() } else { self.lit_false() }
    SmtNumLit(_) => {
      self.errors.push("numeric literal used as a Boolean formula")
      self.lit_false()
    }
    SmtSymRef(i) => {
      let d = self.problem.decls[i]
      if d.bool_var > 0 {
        mk_lit(d.bool_var, positive)
      } else {
        self.errors.push("arithmetic symbol \{d.name} used as a Boolean formula")
        self.lit_false()
      }
    }
    SmtApply(op, args) => self.lower_apply(op, args, positive)
  }
}

fn TseitinEncoder::lower_apply(
  self : TseitinEncoder,
  op : String,
  args : Array[SmtExpr],
  positive : Bool,
) -> Int {
  if op == "not" {
    if args.length() != 1 {
      self.errors.push("not expects one argument")
      return self.lit_false()
    }
    return self.lower(args[0], !positive)
  }
  if op == "and" || op == "or" {
    // Children keep the requested polarity; the connective is the dual one when a negative
    // polarity is requested (¬(a ∧ b) = ¬a ∨ ¬b and ¬(a ∨ b) = ¬a ∧ ¬b).
    let lits : Array[Int] = []
    for a in args {
      lits.push(self.lower(a, positive))
    }
    let use_and = if op == "and" { positive } else { !positive }
    if use_and {
      self.tseitin_and(lits)
    } else {
      self.tseitin_or(lits)
    }
  } else if op == "=>" {
    if args.length() != 2 {
      self.errors.push("=> expects two arguments")
      return self.lit_false()
    }
    if positive {
      self.tseitin_or([
        self.lower(args[0], false),
        self.lower(args[1], true),
      ])
    } else {
      self.tseitin_and([
        self.lower(args[0], true),
        self.lower(args[1], false),
      ])
    }
  } else if op == "=" {
    if args.length() < 2 {
      self.errors.push("= expects at least two arguments")
      return self.lit_false()
    }
    if self.expr_is_boolean(args[0]) {
      if args.length() != 2 {
        self.errors.push("Boolean = with more than two arguments is not supported")
        return self.lit_false()
      }
      let a_pos = self.lower(args[0], true)
      let b_pos = self.lower(args[1], true)
      let a_neg = self.lower(args[0], false)
      let b_neg = self.lower(args[1], false)
      if positive {
        self.tseitin_or([
          self.tseitin_and([a_pos, b_pos]),
          self.tseitin_and([a_neg, b_neg]),
        ])
      } else {
        self.tseitin_or([
          self.tseitin_and([a_pos, b_neg]),
          self.tseitin_and([a_neg, b_pos]),
        ])
      }
    } else {
      let conjs : Array[Int] = []
      for i = 0; i + 1 < args.length(); i = i + 1 {
        match (self.linearize(args[i]), self.linearize(args[i + 1])) {
          (Some(l), Some(r)) => {
            let term = smt_merge_term(smt_sub_terms(l, r))
            let g = self.atom_eq_lit(term, 0.0)
            conjs.push(if positive { g } else { lit_neg(g) })
          }
          _ => ()
        }
      }
      if conjs.length() == 0 {
        self.errors.push("could not linearise an equality")
        self.lit_false()
      } else if positive {
        self.tseitin_and(conjs)
      } else {
        self.tseitin_or(conjs)
      }
    }
  } else if op == "<" || op == "<=" || op == ">" || op == ">=" {
    if args.length() < 2 {
      self.errors.push("\{op} expects at least two arguments")
      return self.lit_false()
    }
    let atom_op = if op == "<" {
      Lt
    } else if op == "<=" {
      Le
    } else if op == ">" {
      Gt
    } else {
      Ge
    }
    let conjs : Array[Int] = []
    for i = 0; i + 1 < args.length(); i = i + 1 {
      match (self.linearize(args[i]), self.linearize(args[i + 1])) {
        (Some(l), Some(r)) => {
          let term = smt_merge_term(smt_sub_terms(l, r))
          let use_op = if positive { atom_op } else { negate_arith_op(atom_op) }
          conjs.push(self.atom_lit(term, use_op, 0.0))
        }
        _ => ()
      }
    }
    if conjs.length() == 0 {
      self.errors.push("could not linearise a comparison")
      self.lit_false()
    } else if positive {
      self.tseitin_and(conjs)
    } else {
      // ¬(c1 ∧ c2 ∧ ...) = ¬c1 ∨ ¬c2 ∨ ...
      let negs : Array[Int] = []
      for c in conjs {
        negs.push(lit_neg(c))
      }
      self.tseitin_or(negs)
    }
  } else {
    self.errors.push("unsupported operator \{op}")
    self.lit_false()
  }
}

///|
/// Encode every assertion as a unit clause over its lowered literal.
fn TseitinEncoder::encode_all(self : TseitinEncoder) -> Unit {
  for e in self.problem.assertions {
    let lit = self.lower(e, true)
    self.clauses.push([lit])
  }
}

///|
/// Result of a `check-sat` call, including the search telemetry and the conflict-graph
/// rendering.
pub(all) struct CdcltResult {
  satisfiable : Bool
  /// True when the search stopped without a verdict (conflict budget / witness search).
  unknown : Bool
  model : Array[TruthVal]
  arith_model : Array[Double]
  conflicts : Int
  decisions : Int
  propagations : Int
  input_clauses : Int
  learnt_clauses : Int
  theory_conflicts : Int
  graph_nodes : Int
  graph_violations : Int
  learnt_clause_failures : Int
  /// Learnt clauses whose recomputed LBD disagreed with the analysis value (must stay 0).
  lbd_certification_failures : Int
  uncertified_models : Int
  model_text : String
  graph_svg : String
}

///|
/// A CDCL(T) satisfiability solver over parsed SMT-LIB problems.
pub(all) struct CdcltSolver {
  problem : SmtProblem
  num_vars : Int
  clauses : Array[Clause]
  values : Array[TruthVal] // 1-indexed
  trail : Array[Int]
  trail_lim : Array[Int]
  var_level : Array[Int]
  var_reason : Array[Int]
  vsids : VsidsOracle
  graph : ImplicationGraph
  theory : LraLiaTheorySolver
  projector : SurjectiveAxiomProjector
  conservation : HomomorphicConservationIdeal
  mut conflicts : Int
  mut decisions : Int
  mut propagations : Int
  mut theory_conflicts : Int
  mut uncertified_models : Int
  mut learnt_invariant_failures : Int
  mut lbd_certification_failures : Int
  mut axiom_certification_failures : Int
  mut budget_exhausted : Bool
  mut unknown : Bool
  mut found_model : Bool
}

///|
/// Build a solver from a parsed problem: Tseitin-encode, create the clause database
/// (certifying every clause origin) and register every theory atom with the LRA/LIA solver.
pub fn CdcltSolver::from_problem(problem : SmtProblem) -> CdcltSolver {
  let enc = TseitinEncoder::new(problem)
  enc.encode_all()
  let num_vars = enc.next_var - 1
  let solver : CdcltSolver = {
    problem,
    num_vars,
    clauses: [],
    values: Array::make(num_vars + 1, Unassigned),
    trail: [],
    trail_lim: [],
    var_level: Array::make(num_vars + 1, 0),
    var_reason: Array::make(num_vars + 1, -1),
    vsids: VsidsOracle::new(num_vars),
    graph: ImplicationGraph::new(num_vars),
    theory: LraLiaTheorySolver::new(
      problem.num_arith_vars,
      problem.is_integer.copy(),
    ),
    projector: SurjectiveAxiomProjector::new(),
    conservation: HomomorphicConservationIdeal::new(num_vars),
    conflicts: 0,
    decisions: 0,
    propagations: 0,
    theory_conflicts: 0,
    uncertified_models: 0,
    learnt_invariant_failures: 0,
    lbd_certification_failures: 0,
    axiom_certification_failures: 0,
    budget_exhausted: false,
    unknown: false,
    found_model: false,
  }
  for lits in enc.clauses {
    let _ = solver.add_clause_checked(lits, false, ProblemInput)
  }
  for atom in enc.atoms {
    solver.theory.add_constraint(
      atom.guard,
      atom.term,
      atom.op,
      atom.rhs,
      atom.is_lia,
    )
  }
  solver
}

///|
/// Add a clause, certifying its origin in the surjective axiom projector.
pub fn CdcltSolver::add_clause_checked(
  self : CdcltSolver,
  lits : Array[Int],
  learnt : Bool,
  origin : AxiomOrigin,
) -> Int {
  let id = self.clauses.length()
  let c = Clause::new(id, lits, learnt, lits.length().max(1), origin)
  if !self.projector.certify_clause_origin(c) {
    self.axiom_certification_failures = self.axiom_certification_failures + 1
  }
  self.clauses.push(c)
  id
}

///|
/// Current decision level.
pub fn CdcltSolver::decision_level(self : CdcltSolver) -> Int {
  self.trail_lim.length()
}

///|
/// Assign `lit` at the current decision level and record it in the implication graph.
pub fn CdcltSolver::enqueue_lit(
  self : CdcltSolver,
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
      self.vsids.on_assign(v, pol)
      self.propagations = self.propagations + 1
      let level = self.decision_level()
      if reason_clause_idx < 0 || reason_clause_idx >= self.clauses.length() {
        let _ = self.graph.record_decision(lit, level)
      } else {
        let reason = self.clauses[reason_clause_idx]
        let antecedents : Array[Int] = []
        for rlit in reason.lits {
          if rlit != lit {
            // The clause literal is falsified; the assigned literal that falsifies it is
            // its negation, which is the node the implication edge starts from.
            antecedents.push(lit_neg(rlit))
          }
        }
        let _ = self.graph.record_implication(
          lit,
          level,
          reason_clause_idx,
          antecedents,
        )
      }
      true
    }
    True => pol
    False => !pol
  }
}

///|
/// Backjump to `target_level`, unassigning the trail above it.
pub fn CdcltSolver::backjump(self : CdcltSolver, target_level : Int) -> Unit {
  if target_level >= self.decision_level() {
    return
  }
  let target_trail_len = self.trail_lim[target_level]
  while self.trail.length() > target_trail_len {
    match self.trail.pop() {
      Some(lit) => {
        let v = lit_var(lit)
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
}

///|
/// Boolean constraint propagation to fixpoint; returns the falsified clause index or `None`.
pub fn CdcltSolver::bcp_propagate(self : CdcltSolver) -> Int? {
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
          changed = true
        }
      }
    }
  }
  None
}

///|
/// Run the arithmetic theory solver on the current Boolean assignment.
pub fn CdcltSolver::theory_check(self : CdcltSolver) -> Clause? {
  match self.theory.propagate_and_check(self.values, [], self.clauses.length()) {
    Some(c) => {
      self.theory_conflicts = self.theory_conflicts + 1
      Some(c)
    }
    None => None
  }
}

///|
/// Learn from a conflict. Returns `false` at decision level 0 (the formula is
/// unsatisfiable) or when the learnt clause cannot be justified.
pub fn CdcltSolver::handle_conflict(
  self : CdcltSolver,
  conflict_clause : Clause,
) -> Bool {
  if self.decision_level() == 0 {
    return false
  }
  self.conflicts = self.conflicts + 1
  let level = self.decision_level()
  let (learnt, bt_level, lbd, part_vars, _reason_vars) = analyze_conflict_1uip_from_trail(
    self.num_vars,
    level,
    self.trail,
    self.var_level,
    self.var_reason,
    self.clauses,
    conflict_clause.lits,
  )
  let _ = self.graph.verify()
  self.vsids.on_conflict(part_vars)
  if learnt.length() == 0 {
    return false
  }
  // Certify the LBD against the actual decision levels of the learnt literals.
  let certified_lbd = distinct_decision_levels(learnt, self.var_level)
  if certified_lbd != lbd {
    self.lbd_certification_failures = self.lbd_certification_failures + 1
  }
  let learnt_clause = Clause::new(
    self.clauses.length(),
    learnt,
    true,
    certified_lbd,
    UipResolution(part_vars.length(), level),
  )
  // The learnt clause must be justified both by the Boolean invariant and by the
  // implication graph; otherwise fall back to chronological backtracking.
  if !self.conservation.verify_learnt_clause_blocks(learnt_clause, self.values) ||
    !self.graph.all_lits_justified(learnt, self.values) {
    self.learnt_invariant_failures = self.learnt_invariant_failures + 1
    let parent_level = (level - 1).max(0)
    self.backjump(parent_level)
    if parent_level == 0 {
      return false
    }
    return true
  }
  self.backjump(bt_level)
  let cid = self.add_clause_checked(learnt, true, learnt_clause.origin)
  if learnt.length() == 1 {
    if !self.enqueue_lit(learnt[0], cid) {
      return false
    }
  } else {
    let _ = self.enqueue_lit(learnt[0], cid)
  }
  true
}

///|
/// Render the model as SMT-LIB `define-fun` lines.
pub fn CdcltSolver::model_text(self : CdcltSolver) -> String {
  let mut out = ""
  for d in self.problem.decls {
    if d.bool_var > 0 && d.bool_var < self.values.length() {
      let val = match self.values[d.bool_var] {
        True => "true"
        False => "false"
        Unassigned => "?"
      }
      out = out + "(define-fun \{d.name} () Bool \{val})\n"
    } else {
      let w = if d.arith_index >= 0 &&
        d.arith_index < self.theory.witness.length() {
        self.theory.witness[d.arith_index]
      } else {
        0.0
      }
      if d.sort == IntSort {
        out = out + "(define-fun \{d.name} () Int \{round_half_away(w).to_int()})\n"
      } else {
        out = out + "(define-fun \{d.name} () Real \{w})\n"
      }
    }
  }
  out
}

///|
/// Solve the problem with a conflict budget. The returned verdict is `satisfiable`,
/// `unsatisfiable`, or `unknown` (budget exhausted / no certified witness found).
pub fn CdcltSolver::solve(self : CdcltSolver, max_conflicts : Int) -> CdcltResult {
  self.graph.clear()
  let max_steps = max_conflicts * cdcl_step_budget_per_conflict +
    cdcl_step_budget_base
  let mut search_active = true
  let mut steps = 0
  while search_active && self.conflicts < max_conflicts && steps < max_steps {
    steps = steps + 1
    match self.bcp_propagate() {
      Some(conflict_cid) => {
        let conflict_clause = self.clauses[conflict_cid]
        let _ = self.graph.record_conflict(conflict_clause.lits)
        if !self.handle_conflict(conflict_clause) {
          search_active = false
          break
        }
        continue
      }
      None => ()
    }
    match self.theory_check() {
      Some(theory_conflict) => {
        let _ = self.graph.record_conflict(theory_conflict.lits)
        if !self.handle_conflict(theory_conflict) {
          search_active = false
          break
        }
        continue
      }
      None => ()
    }
    match self.vsids.select_branch_var(self.values) {
      Some(v) => {
        self.decisions = self.decisions + 1
        let phase = if self.vsids.is_phase_known(v) {
          self.vsids.saved_phase_of(v)
        } else {
          false
        }
        self.trail_lim.push(self.trail.length())
        let _ = self.enqueue_lit(mk_lit(v, phase), -1)
      }
      None => {
        // Every variable is assigned; accept the model only when the arithmetic witness is
        // certified against all active constraints.
        if self.theory.witness_certified {
          self.found_model = true
          search_active = false
          break
        }
        self.uncertified_models = self.uncertified_models + 1
        if self.decision_level() == 0 {
          // Nothing left to block; report "unknown" rather than claiming unsatisfiability.
          self.unknown = true
          search_active = false
          break
        }
        let block_lits : Array[Int] = []
        for lit in self.trail {
          block_lits.push(lit_neg(lit))
        }
        self.backjump(0)
        let _ = self.add_clause_checked(
          block_lits,
          true,
          LraFarkasAxiom(self.theory.farkas_conflicts),
        )
        continue
      }
    }
  }
  if !self.found_model && self.conflicts >= max_conflicts {
    self.budget_exhausted = true
    self.unknown = true
  }
  let mut learnt_count = 0
  for c in self.clauses {
    if c.learnt {
      learnt_count = learnt_count + 1
    }
  }
  {
    satisfiable: self.found_model,
    unknown: self.unknown && !self.found_model,
    model: self.values.copy(),
    arith_model: self.theory.witness.copy(),
    conflicts: self.conflicts,
    decisions: self.decisions,
    propagations: self.propagations,
    input_clauses: self.clauses.length() - learnt_count,
    learnt_clauses: learnt_count,
    theory_conflicts: self.theory_conflicts,
    graph_nodes: self.graph.nodes.length(),
    graph_violations: self.graph.violations,
    learnt_clause_failures: self.learnt_invariant_failures,
    lbd_certification_failures: self.lbd_certification_failures,
    uncertified_models: self.uncertified_models,
    model_text: self.model_text(),
    graph_svg: self.graph.to_svg(),
  }
}

///|
/// Convenience wrapper: parse SMT-LIB text and solve it. Returns `None` when the script
/// cannot be parsed.
pub fn solve_smtlib_text(text : String, max_conflicts : Int) -> CdcltResult? {
  match parse_smtlib(text) {
    Some(problem) => {
      let solver = CdcltSolver::from_problem(problem)
      Some(solver.solve(max_conflicts))
    }
    None => None
  }
}
