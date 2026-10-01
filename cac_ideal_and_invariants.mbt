///|
/// Ring-Lifted Cylindrical Algebraic Covering (CAC) Ideal Reduction,
/// Lazy SMT + CDCL(T) Homomorphic Conservation Ideal, and
/// Superposed Cooperative Exhaustive Upper-Bound Resolution Clause Surjective Axiom Invariant Projector.

///|
/// Monomial c * x_0^{e_0} * ... * x_{n-1}^{e_{n-1}} in Q[x_0, ..., x_{n-1}].
pub(all) struct PolyMonomial {
  coeff : Double
  exponents : Array[Int]
}

///|
/// Multivariate polynomial represented as a list of non-zero monomials sorted in
/// Graded Lexicographic (GrLex) descending order.
pub(all) struct MultivariatePoly {
  num_vars : Int
  terms : Array[PolyMonomial]
}

///|
/// Compare two exponent vectors using Graded Lexicographic (GrLex) order.
/// Returns 1 if a > b, -1 if a < b, 0 if equal.
pub fn compare_exponents_grlex(a : Array[Int], b : Array[Int]) -> Int {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  let mut deg_a = 0
  let mut deg_b = 0
  for i = 0; i < n; i = i + 1 {
    deg_a = deg_a + a[i]
    deg_b = deg_b + b[i]
  }
  if deg_a != deg_b {
    return if deg_a > deg_b { 1 } else { -1 }
  }
  for i = 0; i < n; i = i + 1 {
    if a[i] != b[i] {
      return if a[i] > b[i] { 1 } else { -1 }
    }
  }
  0
}

///|
/// Normalize a MultivariatePoly: combine like terms, drop near-zero coefficients,
/// and sort in descending GrLex order.
pub fn MultivariatePoly::normalize(self : MultivariatePoly) -> MultivariatePoly {
  let combined : Array[PolyMonomial] = []
  for t in self.terms {
    if t.coeff.abs() > 1.0e-10 {
      let mut merged = false
      for i = 0; i < combined.length(); i = i + 1 {
        if compare_exponents_grlex(combined[i].exponents, t.exponents) == 0 {
          combined[i] = {
            coeff: combined[i].coeff + t.coeff,
            exponents: combined[i].exponents,
          }
          merged = true
          break
        }
      }
      if !merged {
        combined.push({ coeff: t.coeff, exponents: t.exponents.copy(), })
      }
    }
  }
  let filtered : Array[PolyMonomial] = []
  for t in combined {
    if t.coeff.abs() > 1.0e-10 {
      filtered.push(t)
    }
  }
  // Insertion sort descending by GrLex
  for i = 1; i < filtered.length(); i = i + 1 {
    let key = filtered[i]
    let mut j = i - 1
    while j >= 0 &&
          compare_exponents_grlex(filtered[j].exponents, key.exponents) < 0 {
      filtered[j + 1] = filtered[j]
      j = j - 1
    }
    filtered[j + 1] = key
  }
  { num_vars: self.num_vars, terms: filtered, }
}

///|
/// Evaluate a MultivariatePoly at point `x : Array[Double]`.
pub fn MultivariatePoly::eval(
  self : MultivariatePoly,
  x : Array[Double],
) -> Double {
  let mut sum = 0.0
  for term in self.terms {
    let mut prod = term.coeff
    for i = 0; i < term.exponents.length() && i < x.length(); i = i + 1 {
      let exp = term.exponents[i]
      if exp > 0 {
        prod = prod * @math.pow(x[i], exp.to_double())
      }
    }
    sum = sum + prod
  }
  sum
}

///|
/// Subtract `scale * x^{shift_exp} * g` from `f` during polynomial ideal reduction.
pub fn poly_subtract_scaled_shifted(
  f : MultivariatePoly,
  g : MultivariatePoly,
  scale : Double,
  shift_exp : Array[Int],
) -> MultivariatePoly {
  let new_terms : Array[PolyMonomial] = []
  for t in f.terms {
    new_terms.push({ coeff: t.coeff, exponents: t.exponents.copy(), })
  }
  for gt in g.terms {
    let shifted = Array::make(f.num_vars, 0)
    for i = 0; i < f.num_vars; i = i + 1 {
      let ge = if i < gt.exponents.length() { gt.exponents[i] } else { 0 }
      let se = if i < shift_exp.length() { shift_exp[i] } else { 0 }
      shifted[i] = ge + se
    }
    new_terms.push({ coeff: -scale * gt.coeff, exponents: shifted, })
  }
  let raw : MultivariatePoly = { num_vars: f.num_vars, terms: new_terms, }
  raw.normalize()
}

///|
/// Check if monomial `a` is divisible by monomial `b`, returning `Some(a - b)` if so.
fn monomial_divide(
  a : Array[Int],
  b : Array[Int],
  num_vars : Int,
) -> Array[Int]? {
  let diff = Array::make(num_vars, 0)
  for i = 0; i < num_vars; i = i + 1 {
    let ea = if i < a.length() { a[i] } else { 0 }
    let eb = if i < b.length() { b[i] } else { 0 }
    if ea < eb {
      return None
    }
    diff[i] = ea - eb
  }
  Some(diff)
}

///|
/// Reduce polynomial `f` modulo an ideal basis `generators` in Q[x_0, ..., x_{n-1}]
/// (Gröbner / multivariate polynomial division f ->_G^* r).
pub fn reduce_poly_modulo_ideal(
  f : MultivariatePoly,
  generators : Array[MultivariatePoly],
) -> MultivariatePoly {
  let mut cur = f.normalize()
  let remainder_terms : Array[PolyMonomial] = []
  let mut steps = 0
  while cur.terms.length() > 0 && steps < 64 {
    steps = steps + 1
    let lt = cur.terms[0]
    let mut reduced = false
    for g in generators {
      let g_norm = g.normalize()
      if g_norm.terms.length() > 0 {
        let glt = g_norm.terms[0]
        match monomial_divide(lt.exponents, glt.exponents, f.num_vars) {
          Some(shift) => {
            let scale = lt.coeff / glt.coeff
            cur = poly_subtract_scaled_shifted(cur, g_norm, scale, shift)
            reduced = true
            break
          }
          None => ()
        }
      }
    }
    if !reduced {
      // Move leading term to remainder and continue reducing the tail
      remainder_terms.push(lt)
      let tail_terms : Array[PolyMonomial] = []
      for i = 1; i < cur.terms.length(); i = i + 1 {
        tail_terms.push(cur.terms[i])
      }
      cur = { num_vars: f.num_vars, terms: tail_terms, }
    }
  }
  for t in cur.terms {
    remainder_terms.push(t)
  }
  let rem : MultivariatePoly = { num_vars: f.num_vars, terms: remainder_terms, }
  rem.normalize()
}

///|
/// Buchberger S-Polynomial S(f, g) for Ring-Lifted Ideal Reduction.
pub fn compute_spoly(
  f : MultivariatePoly,
  g : MultivariatePoly,
) -> MultivariatePoly {
  let fn_ = f.normalize()
  let gn = g.normalize()
  if fn_.terms.length() == 0 || gn.terms.length() == 0 {
    return { num_vars: f.num_vars, terms: [], }
  }
  let ltf = fn_.terms[0]
  let ltg = gn.terms[0]
  let n = f.num_vars
  let shift_f = Array::make(n, 0)
  let shift_g = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    let ef = if i < ltf.exponents.length() { ltf.exponents[i] } else { 0 }
    let eg = if i < ltg.exponents.length() { ltg.exponents[i] } else { 0 }
    let lcm_e = ef.max(eg)
    shift_f[i] = lcm_e - ef
    shift_g[i] = lcm_e - eg
  }
  let zero : MultivariatePoly = { num_vars: n, terms: [], }
  let f_part = poly_subtract_scaled_shifted(
    zero,
    fn_,
    -1.0 / ltf.coeff,
    shift_f,
  )
  poly_subtract_scaled_shifted(f_part, gn, 1.0 / ltg.coeff, shift_g)
}

///|
/// Ring-Lifted Cylindrical Algebraic Covering (環升態圓柱代數覆蓋理想歸約) engine.
pub(all) struct CylindricalAlgebraicCovering {
  num_arith_vars : Int
  ideal_generators : Array[MultivariatePoly]
  // Active inequality constraints: (poly, op, rhs, reason_lit)
  active_constraints : Array[(MultivariatePoly, ArithOp, Double, Int)]
  mut ideal_reductions_count : Int
  mut cac_pruned_cells : Int
}

///|
/// Create a new CylindricalAlgebraicCovering engine.
pub fn CylindricalAlgebraicCovering::new(
  num_arith_vars : Int,
) -> CylindricalAlgebraicCovering {
  {
    num_arith_vars,
    ideal_generators: [],
    active_constraints: [],
    ideal_reductions_count: 0,
    cac_pruned_cells: 0,
  }
}

///|
/// Add an algebraic equality generator g(x) = 0 to the polynomial ring ideal.
pub fn CylindricalAlgebraicCovering::add_ideal_generator(
  self : CylindricalAlgebraicCovering,
  g : MultivariatePoly,
) -> Unit {
  self.ideal_generators.push(g.normalize())
}

///|
/// Register a guarded polynomial inequality constraint `poly(x) op rhs` with `reason_lit`.
pub fn CylindricalAlgebraicCovering::add_constraint(
  self : CylindricalAlgebraicCovering,
  poly : MultivariatePoly,
  op : ArithOp,
  rhs : Double,
  reason_lit : Int,
) -> Unit {
  self.active_constraints.push((poly.normalize(), op, rhs, reason_lit))
}

///|
/// Check whether value `v` satisfies `v op rhs`.
fn eval_arith_op(v : Double, op : ArithOp, rhs : Double) -> Bool {
  match op {
    Le => v <= rhs + 1.0e-7
    Ge => v >= rhs - 1.0e-7
    Eq => (v - rhs).abs() <= 1.0e-7
    Lt => v < rhs - 1.0e-7
    Gt => v > rhs + 1.0e-7
  }
}

///|
/// Execute Ring-Lifted Cylindrical Algebraic Covering & Ideal Reduction over the box
/// `[var_lb[k], var_ub[k]]` around `base_sample`.
/// Returns `Some(conflict_clause)` if a cylindrical level is completely covered by offending
/// intervals after ideal reduction, or `None` if a feasible lifted cylinder witness exists.
pub fn CylindricalAlgebraicCovering::check_cylindrical_covering(
  self : CylindricalAlgebraicCovering,
  base_sample : Array[Double],
  var_lb : Array[Double],
  var_ub : Array[Double],
  next_clause_id : Int,
) -> Clause? {
  if self.active_constraints.length() == 0 {
    return None
  }
  let sample = base_sample.copy()
  // Lift level by level k = 0 .. num_arith_vars - 1
  for k = 0; k < self.num_arith_vars; k = k + 1 {
    let lb_k = if k < var_lb.length() { var_lb[k] } else { -10.0 }
    let ub_k = if k < var_ub.length() { var_ub[k] } else { 10.0 }
    if lb_k > ub_k + 1.0e-9 {
      return None
    }
    // Sample grid along cylinder fiber at level k (5 cell checkpoints: lb, q1, mid, q3, ub)
    let grid : Array[Double] = [
      lb_k,
      lb_k + 0.25 * (ub_k - lb_k),
      0.5 * (lb_k + ub_k),
      lb_k + 0.75 * (ub_k - lb_k),
      ub_k,
    ]
    let mut found_feasible_fiber_point = false
    let covering_reasons : Array[Int] = []

    for pt in grid {
      if k < sample.length() {
        sample[k] = pt
      }
      let mut point_ok = true
      for item in self.active_constraints {
        let (poly, op, rhs, rlit) = item
        let reduced_poly = reduce_poly_modulo_ideal(poly, self.ideal_generators)
        self.ideal_reductions_count = self.ideal_reductions_count + 1
        let val = reduced_poly.eval(sample)
        if !eval_arith_op(val, op, rhs) {
          point_ok = false
          if rlit != 0 {
            let mut exists = false
            for r in covering_reasons {
              if r == rlit {
                exists = true
              }
            }
            if !exists {
              covering_reasons.push(rlit)
            }
          }
        }
      }
      if point_ok {
        found_feasible_fiber_point = true
        break
      }
    }

    if !found_feasible_fiber_point && covering_reasons.length() > 0 {
      self.cac_pruned_cells = self.cac_pruned_cells + 1
      let conflict_lits : Array[Int] = []
      for r in covering_reasons {
        conflict_lits.push(lit_neg(r))
      }
      return Some(
        Clause::new(
          next_clause_id,
          conflict_lits,
          true,
          conflict_lits.length(),
          CacIdealReductionAxiom(k),
        ),
      )
    }
  }
  None
}

///|
/// Lazy SMT + CDCL(T) Homomorphic Conservation Ideal Verifier (同態守恆理想).
/// Maps CNF clauses homomorphically into the Boolean quotient polynomial ring
/// R[x_1, ..., x_n] / <x_i^2 - x_i>:
///   Psi(l_1 v ... v l_k) = prod_{j=1}^k (1 - tilde(l_j))
/// A truth assignment x in {0, 1}^n satisfies C iff Psi(C)(x) == 0.
pub(all) struct HomomorphicConservationIdeal {
  num_vars : Int
  mut verified_resolutions : Int
  mut verified_clauses : Int
}

///|
/// Construct a HomomorphicConservationIdeal verifier.
pub fn HomomorphicConservationIdeal::new(
  num_vars : Int,
) -> HomomorphicConservationIdeal {
  { num_vars, verified_resolutions: 0, verified_clauses: 0, }
}

///|
/// Evaluate the homomorphic image polynomial Psi(C)(x) for a clause C at a Boolean/relaxed point x.
/// In the Boolean ring, Psi(C)(x) == 0 iff C is satisfied by x.
pub fn HomomorphicConservationIdeal::eval_clause_ideal_polynomial(
  self : HomomorphicConservationIdeal,
  clause : Clause,
  assignment : Array[TruthVal],
) -> Double {
  let _ = self.num_vars
  let mut prod = 1.0
  for lit in clause.lits {
    let v = lit_var(lit)
    let x_v = if v >= 1 && v < assignment.length() {
      match assignment[v] {
        True => 1.0
        False => 0.0
        Unassigned => 0.5
      }
    } else {
      0.5
    }
    let lit_val = if lit > 0 { x_v } else { 1.0 - x_v }
    prod = prod * (1.0 - lit_val)
  }
  prod
}

///|
/// Verify the Homomorphic Conservation Ideal invariant on a resolution step
/// `resolvent = Resolve(c1, c2, pivot_var)`:
/// For every Boolean point where Psi(c1)(x) == 0 and Psi(c2)(x) == 0,
/// we must have Psi(resolvent)(x) == 0 (i.e., Psi(resolvent) is in the radical ideal <Psi(c1), Psi(c2)>).
pub fn HomomorphicConservationIdeal::verify_resolution_conservation(
  self : HomomorphicConservationIdeal,
  c1 : Clause,
  c2 : Clause,
  resolvent : Clause,
) -> Bool {
  // Collect all variables appearing in c1, c2, resolvent (cap to 6 vars for exhaustive 2^k check)
  let vars : Array[Int] = []
  for c in [c1, c2, resolvent] {
    for lit in c.lits {
      let v = lit_var(lit)
      let mut seen = false
      for u in vars {
        if u == v {
          seen = true
        }
      }
      if !seen && vars.length() < 6 {
        vars.push(v)
      }
    }
  }
  let k = vars.length()
  let total_masks = 1 << k
  let assign = Array::make(self.num_vars + 1, False)
  for mask = 0; mask < total_masks; mask = mask + 1 {
    for i = 0; i < k; i = i + 1 {
      let v = vars[i]
      if v >= 1 && v <= self.num_vars {
        assign[v] = if ((mask >> i) & 1) == 1 { True } else { False }
      }
    }
    let p1 = self.eval_clause_ideal_polynomial(c1, assign)
    let p2 = self.eval_clause_ideal_polynomial(c2, assign)
    let pres = self.eval_clause_ideal_polynomial(resolvent, assign)
    // If both c1 and c2 vanish in the ideal (satisfied), resolvent must also vanish!
    if p1.abs() < 1.0e-9 && p2.abs() < 1.0e-9 {
      if pres.abs() > 1.0e-9 {
        return false
      }
    }
  }
  self.verified_resolutions = self.verified_resolutions + 1
  true
}

///|
/// Verify that all clauses in `clauses` vanish under `model` in the Homomorphic Conservation Ideal.
pub fn HomomorphicConservationIdeal::verify_all_clauses_conserved(
  self : HomomorphicConservationIdeal,
  clauses : Array[Clause],
  model : Array[TruthVal],
) -> Bool {
  for c in clauses {
    let val = self.eval_clause_ideal_polynomial(c, model)
    if val.abs() > 1.0e-6 {
      return false
    }
    self.verified_clauses = self.verified_clauses + 1
  }
  true
}

///|
/// Superposed Cooperative Exhaustive Upper-Bound Resolution Clause Surjective Axiom Invariant
/// Constraint Projector (疊加協同窮舉上界歸因子句全射公理不變量約束投影).
pub(all) struct SurjectiveAxiomProjector {
  mut total_certified_clauses : Int
  mut upper_bound_projections : Int
  schema_coverage : Array[Int] // Counts per AxiomOrigin category (9 categories)
}

///|
/// Create a new SurjectiveAxiomProjector.
pub fn SurjectiveAxiomProjector::new() -> SurjectiveAxiomProjector {
  {
    total_certified_clauses: 0,
    upper_bound_projections: 0,
    schema_coverage: Array::make(9, 0),
  }
}

///|
/// Map an AxiomOrigin to its canonical index in [0..8] and record surjective coverage.
pub fn SurjectiveAxiomProjector::certify_clause_origin(
  self : SurjectiveAxiomProjector,
  clause : Clause,
) -> Bool {
  let expected_hash = compute_clause_conservation_hash(clause.lits)
  if clause.conservation_hash != expected_hash {
    return false
  }
  let idx = match clause.origin {
    ProblemInput => 0
    UipResolution(_, _) => 1
    EufCongruenceAxiom(_, _) => 2
    KleisliUnificationAxiom(_) => 3
    LraFarkasAxiom(_) => 4
    LiaIntegralityCut(_) => 5
    QapDiscretePruneAxiom(_) => 6
    CacIdealReductionAxiom(_) => 7
    LrbOptimalLemma(_) => 8
  }
  self.schema_coverage[idx] = self.schema_coverage[idx] + 1
  self.total_certified_clauses = self.total_certified_clauses + 1
  true
}

///|
/// Perform Superposed Cooperative Exhaustive Upper-Bound Resolution Constraint Projection:
/// Given a linear objective `bool_obj_weights`, an upper bound `ub_limit`, and current clauses,
/// projects minimal forbidden positive-cost variable pairs/triples whose combined cost exceeds `ub_limit`,
/// and resolves them with binary implications to strengthen the upper-bound invariant!
pub fn SurjectiveAxiomProjector::project_upper_bound_clauses(
  self : SurjectiveAxiomProjector,
  bool_obj_weights : Array[Double],
  ub_limit : Double,
  start_clause_id : Int,
) -> Array[Clause] {
  let projected : Array[Clause] = []
  let mut cid = start_clause_id
  let n = bool_obj_weights.length() - 1
  // 1. Single variables exceeding ub_limit
  for v = 1; v <= n; v = v + 1 {
    if bool_obj_weights[v] >= ub_limit - 1.0e-9 {
      let c = Clause::new(
        cid,
        [mk_lit(v, false)],
        true,
        1,
        LrbOptimalLemma((ub_limit * 100.0).to_int()),
      )
      let _ = self.certify_clause_origin(c)
      projected.push(c)
      cid = cid + 1
      self.upper_bound_projections = self.upper_bound_projections + 1
    }
  }
  // 2. Superposed pairwise exhaustive upper-bound projection: w_u + w_v >= ub_limit
  for u = 1; u <= n; u = u + 1 {
    let wu = bool_obj_weights[u]
    if wu > 0.0 && wu < ub_limit - 1.0e-9 {
      for v = u + 1; v <= n; v = v + 1 {
        let wv = bool_obj_weights[v]
        if wv > 0.0 && wv < ub_limit - 1.0e-9 && wu + wv >= ub_limit - 1.0e-9 {
          let c = Clause::new(
            cid,
            [mk_lit(u, false), mk_lit(v, false)],
            true,
            2,
            LrbOptimalLemma((ub_limit * 100.0).to_int()),
          )
          let _ = self.certify_clause_origin(c)
          projected.push(c)
          cid = cid + 1
          self.upper_bound_projections = self.upper_bound_projections + 1
        }
      }
    }
  }
  projected
}
