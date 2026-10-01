///|
/// Implication / conflict graph for CDCL(T).
///
/// Every Boolean assignment step is recorded as a node: decisions have no reason, implied
/// literals store the clause index and the antecedent literals that forced them. Conflicts
/// mark the falsified literals, so the graph is a real trace of the refutation and can be
/// exported as an SVG diagram.
///
/// The same file hosts the shared 1-UIP conflict analysis used by both the OMT solver and
/// the plain CDCL(T) solver, so the two search engines cannot drift apart.

///|
/// One node of the implication graph.
pub(all) struct ConflictNode {
  lit : Int
  level : Int
  /// Clause index in the solver's clause database, or -1 for a decision.
  reason_clause : Int
  /// Node indices of the falsified literals in `reason_clause` that implied `lit`.
  antecedents : Array[Int]
  /// Set when this literal takes part in a recorded conflict (drawn in red).
  mut on_conflict_path : Bool
}

///|
/// Chronological implication graph over the CDCL(T) trail.
pub(all) struct ImplicationGraph {
  num_vars : Int
  nodes : Array[ConflictNode]
  /// Newest node index for each literal sign, indexed by `2 * (var - 1) + (0 if lit > 0 else 1)`.
  lit_slot : Array[Int]
  mut decisions : Int
  mut implications : Int
  mut conflicts_recorded : Int
  /// Number of times an invariant check failed while recording; must stay 0.
  mut violations : Int
  mut last_violation : String
  mut last_conflict_lits : Array[Int]
}

///|
/// Create an empty implication graph for `num_vars` Boolean variables.
pub fn ImplicationGraph::new(num_vars : Int) -> ImplicationGraph {
  {
    num_vars,
    nodes: [],
    lit_slot: Array::make(2 * num_vars + 2, -1),
    decisions: 0,
    implications: 0,
    conflicts_recorded: 0,
    violations: 0,
    last_violation: "",
    last_conflict_lits: [],
  }
}

///|
/// Drop the recorded trace (used at the start of a solve); counters are cumulative.
pub fn ImplicationGraph::clear(self : ImplicationGraph) -> Unit {
  self.nodes.clear()
  for i = 0; i < self.lit_slot.length(); i = i + 1 {
    self.lit_slot[i] = -1
  }
  self.last_conflict_lits = []
}

///|
/// Slot index of a literal, or -1 when its variable is out of range.
fn ImplicationGraph::slot_of(self : ImplicationGraph, lit : Int) -> Int {
  let v = lit_var(lit)
  if v < 1 || v > self.num_vars {
    return -1
  }
  let sign_slot = if lit > 0 { 0 } else { 1 }
  2 * (v - 1) + sign_slot
}

///|
/// Newest node index for `lit`, or -1 when `lit` was never assigned.
pub fn ImplicationGraph::node_of(self : ImplicationGraph, lit : Int) -> Int {
  let slot = self.slot_of(lit)
  if slot < 0 || slot >= self.lit_slot.length() {
    return -1
  }
  self.lit_slot[slot]
}

fn ImplicationGraph::fail(self : ImplicationGraph, message : String) -> Unit {
  self.violations = self.violations + 1
  self.last_violation = message
}

///|
/// Record a decision literal (no reason) at `level`.
pub fn ImplicationGraph::record_decision(
  self : ImplicationGraph,
  lit : Int,
  level : Int,
) -> Int {
  self.decisions = self.decisions + 1
  let id = self.nodes.length()
  self.nodes.push({
    lit,
    level,
    reason_clause: -1,
    antecedents: [],
    on_conflict_path: false,
  })
  let slot = self.slot_of(lit)
  if slot >= 0 {
    self.lit_slot[slot] = id
  }
  id
}

///|
/// Record an implied literal together with the antecedent literals of its reason clause.
/// Recording checks that every antecedent was already assigned and that no antecedent sits
/// at a *higher* decision level than the implied literal; both are invariants of CDCL
/// propagation, so a failure means the reason clause was not a valid implication.
pub fn ImplicationGraph::record_implication(
  self : ImplicationGraph,
  lit : Int,
  level : Int,
  reason_clause : Int,
  antecedent_lits : Array[Int],
) -> Int {
  self.implications = self.implications + 1
  let antecedent_nodes : Array[Int] = []
  for alit in antecedent_lits {
    let idx = self.node_of(alit)
    if idx < 0 {
      self.fail("antecedent \{alit} of implied literal \{lit} was never assigned")
    } else {
      if self.nodes[idx].level > level {
        self.fail(
          "antecedent \{alit} (level \{self.nodes[idx].level}) is above implied literal \{lit} (level \{level})",
        )
      }
      antecedent_nodes.push(idx)
    }
  }
  let id = self.nodes.length()
  self.nodes.push({
    lit,
    level,
    reason_clause,
    antecedents: antecedent_nodes,
    on_conflict_path: false,
  })
  let slot = self.slot_of(lit)
  if slot >= 0 {
    self.lit_slot[slot] = id
  }
  id
}

///|
/// Record a conflict over `lits` (the literals that are all falsified) and mark the nodes
/// of their assignments. Nodes are keyed by assigned literals, so the literal that
/// falsifies a clause literal `lit` is `lit_neg(lit)`.
pub fn ImplicationGraph::record_conflict(
  self : ImplicationGraph,
  lits : Array[Int],
) -> Unit {
  self.conflicts_recorded = self.conflicts_recorded + 1
  self.last_conflict_lits = lits.copy()
  for lit in lits {
    let idx = self.node_of(lit_neg(lit))
    if idx < 0 {
      self.fail("conflict literal \{lit} has no assignment node in the implication graph")
    } else {
      self.nodes[idx].on_conflict_path = true
    }
  }
}

///|
/// Re-check every recorded node: levels are non-negative, reason indices are in range, and
/// each antecedent node exists and sits at a level not above its consequence.
/// Returns `true` when the whole trace is consistent.
pub fn ImplicationGraph::verify(self : ImplicationGraph) -> Bool {
  let mut ok = true
  for i = 0; i < self.nodes.length(); i = i + 1 {
    let node = self.nodes[i]
    if node.level < 0 {
      self.fail("node \{i} has negative level")
      ok = false
    }
    if node.reason_clause < -1 {
      self.fail("node \{i} has reason index \{node.reason_clause}")
      ok = false
    }
    for a in node.antecedents {
      if a < 0 || a >= self.nodes.length() {
        self.fail("node \{i} references antecedent node \{a} out of range")
        ok = false
      } else if self.nodes[a].level > node.level {
        self.fail(
          "antecedent node \{a} (level \{self.nodes[a].level}) is above node \{i} (level \{node.level})",
        )
        ok = false
      }
    }
  }
  ok && self.violations == 0
}

///|
/// Whether every literal in `lits` is falsified by `values` and every falsifying assignment
/// has a node in the graph. This is the graph-side counterpart of the learnt-clause
/// invariant check: a learnt clause must consist of literals that the graph can justify.
/// Nodes are keyed by *assigned* literals (the negation of a falsified clause literal), so
/// the lookup uses `lit_neg(lit)`.
pub fn ImplicationGraph::all_lits_justified(
  self : ImplicationGraph,
  lits : Array[Int],
  values : Array[TruthVal],
) -> Bool {
  for lit in lits {
    if !is_lit_false(lit, values) {
      return false
    }
    if self.node_of(lit_neg(lit)) < 0 {
      return false
    }
  }
  true
}

///|
/// Render the implication graph as an SVG document: nodes are grouped in columns by
/// decision level (left to right), arrows point from antecedent to consequence, decisions
/// are blue, implications green, and nodes on a recorded conflict path red.
pub fn ImplicationGraph::to_svg(self : ImplicationGraph) -> String {
  let mut max_level = 0
  for node in self.nodes {
    if node.level > max_level {
      max_level = node.level
    }
  }
  let per_level : Array[Int] = Array::make(max_level + 1, 0)
  let x_of : Array[Int] = []
  let y_of : Array[Int] = []
  for node in self.nodes {
    let lv = if node.level < 0 { 0 } else { node.level }
    let slot = per_level[lv]
    per_level[lv] = slot + 1
    x_of.push(80 + lv * 120)
    y_of.push(60 + slot * 56)
  }
  let mut max_slot = 0
  for c in per_level {
    if c > max_slot {
      max_slot = c
    }
  }
  let width = 160 + (max_level + 1) * 120
  let height = 120 + max_slot * 56
  let mut svg = "<svg xmlns='http://www.w3.org/2000/svg' width='\{width}' height='\{height}' viewBox='0 0 \{width} \{height}'>\n"
  svg = svg + "<rect width='100%' height='100%' fill='#0b1020'/>\n"
  svg = svg + "<text x='16' y='24' fill='#e8eefc' font-family='monospace' font-size='13'>CDCL(T) implication graph: \{self.nodes.length()} nodes, \{self.conflicts_recorded} conflict(s), \{self.violations} violation(s)</text>\n"
  // Edges first (so nodes are drawn on top)
  for i = 0; i < self.nodes.length(); i = i + 1 {
    for a in self.nodes[i].antecedents {
      svg = svg +
        "<line x1='\{x_of[a]}' y1='\{y_of[a]}' x2='\{x_of[i]}' y2='\{y_of[i]}' stroke='#55608a' stroke-width='1'/>\n"
    }
  }
  for i = 0; i < self.nodes.length(); i = i + 1 {
    let node = self.nodes[i]
    let fill = if node.on_conflict_path {
      "#ff6b6b"
    } else if node.reason_clause < 0 {
      "#4fa3ff"
    } else {
      "#8be28b"
    }
    svg = svg +
      "<circle cx='\{x_of[i]}' cy='\{y_of[i]}' r='15' fill='\{fill}' stroke='#0b1020' stroke-width='2'/>\n"
    svg = svg + "<text x='\{x_of[i]}' y='\{y_of[i] + 4}' text-anchor='middle' fill='#0b1020' font-family='monospace' font-size='11'>\{node.lit}</text>\n"
  }
  svg = svg + "</svg>\n"
  svg
}

///|
/// Number of distinct decision levels occurring among `lits` under `var_level` (the
/// literal-block distance of a clause; the level-0 literals count as one level). Solvers
/// certify the stored `Clause::lbd` against this value instead of trusting the analysis.
pub fn distinct_decision_levels(
  lits : Array[Int],
  var_level : Array[Int],
) -> Int {
  let levels : Array[Int] = []
  for lit in lits {
    let v = lit_var(lit)
    let lv = if v >= 0 && v < var_level.length() { var_level[v] } else { 0 }
    let mut seen = false
    for m in levels {
      if m == lv {
        seen = true
      }
    }
    if !seen {
      levels.push(lv)
    }
  }
  levels.length().max(1)
}

///|
/// 1-UIP conflict analysis over the trail, shared by the OMT solver and the CDCL(T) solver.
///
/// Returns `(learnt_lits, backtrack_level, lbd, participating_vars, reason_vars)`:
///   * `learnt_lits[0]` is the asserting literal (the negation of the first UIP),
///   * `learnt_lits[1]` is the literal of the highest other decision level,
///   * `lbd` counts the distinct decision levels occurring in the clause,
///   * `participating_vars` collected every variable touched by the resolution (the VSIDS
///     bump set), `reason_vars` only those reached through reason clauses.
pub fn analyze_conflict_1uip_from_trail(
  num_vars : Int,
  cur_level : Int,
  trail : Array[Int],
  var_level : Array[Int],
  var_reason : Array[Int],
  clauses : Array[Clause],
  conflict_lits : Array[Int],
) -> (Array[Int], Int, Int, Array[Int], Array[Int]) {
  if cur_level == 0 {
    return ([], 0, 1, [], [])
  }
  let seen = Array::make(num_vars + 1, false)
  let learnt : Array[Int] = [0] // placeholder for the asserting literal
  let participating_vars : Array[Int] = []
  let reason_vars : Array[Int] = []
  let mut path_c = 0
  // Initialise from the conflict clause
  for lit in conflict_lits {
    let v = lit_var(lit)
    if v >= 1 && v <= num_vars && !seen[v] {
      seen[v] = true
      participating_vars.push(v)
      if var_level[v] == cur_level {
        path_c = path_c + 1
      } else if var_level[v] > 0 {
        learnt.push(lit)
      }
    }
  }
  // Walk the trail backwards resolving reason clauses until the first UIP
  let mut trail_idx = trail.length() - 1
  let mut uip_lit = 0
  while path_c > 0 && trail_idx >= 0 {
    let p = trail[trail_idx]
    trail_idx = trail_idx - 1
    let pv = lit_var(p)
    if seen[pv] && var_level[pv] == cur_level {
      path_c = path_c - 1
      if path_c == 0 {
        uip_lit = lit_neg(p)
        break
      }
      let r_idx = var_reason[pv]
      if r_idx >= 0 && r_idx < clauses.length() {
        let reason_clause = clauses[r_idx]
        for rlit in reason_clause.lits {
          let rv = lit_var(rlit)
          if rv != pv && rv >= 1 && rv <= num_vars {
            if !seen[rv] {
              seen[rv] = true
              participating_vars.push(rv)
              reason_vars.push(rv)
              if var_level[rv] == cur_level {
                path_c = path_c + 1
              } else if var_level[rv] > 0 {
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
    // Fallback: the conflict clause itself, at the parent level
    let fallback : Array[Int] = []
    for lit in conflict_lits {
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
  let mut bt_level = 0
  let mut max_idx = 1
  let level_marks : Array[Int] = []
  for i = 0; i < learnt.length(); i = i + 1 {
    let lv = var_level[lit_var(learnt[i])]
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
  (learnt, bt_level, lbd, participating_vars, reason_vars)
}
