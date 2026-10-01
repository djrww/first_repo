///|
/// VSIDS (Variable State Independent Decaying Sum) decision heuristic.
///
/// This replaces the earlier learning-rate brancher, whose hybrid score was mostly a
/// constant weighted sum with a hand-tuned locality decay. VSIDS is the branching scheme
/// actually used by modern CDCL solvers and is described directly in terms of measurable
/// quantities:
///
///   * every variable keeps an activity score, initialised to 0,
///   * a conflict bumps the activity of every variable participating in the conflict
///     analysis by the current increment `var_inc`,
///   * after each conflict the increment is divided by `vsids_var_decay` (0.95), so older
///     activity counts weigh less and the heuristic follows the recent conflict history,
///   * the next branch variable is the unassigned variable with the highest activity.
///
/// Phase saving is kept (a variable is re-tried with the polarity it had when it was last
/// assigned); when no phase has ever been observed for a variable the caller falls back to
/// the GNN polarity prediction, which keeps the OMT-GNN component in the loop for polarity
/// only — it no longer fabricates the branching order.
pub(all) struct VsidsOracle {
  num_vars : Int
  /// Current activity increment; grows by `1 / vsids_var_decay` per conflict.
  mut var_inc : Double
  /// 1-indexed activity score per variable.
  activity : Array[Double]
  mut conflicts : Int
  mut rescalings : Int
  saved_phase : Array[Bool]
  phase_valid : Array[Bool]
}

///|
/// Create a VSIDS oracle for `num_vars` Boolean variables.
pub fn VsidsOracle::new(num_vars : Int) -> VsidsOracle {
  {
    num_vars,
    var_inc: vsids_var_inc_initial,
    activity: Array::make(num_vars + 1, 0.0),
    conflicts: 0,
    rescalings: 0,
    saved_phase: Array::make(num_vars + 1, false),
    phase_valid: Array::make(num_vars + 1, false),
  }
}

///|
/// Add `var_inc` to the activity of `v`.
fn VsidsOracle::bump(self : VsidsOracle, v : Int) -> Unit {
  if v >= 1 && v <= self.num_vars {
    self.activity[v] = self.activity[v] + self.var_inc
  }
}

///|
/// Keep activities representable: when the increment grows past the rescale threshold,
/// divide every activity (and the increment) by the increment. This preserves the relative
/// ordering exactly while preventing overflow in long runs.
fn VsidsOracle::rescale_if_needed(self : VsidsOracle) -> Unit {
  if self.var_inc > vsids_rescale_threshold {
    for v = 1; v <= self.num_vars; v = v + 1 {
      self.activity[v] = self.activity[v] / self.var_inc
    }
    self.var_inc = 1.0
    self.rescalings = self.rescalings + 1
  }
}

///|
/// Register a conflict: decay the increment and bump every participating variable.
/// `conflict_vars` is the set of variables collected by the 1-UIP analysis (the same set
/// that appears in the learnt clause plus the resolved reason clauses).
pub fn VsidsOracle::on_conflict(
  self : VsidsOracle,
  conflict_vars : Array[Int],
) -> Unit {
  self.conflicts = self.conflicts + 1
  self.var_inc = self.var_inc / vsids_var_decay
  self.rescale_if_needed()
  for v in conflict_vars {
    self.bump(v)
  }
}

///|
/// Remember the polarity `v` was assigned with (phase saving).
pub fn VsidsOracle::on_assign(self : VsidsOracle, v : Int, phase : Bool) -> Unit {
  if v >= 1 && v <= self.num_vars {
    self.saved_phase[v] = phase
    self.phase_valid[v] = true
  }
}

///|
/// Store a phase for `v` without an assignment event. Used to steer the search towards the
/// polarities seen in the best incumbent, and by the optimality lemma engine.
pub fn VsidsOracle::hint_phase(self : VsidsOracle, v : Int, phase : Bool) -> Unit {
  if v >= 1 && v <= self.num_vars {
    self.saved_phase[v] = phase
    self.phase_valid[v] = true
  }
}

///|
/// Whether a phase has ever been observed for `v`.
pub fn VsidsOracle::is_phase_known(self : VsidsOracle, v : Int) -> Bool {
  v >= 1 && v <= self.num_vars && self.phase_valid[v]
}

///|
/// The saved phase of `v` (falls back to `false`, but callers should check
/// `is_phase_known` first).
pub fn VsidsOracle::saved_phase_of(self : VsidsOracle, v : Int) -> Bool {
  if v >= 1 && v <= self.num_vars {
    self.saved_phase[v]
  } else {
    false
  }
}

///|
/// Activity score of `v` (0.0 for an out-of-range variable).
pub fn VsidsOracle::activity_of(self : VsidsOracle, v : Int) -> Double {
  if v >= 1 && v <= self.num_vars {
    self.activity[v]
  } else {
    0.0
  }
}

/// Pick the unassigned variable with the highest activity (ties resolved by the lower
/// variable index, since the scan runs ascending). Returns `None` when all variables are
/// assigned.
pub fn VsidsOracle::select_branch_var(
  self : VsidsOracle,
  values : Array[TruthVal],
) -> Int? {
  let mut best_var = -1
  let mut best_score = 0.0
  for v = 1; v <= self.num_vars; v = v + 1 {
    let is_unassigned = if v < values.length() {
      values[v] == Unassigned
    } else {
      true
    }
    if is_unassigned {
      let score = self.activity[v]
      if best_var == -1 || score > best_score {
        best_var = v
        best_score = score
      }
    }
  }
  if best_var == -1 {
    None
  } else {
    Some(best_var)
  }
}

///|
/// A copy of the activity vector, used as the per-variable feature scale of the OMT-GNN
/// message passing.
pub fn VsidsOracle::activity_scores(self : VsidsOracle) -> Array[Double] {
  self.activity.copy()
}

/// Activity scores normalised to [0, 1] by the current maximum (all zeros stay zero), which
/// is the form the OMT-GNN message passing consumes.
pub fn VsidsOracle::normalized_activity_scores(self : VsidsOracle) -> Array[Double] {
  let out = self.activity.copy()
  let mut max_activity = 0.0
  for v = 1; v <= self.num_vars; v = v + 1 {
    if out[v] > max_activity {
      max_activity = out[v]
    }
  }
  if max_activity > 0.0 {
    for v = 1; v <= self.num_vars; v = v + 1 {
      out[v] = out[v] / max_activity
    }
  }
  out
}
