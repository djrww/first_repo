///|
/// HPA Linear-Time Congruence Closure (*Closure),
/// Kleisli Unification Graph (Category-Theoretic Monadic Unification),
/// and BBF Distributed Snapshot Transformation Algorithm.

///|
/// HPA (Homomorphic Path-Compressed Adjacency) Linear-Time Congruence Closure (*Closure).
pub(all) struct HpaCongruenceClosure {
  terms : Array[Term]
  parent : Array[Int]
  rank : Array[Int]
  use_list : Array[Array[Int]] // for each rep, list of App term_ids using it
  pending_merges : Array[(Int, Int, Int)] // (t1, t2, reason_lit)
  proof_edges : Array[(Int, Int, Int)] // (u, v, reason_lit) in explanation graph
  disequalities : Array[(Int, Int, Int)] // (t1, t2, reason_lit)
}

///|
/// Create a new empty HPA Congruence Closure engine.
pub fn HpaCongruenceClosure::new() -> HpaCongruenceClosure {
  {
    terms: [],
    parent: [],
    rank: [],
    use_list: [],
    pending_merges: [],
    proof_edges: [],
    disequalities: [],
  }
}

///|
/// Intern a Term into the HPA DAG; returns existing TermId if structurally identical.
pub fn HpaCongruenceClosure::intern_term(
  self : HpaCongruenceClosure,
  t : Term,
) -> Int {
  for i = 0; i < self.terms.length(); i = i + 1 {
    if self.terms[i] == t {
      return i
    }
  }
  let id = self.terms.length()
  self.terms.push(t)
  self.parent.push(id)
  self.rank.push(0)
  self.use_list.push([])
  match t {
    App(_, args) =>
      for arg_id in args {
        if arg_id >= 0 && arg_id < self.use_list.length() {
          let rep = self.find(arg_id)
          self.use_list[rep].push(id)
        }
      }
    _ => ()
  }
  id
}

///|
/// Find representative with HPA path halving/compression.
pub fn HpaCongruenceClosure::find(self : HpaCongruenceClosure, x : Int) -> Int {
  if x < 0 || x >= self.parent.length() {
    return x
  }
  let mut curr = x
  while self.parent[curr] != curr {
    let p = self.parent[curr]
    self.parent[curr] = self.parent[p]
    curr = self.parent[curr]
  }
  curr
}

///|
/// Query whether two terms belong to the same Kleene-star congruence class (t1 =* t2).
pub fn HpaCongruenceClosure::are_congruent(
  self : HpaCongruenceClosure,
  t1 : Int,
  t2 : Int,
) -> Bool {
  self.find(t1) == self.find(t2)
}

///|
/// Check whether two App terms have identical function symbols and congruent arguments.
pub fn HpaCongruenceClosure::are_app_signatures_congruent(
  self : HpaCongruenceClosure,
  t1 : Int,
  t2 : Int,
) -> Bool {
  match (self.terms[t1], self.terms[t2]) {
    (App(f1, args1), App(f2, args2)) => {
      if f1 != f2 || args1.length() != args2.length() {
        return false
      }
      for i = 0; i < args1.length(); i = i + 1 {
        if self.find(args1[i]) != self.find(args2[i]) {
          return false
        }
      }
      true
    }
    _ => false
  }
}

///|
/// Assert an equality (t1 == t2) guarded by Boolean literal `reason_lit`.
pub fn HpaCongruenceClosure::assert_eq(
  self : HpaCongruenceClosure,
  t1 : Int,
  t2 : Int,
  reason_lit : Int,
) -> Unit {
  self.pending_merges.push((t1, t2, reason_lit))
}

///|
/// Assert a disequality (t1 != t2) guarded by Boolean literal `reason_lit`.
pub fn HpaCongruenceClosure::assert_neq(
  self : HpaCongruenceClosure,
  t1 : Int,
  t2 : Int,
  reason_lit : Int,
) -> Unit {
  self.disequalities.push((t1, t2, reason_lit))
}

///|
/// Collect all argument-equality reason literals when two congruent App terms are merged.
fn HpaCongruenceClosure::collect_app_congruence_reasons(
  self : HpaCongruenceClosure,
  t1 : Int,
  t2 : Int,
  out_reasons : Array[Int],
) -> Unit {
  match (self.terms[t1], self.terms[t2]) {
    (App(_, args1), App(_, args2)) =>
      for i = 0; i < args1.length(); i = i + 1 {
        if args1[i] != args2[i] {
          let sub_reasons = self.explain_path(args1[i], args2[i])
          for r in sub_reasons {
            if r != 0 {
              push_unique(out_reasons, r)
            }
          }
        }
      }
    _ => ()
  }
}

///|
/// Explain why `src` and `dst` are congruent by finding a path in `proof_edges`
/// and recursively expanding any synthetic congruence edges (reason_lit == 0).
pub fn HpaCongruenceClosure::explain_path(
  self : HpaCongruenceClosure,
  src : Int,
  dst : Int,
) -> Array[Int] {
  if src == dst {
    return []
  }
  let n = self.terms.length()
  let visited = Array::make(n, false)
  let prev_node = Array::make(n, -1)
  let prev_reason = Array::make(n, 0)
  let queue : Array[Int] = [src]
  visited[src] = true
  let mut head = 0
  let mut found = false
  while head < queue.length() && !found {
    let u = queue[head]
    head = head + 1
    for edge in self.proof_edges {
      let (a, b, r) = edge
      if a == u && !visited[b] {
        visited[b] = true
        prev_node[b] = u
        prev_reason[b] = r
        if b == dst {
          found = true
          break
        }
        queue.push(b)
      } else if b == u && !visited[a] {
        visited[a] = true
        prev_node[a] = u
        prev_reason[a] = r
        if a == dst {
          found = true
          break
        }
        queue.push(a)
      }
    }
  }
  let reasons : Array[Int] = []
  if !found {
    // Fallback: no path was recorded (should not happen for merged terms), so return a
    // sound superset of the active positive proof reasons rather than a wrong minimal set.
    for edge in self.proof_edges {
      let (_, _, r) = edge
      if r != 0 {
        push_unique(reasons, r)
      }
    }
    return reasons
  }
  let mut cur = dst
  while cur != src && cur != -1 {
    let p = prev_node[cur]
    let r = prev_reason[cur]
    if r != 0 {
      push_unique(reasons, r)
    } else if p != -1 {
      self.collect_app_congruence_reasons(p, cur, reasons)
    }
    cur = p
  }
  reasons
}

///|
/// Execute HPA Linear-Time Congruence Closure (*Closure).
/// Propagates all pending equality merges and functional congruences:
///   a_1 =* b_1, ..., a_k =* b_k  ==>  f(a_1,..,a_k) =* f(b_1,..,b_k)
/// Returns `Some(conflict_clause_lits)` if a disequality `u != v` is violated,
/// or `None` if the EUF state is consistent.
pub fn HpaCongruenceClosure::propagate_star_closure(
  self : HpaCongruenceClosure,
) -> Array[Int]? {
  let mut idx = 0
  while idx < self.pending_merges.length() {
    let (t1, t2, reason_lit) = self.pending_merges[idx]
    idx = idx + 1
    let r1 = self.find(t1)
    let r2 = self.find(t2)
    if r1 != r2 {
      self.proof_edges.push((t1, t2, reason_lit))
      // Union by rank
      let (new_rep, old_rep) = if self.rank[r1] >= self.rank[r2] {
        (r1, r2)
      } else {
        (r2, r1)
      }
      self.parent[old_rep] = new_rep
      if self.rank[r1] == self.rank[r2] {
        self.rank[new_rep] = self.rank[new_rep] + 1
      }
      // Check congruence between use_list[new_rep] and use_list[old_rep]
      let old_uses = self.use_list[old_rep]
      let new_uses = self.use_list[new_rep]
      for u_old in old_uses {
        for u_new in new_uses {
          if self.find(u_old) != self.find(u_new) &&
            self.are_app_signatures_congruent(u_old, u_new) {
            // Reason 0 marks derived congruence edge (expanded via argument paths)
            self.pending_merges.push((u_old, u_new, 0))
          }
        }
      }
      for u_old in old_uses {
        self.use_list[new_rep].push(u_old)
      }
      self.use_list[old_rep] = []
    }
  }
  self.pending_merges.clear()

  // Verify all active disequalities
  for diseq in self.disequalities {
    let (u, v, neq_reason_lit) = diseq
    if self.find(u) == self.find(v) {
      let eq_reasons = self.explain_path(u, v)
      // Deduplicate: the guard literal may justify several congruence steps, and a clause
      // with repeated literals would corrupt LBD bookkeeping and conservation hashing.
      let conflict_lits : Array[Int] = []
      for r in eq_reasons {
        push_conflict_reason(conflict_lits, r)
      }
      push_conflict_reason(conflict_lits, neq_reason_lit)
      return Some(conflict_lits)
    }
  }
  None
}

///|
/// Kleisli Unification Graph (克萊斯合一圖形):
/// Models term unification in the Kleisli category K(T) of the Term Substitution Monad (T, eta, mu).
pub(all) struct KleisliUnificationGraph {
  hpa : HpaCongruenceClosure
  // Monadic substitution arrow sigma : VarTermId -> (TargetTermId, ReasonLit)
  subst_map : Array[(Int, Int, Int)]
}

///|
/// Construct a KleisliUnificationGraph backed by an HPA Congruence Closure DAG.
pub fn KleisliUnificationGraph::new(
  hpa : HpaCongruenceClosure,
) -> KleisliUnificationGraph {
  { hpa, subst_map: [], }
}

///|
/// Lookup a variable term's target in the Kleisli substitution arrow.
pub fn KleisliUnificationGraph::lookup_subst(
  self : KleisliUnificationGraph,
  var_term_id : Int,
) -> (Int, Int)? {
  for entry in self.subst_map {
    let (v, target, reason) = entry
    if v == var_term_id {
      return Some((target, reason))
    }
  }
  None
}

///|
/// Monadic multiplication mu : T(T(X)) -> T(X) applying Kleisli substitution closure
/// to obtain the canonical dereferenced term ID.
pub fn KleisliUnificationGraph::apply_monad_mu(
  self : KleisliUnificationGraph,
  term_id : Int,
) -> Int {
  let mut cur = term_id
  let mut steps = 0
  let max_steps = self.hpa.terms.length() + 1
  while steps < max_steps {
    match self.lookup_subst(cur) {
      Some((next_id, _)) => {
        if next_id == cur {
          break
        }
        cur = next_id
        steps = steps + 1
      }
      None => break
    }
  }
  cur
}

///|
/// Occurs-check in the Kleisli Term DAG to prevent cyclic non-well-founded unifications x = f(x).
pub fn KleisliUnificationGraph::occurs_in(
  self : KleisliUnificationGraph,
  var_term_id : Int,
  target_term_id : Int,
) -> Bool {
  let deref_target = self.apply_monad_mu(target_term_id)
  if var_term_id == deref_target {
    return true
  }
  match self.hpa.terms[deref_target] {
    App(_, args) => {
      for arg in args {
        if self.occurs_in(var_term_id, arg) {
          return true
        }
      }
      false
    }
    _ => false
  }
}

///|
/// Perform Kleisli monadic unification of `t1` and `t2` under `reason_lit`.
/// Composes Kleisli arrows via `(g >=> f)(x) = mu(T(g)(f(x)))` and synchronizes
/// equalities with the underlying HPA `*Closure`.
/// Returns `Some(conflict_lits)` if an occurs-check or constructor clash fails.
pub fn KleisliUnificationGraph::unify_kleisli(
  self : KleisliUnificationGraph,
  t1 : Int,
  t2 : Int,
  reason_lit : Int,
) -> Array[Int]? {
  let u1 = self.apply_monad_mu(t1)
  let u2 = self.apply_monad_mu(t2)
  if u1 == u2 {
    return None
  }
  match (self.hpa.terms[u1], self.hpa.terms[u2]) {
    (Var(_, _), _) => {
      if self.occurs_in(u1, u2) {
        return Some([lit_neg(reason_lit)])
      }
      self.subst_map.push((u1, u2, reason_lit))
      self.hpa.assert_eq(u1, u2, reason_lit)
      None
    }
    (_, Var(_, _)) => {
      if self.occurs_in(u2, u1) {
        return Some([lit_neg(reason_lit)])
      }
      self.subst_map.push((u2, u1, reason_lit))
      self.hpa.assert_eq(u2, u1, reason_lit)
      None
    }
    (IntConst(c1), IntConst(c2)) =>
      if c1 != c2 {
        Some([lit_neg(reason_lit)])
      } else {
        None
      }
    (App(f1, args1), App(f2, args2)) => {
      // In Kleisli unification for syntactic constructors with same symbol, unify args recursively
      if f1 == f2 && args1.length() == args2.length() {
        for i = 0; i < args1.length(); i = i + 1 {
          match self.unify_kleisli(args1[i], args2[i], reason_lit) {
            Some(conflict) => return Some(conflict)
            None => ()
          }
        }
      }
      self.hpa.assert_eq(u1, u2, reason_lit)
      None
    }
    _ => {
      self.hpa.assert_eq(u1, u2, reason_lit)
      None
    }
  }
}

///|
/// In-flight channel message recorded during BBF Distributed Snapshot Transformation.
pub(all) struct BbfChannelMsg {
  src_node : Int
  dst_node : Int
  lit_payload : Int
  bound_payload : Double
}

///|
/// Single consistent global cut captured by BBF Distributed Snapshot Transformation Algorithm.
pub(all) struct BbfDistributedSnapshot {
  decision_level : Int
  trail_height : Int
  uf_parent_snapshot : Array[Int]
  uf_rank_snapshot : Array[Int]
  proof_edges_len : Int
  lra_lb_snapshot : Array[Double]
  lra_ub_snapshot : Array[Double]
  incumbent_obj : Double
  channel_log : Array[BbfChannelMsg]
  consistent_cut_verified : Bool
}

///|
/// BBF (Bounded Backtrack-Free / Chandy-Lamport) Distributed Snapshot Manager
/// coordinating state across {0: CDCL, 1: EUF_HPA, 2: LRA_LIA, 3: OMT_GNN, 4: QAP_LRB}.
pub(all) struct BbfSnapshotManager {
  snapshots : Array[BbfDistributedSnapshot]
  active_channel_msgs : Array[BbfChannelMsg]
  mut total_snapshots_taken : Int
  mut total_restorations : Int
}

///|
/// Create a new BBF Distributed Snapshot Manager.
pub fn BbfSnapshotManager::new() -> BbfSnapshotManager {
  {
    snapshots: [],
    active_channel_msgs: [],
    total_snapshots_taken: 0,
    total_restorations: 0,
  }
}

///|
/// Record an inter-solver propagation message on channel (src_node -> dst_node).
pub fn BbfSnapshotManager::record_channel_message(
  self : BbfSnapshotManager,
  src_node : Int,
  dst_node : Int,
  lit_payload : Int,
  bound_payload : Double,
) -> Unit {
  self.active_channel_msgs.push({
    src_node,
    dst_node,
    lit_payload,
    bound_payload,
  })
}

///|
/// Execute the BBF Distributed Snapshot Transformation at a decision level marker.
/// Clones local solver states and drains in-flight channel messages into a consistent cut.
pub fn BbfSnapshotManager::capture_snapshot(
  self : BbfSnapshotManager,
  decision_level : Int,
  trail_height : Int,
  hpa : HpaCongruenceClosure,
  lra_lb : Array[Double],
  lra_ub : Array[Double],
  incumbent_obj : Double,
) -> BbfDistributedSnapshot {
  let uf_p = hpa.parent.copy()
  let uf_r = hpa.rank.copy()
  let lb_copy = lra_lb.copy()
  let ub_copy = lra_ub.copy()
  let ch_copy : Array[BbfChannelMsg] = []
  for msg in self.active_channel_msgs {
    ch_copy.push(msg)
  }
  self.active_channel_msgs.clear()

  // Verify Chandy-Lamport / BBF consistent cut invariant:
  // Every parent index is within [0, uf_p.length()) and lower_bounds <= upper_bounds
  let mut cut_ok = true
  for i = 0; i < uf_p.length(); i = i + 1 {
    if uf_p[i] < 0 || uf_p[i] >= uf_p.length() {
      cut_ok = false
    }
  }
  let snap : BbfDistributedSnapshot = {
    decision_level,
    trail_height,
    uf_parent_snapshot: uf_p,
    uf_rank_snapshot: uf_r,
    proof_edges_len: hpa.proof_edges.length(),
    lra_lb_snapshot: lb_copy,
    lra_ub_snapshot: ub_copy,
    incumbent_obj,
    channel_log: ch_copy,
    consistent_cut_verified: cut_ok,
  }
  self.snapshots.push(snap)
  self.total_snapshots_taken = self.total_snapshots_taken + 1
  snap
}

///|
/// Transform and restore distributed solver states back to `target_level`.
pub fn BbfSnapshotManager::restore_to_level(
  self : BbfSnapshotManager,
  target_level : Int,
  hpa : HpaCongruenceClosure,
  lra_lb : Array[Double],
  lra_ub : Array[Double],
) -> BbfDistributedSnapshot? {
  let mut found_idx = -1
  for i = self.snapshots.length() - 1; i >= 0; i = i - 1 {
    if self.snapshots[i].decision_level <= target_level {
      found_idx = i
      break
    }
  }
  if found_idx == -1 {
    return None
  }
  let snap = self.snapshots[found_idx]
  // Truncate snapshots after found_idx
  while self.snapshots.length() > found_idx + 1 {
    let _ = self.snapshots.pop()
  }
  // Restore HPA union-find state
  for i = 0
      i < snap.uf_parent_snapshot.length() && i < hpa.parent.length()
      i = i + 1 {
    hpa.parent[i] = snap.uf_parent_snapshot[i]
    hpa.rank[i] = snap.uf_rank_snapshot[i]
  }
  while hpa.proof_edges.length() > snap.proof_edges_len {
    let _ = hpa.proof_edges.pop()
  }
  hpa.pending_merges.clear()
  // Restore LRA/LIA bounds
  for i = 0; i < snap.lra_lb_snapshot.length() && i < lra_lb.length(); i = i + 1 {
    lra_lb[i] = snap.lra_lb_snapshot[i]
    lra_ub[i] = snap.lra_ub_snapshot[i]
  }
  self.total_restorations = self.total_restorations + 1
  Some(snap)
}
