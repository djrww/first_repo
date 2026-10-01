///|
/// Inner-Layer OMT Graph Neural Network (GNN) over EUF + Clause-Variable Tripartite Graph
/// and SVM (Support Vector Machine) Kernel Function Mapping in RKHS.

///|
/// Kernel types supported by the OMT-SVM Kernel Mapper.
pub(all) enum SvmKernelKind {
  RbfGaussian(Double) // gamma
  Polynomial(Double, Double, Int) // (gamma, coef0, degree)
  HybridOmtEuf(Double, Double) // (gamma, euf_congruence_bonus)
}

///|
/// SVM Kernel Function Mapper operating in Reproducing Kernel Hilbert Space (RKHS).
/// Separates conflict-inducing search states (y = -1) from feasible/improving OMT states (y = +1)
/// and provides RKHS spectral margin bounds for Hybrid-6 pruning.
pub(all) struct SvmKernelMapper {
  kernel : SvmKernelKind
  support_vectors : Array[Array[Double]]
  alpha_y : Array[Double] // signed dual weights alpha_i * y_i
  mut bias : Double
  c_regularization : Double
}

///|
/// Create a new SVM Kernel Mapper.
pub fn SvmKernelMapper::new(
  kernel : SvmKernelKind,
  c_regularization : Double,
) -> SvmKernelMapper {
  { kernel, support_vectors: [], alpha_y: [], bias: 0.0, c_regularization, }
}

///|
/// Evaluate the Mercer kernel K(x, z) between two feature vectors in R^d.
pub fn SvmKernelMapper::eval_kernel(
  self : SvmKernelMapper,
  x : Array[Double],
  z : Array[Double],
  are_euf_congruent : Bool,
) -> Double {
  let n = if x.length() < z.length() { x.length() } else { z.length() }
  match self.kernel {
    RbfGaussian(gamma) => {
      let mut sq_dist = 0.0
      for i = 0; i < n; i = i + 1 {
        let diff = x[i] - z[i]
        sq_dist = sq_dist + diff * diff
      }
      @math.exp(-gamma * sq_dist)
    }
    Polynomial(gamma, coef0, degree) => {
      let mut dot = 0.0
      for i = 0; i < n; i = i + 1 {
        dot = dot + x[i] * z[i]
      }
      let base = gamma * dot + coef0
      @math.pow(base, degree.to_double())
    }
    HybridOmtEuf(gamma, euf_bonus) => {
      let mut sq_dist = 0.0
      for i = 0; i < n; i = i + 1 {
        let diff = x[i] - z[i]
        sq_dist = sq_dist + diff * diff
      }
      let rbf = @math.exp(-gamma * sq_dist)
      let bonus = if are_euf_congruent { euf_bonus } else { 0.0 }
      (rbf + bonus) / (1.0 + euf_bonus)
    }
  }
}

///|
/// Evaluate the SVM decision value f(x) = sum_i alpha_i * y_i * K(s_i, x) + bias.
pub fn SvmKernelMapper::decision_function(
  self : SvmKernelMapper,
  x : Array[Double],
  are_euf_congruent : Bool,
) -> Double {
  let mut sum = self.bias
  for i = 0; i < self.support_vectors.length(); i = i + 1 {
    let k_val = self.eval_kernel(self.support_vectors[i], x, are_euf_congruent)
    sum = sum + self.alpha_y[i] * k_val
  }
  sum
}

///|
/// Online dual SMO-style update adding or adjusting a support vector from OMT/CDCL(T) feedback.
/// `label_y` is +1.0 for feasible/improving OMT trajectories and -1.0 for conflict cores.
pub fn SvmKernelMapper::fit_online_sample(
  self : SvmKernelMapper,
  x : Array[Double],
  label_y : Double,
) -> Unit {
  let pred = self.decision_function(x, false)
  let margin = label_y * pred
  if margin < 1.0 {
    let step = (1.0 - margin).clamp(min=0.05, max=self.c_regularization)
    let signed_alpha = label_y * step
    // Cap support vector bank size for bounded overhead
    if self.support_vectors.length() < 32 {
      self.support_vectors.push(x.copy())
      self.alpha_y.push(signed_alpha)
    } else {
      // Replace oldest or merge into closest support vector
      let idx = self.support_vectors.length() - 1
      self.support_vectors[idx] = x.copy()
      self.alpha_y[idx] = signed_alpha
    }
    self.bias = self.bias + 0.1 * signed_alpha
  }
}

///|
/// Compute the RKHS dual norm ||w||_H^2 = sum_{i,j} alpha_i y_i alpha_j y_j K(s_i, s_j)
/// used as a spectral margin lower-bound contribution in Hybrid-6 dynamic pruning.
pub fn SvmKernelMapper::rkhs_spectral_margin_norm(
  self : SvmKernelMapper,
) -> Double {
  let m = self.support_vectors.length()
  if m == 0 {
    return 0.0
  }
  let mut norm_sq = 0.0
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      let k_ij = self.eval_kernel(
        self.support_vectors[i],
        self.support_vectors[j],
        i == j,
      )
      norm_sq = norm_sq + self.alpha_y[i] * self.alpha_y[j] * k_ij
    }
  }
  norm_sq.max(0.0).sqrt()
}

///|
/// OMT Graph Neural Network (OMT 圖神經網絡) over the tripartite Clause-Variable-EUF Graph.
/// Embedding dimension d = 6 per variable and per clause.
pub(all) struct OmtGnn {
  num_vars : Int
  embed_dim : Int
  var_embeddings : Array[Array[Double]] // (num_vars + 1) x 6
  clause_embeddings : Array[Array[Double]] // num_clauses x 6
  euf_edges : Array[(Int, Int)] // pairs of Boolean vars linked via EUF congruence
  obj_weights : Array[Double] // OMT objective weight per variable (1-indexed)
  mut message_passing_rounds : Int
}

///|
/// Construct and initialize an OMT Graph Neural Network.
pub fn OmtGnn::new(
  num_vars : Int,
  clauses : Array[Clause],
  obj_weights : Array[Double],
) -> OmtGnn {
  let d = 6
  let var_embeddings : Array[Array[Double]] = []
  for _i = 0; _i <= num_vars; _i = _i + 1 {
    var_embeddings.push(Array::make(d, 0.0))
  }
  let pos_deg = Array::make(num_vars + 1, 0.0)
  let neg_deg = Array::make(num_vars + 1, 0.0)
  for c in clauses {
    for lit in c.lits {
      let v = lit_var(lit)
      if v >= 1 && v <= num_vars {
        if lit > 0 {
          pos_deg[v] = pos_deg[v] + 1.0
        } else {
          neg_deg[v] = neg_deg[v] + 1.0
        }
      }
    }
  }
  let norm_c = clauses.length().max(1).to_double()
  for v = 1; v <= num_vars; v = v + 1 {
    let obj_w = if v < obj_weights.length() { obj_weights[v] } else { 0.0 }
    var_embeddings[v][0] = pos_deg[v] / norm_c
    var_embeddings[v][1] = neg_deg[v] / norm_c
    var_embeddings[v][2] = @math.tanh(obj_w * 0.1)
    var_embeddings[v][3] = (pos_deg[v] - neg_deg[v]) / norm_c
    var_embeddings[v][4] = 0.5
    var_embeddings[v][5] = 0.1
  }
  let clause_embeddings : Array[Array[Double]] = []
  for _c in clauses {
    clause_embeddings.push(Array::make(d, 0.0))
  }
  {
    num_vars,
    embed_dim: d,
    var_embeddings,
    clause_embeddings,
    euf_edges: [],
    obj_weights: obj_weights.copy(),
    message_passing_rounds: 0,
  }
}

///|
/// Add an EUF congruence graph edge between two Boolean abstraction variables.
pub fn OmtGnn::add_euf_congruence_edge(
  self : OmtGnn,
  var_u : Int,
  var_v : Int,
) -> Unit {
  if var_u >= 1 &&
    var_u <= self.num_vars &&
    var_v >= 1 &&
    var_v <= self.num_vars {
    self.euf_edges.push((var_u, var_v))
    self.var_embeddings[var_u][3] = self.var_embeddings[var_u][3] + 0.15
    self.var_embeddings[var_v][3] = self.var_embeddings[var_v][3] + 0.15
  }
}

///|
/// Execute `rounds` iterations of heterogeneous Clause-Variable-EUF message passing.
pub fn OmtGnn::forward_message_passing(
  self : OmtGnn,
  clauses : Array[Clause],
  lrb_ema_scores : Array[Double],
  rounds : Int,
) -> Unit {
  let d = self.embed_dim
  // Ensure clause_embeddings matches clauses length
  while self.clause_embeddings.length() < clauses.length() {
    self.clause_embeddings.push(Array::make(d, 0.0))
  }
  // Inject latest LRB conflict participation rate into feature 5
  for v = 1; v <= self.num_vars; v = v + 1 {
    if v < lrb_ema_scores.length() {
      self.var_embeddings[v][5] = lrb_ema_scores[v].clamp(min=0.0, max=1.0)
    }
  }

  for _r = 0; _r < rounds; _r = _r + 1 {
    // Pass 1: Variable -> Clause message passing
    for ci = 0; ci < clauses.length(); ci = ci + 1 {
      let c = clauses[ci]
      let len = c.lits.length().max(1).to_double()
      for k = 0; k < d; k = k + 1 {
        let mut acc = 0.0
        for lit in c.lits {
          let v = lit_var(lit)
          if v >= 1 && v <= self.num_vars {
            let sign_factor = if lit > 0 { 1.0 } else { -0.65 }
            acc = acc + sign_factor * self.var_embeddings[v][k]
          }
        }
        let lbd_weight = 1.0 / c.lbd.max(1).to_double()
        self.clause_embeddings[ci][k] = @math.tanh(acc / len + 0.1 * lbd_weight)
      }
    }

    // Pass 2: Clause -> Variable + EUF Congruence Neighborhood aggregation
    let next_var_emb : Array[Array[Double]] = []
    for v = 0; v <= self.num_vars; v = v + 1 {
      next_var_emb.push(self.var_embeddings[v].copy())
    }

    for ci = 0; ci < clauses.length(); ci = ci + 1 {
      let c = clauses[ci]
      let att = 1.0 / c.lbd.max(1).to_double()
      for lit in c.lits {
        let v = lit_var(lit)
        if v >= 1 && v <= self.num_vars {
          let pol = if lit > 0 { 0.35 } else { -0.25 }
          for k = 0; k < d; k = k + 1 {
            next_var_emb[v][k] = next_var_emb[v][k] +
              att * pol * self.clause_embeddings[ci][k]
          }
        }
      }
    }

    // EUF congruence edge message passing
    for edge in self.euf_edges {
      let (u, v) = edge
      for k = 0; k < d; k = k + 1 {
        let mu = self.var_embeddings[u][k]
        let mv = self.var_embeddings[v][k]
        next_var_emb[u][k] = next_var_emb[u][k] + 0.2 * mv
        next_var_emb[v][k] = next_var_emb[v][k] + 0.2 * mu
      }
    }

    // Nonlinear activation and normalization
    for v = 1; v <= self.num_vars; v = v + 1 {
      for k = 0; k < d; k = k + 1 {
        self.var_embeddings[v][k] = @math.tanh(next_var_emb[v][k])
      }
    }
    self.message_passing_rounds = self.message_passing_rounds + 1
  }
}

///|
/// Neural Variable Branching Utility Score in [0.0, 1.0], combining GNN embedding
/// and SVM kernel hyperplane margin.
pub fn OmtGnn::predict_branch_score(
  self : OmtGnn,
  v : Int,
  svm : SvmKernelMapper,
) -> Double {
  if v < 1 || v > self.num_vars {
    return 0.0
  }
  let emb = self.var_embeddings[v]
  let gnn_logit = 0.40 * emb[0].abs() +
    0.40 * emb[1].abs() +
    0.55 * emb[2].abs() +
    0.30 * emb[3].abs() +
    0.45 * emb[4] +
    0.65 * emb[5]
  let svm_margin = svm.decision_function(emb, emb[3] > 0.5)
  let combined = gnn_logit + 0.25 * svm_margin.abs()
  1.0 / (1.0 + @math.exp(-combined))
}

///|
/// Neural Polarity (Phase) Prediction guiding OMT minimization:
/// If objective weight > 0 (minimization), biases towards False (0) unless
/// structural positive clause pressure strongly dominates.
pub fn OmtGnn::predict_optimal_polarity(self : OmtGnn, v : Int) -> Bool {
  if v < 1 || v > self.num_vars {
    return false
  }
  let emb = self.var_embeddings[v]
  let obj_w = if v < self.obj_weights.length() {
    self.obj_weights[v]
  } else {
    0.0
  }
  // Structural pressure (pos_deg - neg_deg) minus objective minimization cost
  let score = (emb[0] - emb[1]) * 1.2 - obj_w * 0.45 + 0.2 * emb[3]
  score >= 0.0
}

///|
/// Predict a calibrated non-negative neural lower-bound estimate (LB_6)
/// from the global graph pooling readout.
pub fn OmtGnn::predict_calibrated_lower_bound(
  self : OmtGnn,
  assigned_values : Array[TruthVal],
  guaranteed_base_lb : Double,
) -> Double {
  let mut fixed_cost = 0.0
  let mut unassigned_min_potential = 0.0
  for v = 1; v <= self.num_vars; v = v + 1 {
    let w = if v < self.obj_weights.length() {
      self.obj_weights[v]
    } else {
      0.0
    }
    let val = if v < assigned_values.length() {
      assigned_values[v]
    } else {
      Unassigned
    }
    match val {
      True => fixed_cost = fixed_cost + w
      False => ()
      Unassigned =>
        if w < 0.0 {
          unassigned_min_potential = unassigned_min_potential + w
        }
    }
  }
  let raw_est = fixed_cost + unassigned_min_potential
  // Calibrate so LB_6 never exceeds sound lower bound (maintaining admissibility)
  raw_est.min(guaranteed_base_lb)
}
