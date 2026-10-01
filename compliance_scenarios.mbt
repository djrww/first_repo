///|
/// SMT-LIB 2 compliance examples for the LRA / LIA fragment.
///
/// The examples are the standard textbook / tutorial scripts for quantifier-free linear
/// arithmetic (the shapes used in the SMT-LIB tutorials from CMU 15-217 and the RWTH
/// SMT-SynASC course, plus the canonical integrality-cut contrast between `Int` and `Real`).
/// Each example is parsed by the in-tree SMT-LIB front-end, solved by the CDCL(T) solver,
/// and checked against its expected verdict; the report prints `OK` / `MISMATCH` per case so
/// a regression is visible instead of silently absorbed.

///|
/// One compliance example.
struct ComplianceCase {
  name : String
  /// What the example demonstrates.
  notes : String
  /// The SMT-LIB script, one array entry per line.
  lines : Array[String]
  /// Expected `check-sat` answer.
  expect_sat : Bool
}

fn smt_script(lines : Array[String]) -> String {
  let mut s = ""
  for l in lines {
    s = s + l + "\n"
  }
  s
}

fn compliance_cases() -> Array[ComplianceCase] {
  [
    {
      name: "lia-relative-order",
      notes: "Tutorial shape: an integer strictly larger than another (written as x = y + 2).",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (= x (+ y 2)))",
        "(check-sat)",
        "(get-model)",
      ],
      expect_sat: true,
    },
    {
      name: "lia-bounded-box",
      notes: "Interval bounds on one integer variable.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const x Int)",
        "(assert (>= x 5))",
        "(assert (<= x 9))",
        "(check-sat)",
        "(get-model)",
      ],
      expect_sat: true,
    },
    {
      name: "lia-integrality-cut",
      notes: "The interval [1.4, 1.6] contains no integer: UNSAT over Int.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const x Int)",
        "(assert (>= x 1.4))",
        "(assert (<= x 1.6))",
        "(check-sat)",
      ],
      expect_sat: false,
    },
    {
      name: "lra-same-interval",
      notes: "The same interval over Real is satisfiable: the LIA cut is what differs.",
      lines: [
        "(set-logic QF_LRA)",
        "(declare-const x Real)",
        "(assert (>= x 1.4))",
        "(assert (<= x 1.6))",
        "(check-sat)",
        "(get-model)",
      ],
      expect_sat: true,
    },
    {
      name: "lia-odd-equality",
      notes: "2x = 1 has no integer solution: UNSAT over Int.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const x Int)",
        "(assert (= (* 2 x) 1))",
        "(check-sat)",
      ],
      expect_sat: false,
    },
    {
      name: "lra-dyadic-equality",
      notes: "2x = 1 over Real is satisfiable with x = 0.5.",
      lines: [
        "(set-logic QF_LRA)",
        "(declare-const x Real)",
        "(assert (= (* 2 x) 1))",
        "(check-sat)",
        "(get-model)",
      ],
      expect_sat: true,
    },
    {
      name: "lia-equality-vs-bounds",
      notes: "x = y with x <= 0 and y >= 1 is contradictory by bound propagation alone.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (= x y))",
        "(assert (<= x 0))",
        "(assert (>= y 1))",
        "(check-sat)",
      ],
      expect_sat: false,
    },
    {
      name: "cdclt-boolean-theory-unsat",
      notes: "Boolean structure feeding the theory: p false forces x >= 3, contradicting x <= 0.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const p Bool)",
        "(declare-const x Int)",
        "(assert (or p (>= x 3)))",
        "(assert (not p))",
        "(assert (<= x 0))",
        "(check-sat)",
      ],
      expect_sat: false,
    },
    {
      name: "cdclt-boolean-theory-sat",
      notes: "Same shape, satisfiable: p false forces x >= 3 and x >= 0 is harmless.",
      lines: [
        "(set-logic QF_LIA)",
        "(declare-const p Bool)",
        "(declare-const x Int)",
        "(assert (or p (>= x 3)))",
        "(assert (not p))",
        "(assert (>= x 0))",
        "(check-sat)",
        "(get-model)",
      ],
      expect_sat: true,
    },
  ]
}

///|
/// Run every compliance example and return a text report with per-case verdicts, models and
/// search telemetry.
pub fn run_lra_lia_compliance_scenario() -> String {
  let mut report = "=== SMT-LIB 2 compliance examples: LRA / LIA fragment ===\n"
  let mut passed = 0
  let mut mismatches = 0
  let mut parse_errors = 0
  for case in compliance_cases() {
    report = report + "\n--- " + case.name + " ---\n"
    report = report + case.notes + "\n"
    report = report + smt_script(case.lines)
    match parse_smtlib(smt_script(case.lines)) {
      None => {
        report = report + "  result: PARSE ERROR\n"
        parse_errors = parse_errors + 1
      }
      Some(problem) => {
        let solver = CdcltSolver::from_problem(problem)
        let res = solver.solve(compliance_conflict_budget)
        let verdict = if res.satisfiable {
          "sat"
        } else if res.unknown {
          "unknown"
        } else {
          "unsat"
        }
        let expected = if case.expect_sat { "sat" } else { "unsat" }
        let status = if verdict == expected { "OK" } else { "MISMATCH" }
        if verdict == expected {
          passed = passed + 1
        } else {
          mismatches = mismatches + 1
        }
        report = report + "  parsed  : " + problem.summary() + "\n"
        report = report + "  verdict : expected " + expected + ", got " + verdict +
          " [" + status + "]\n"
        if res.satisfiable {
          report = report + res.model_text
          report = report + "  witness : "
          for i = 0; i < res.arith_model.length(); i = i + 1 {
            report = report + "a" + "\{i}" + "=" + "\{res.arith_model[i]}" + " "
          }
          report = report + "\n"
        }
        report = report + "  search  : " + "\{res.conflicts}" + " conflicts, " +
          "\{res.decisions}" + " decisions, " + "\{res.propagations}" +
          " propagations, " + "\{res.theory_conflicts}" + " theory conflicts, " +
          "\{res.learnt_clauses}" + " learnt clauses\n"
        report = report + "  graph   : " + "\{res.graph_nodes}" + " nodes, " +
          "\{res.graph_violations}" + " violations, " +
          "\{res.learnt_clause_failures}" + " invariant fallbacks, " +
          "\{res.lbd_certification_failures}" + " LBD certification failures\n"
      }
    }
  }
  report = report + "\n" + "\{passed}" + " / " + "\{compliance_cases().length()}" +
    " examples matched their expected verdict"
  if mismatches > 0 {
    report = report + " (" + "\{mismatches}" + " mismatch(es))"
  }
  if parse_errors > 0 {
    report = report + ", " + "\{parse_errors}" + " parse error(s)"
  }
  report = report + ".\n"
  report
}

///|
/// A small QF_LIA problem whose first branch is wrong, so the search really learns from a
/// conflict: x is pinned to 2, the disjunction (x >= 3 or x <= 1) must fail on both sides.
pub fn conflict_graph_script() -> String {
  smt_script([
    "(set-logic QF_LIA)",
    "(declare-const x Int)",
    "(assert (or (>= x 3) (<= x 1)))",
    "(assert (>= x 2))",
    "(assert (<= x 2))",
    "(check-sat)",
  ])
}

///|
/// Deliverable for the "conflict graph" feature: solve the backtracking example, verify the
/// recorded implication graph, and return `(report, svg)`. The SVG can be written to a file
/// by the caller (`main` prints it between markers).
pub fn run_conflict_graph_scenario() -> (String, String) {
  let script = conflict_graph_script()
  let mut report = "=== CDCL(T) implication / conflict graph ===\n"
  report = report + script
  match parse_smtlib(script) {
    None => {
      report = report + "PARSE ERROR\n"
      (report, "")
    }
    Some(problem) => {
      let solver = CdcltSolver::from_problem(problem)
      let res = solver.solve(compliance_conflict_budget)
      let verdict = if res.satisfiable {
        "sat"
      } else if res.unknown {
        "unknown"
      } else {
        "unsat"
      }
      let graph_ok = solver.graph.verify()
      report = report + "  verdict        : " + verdict + " (expected unsat)\n"
      report = report + "  conflicts      : " + "\{res.conflicts}" + "\n"
      report = report + "  decisions      : " + "\{res.decisions}" + "\n"
      report = report + "  theory checks  : " + "\{res.theory_conflicts}" +
        " theory conflict(s)\n"
      report = report + "  learnt clauses : " + "\{res.learnt_clauses}" + "\n"
      report = report + "  graph nodes    : " + "\{res.graph_nodes}" + "\n"
      report = report + "  graph verify   : " + "\{graph_ok}" + " (" +
        "\{res.graph_violations}" + " violation(s))\n"
      report = report + "  invariant fallbacks: " + "\{res.learnt_clause_failures}" +
        "\n"
      report = report + "  LBD certification   : " +
        "\{res.lbd_certification_failures}" + " failure(s)\n"
      report = report + "  decision nodes : " + "\{solver.graph.decisions}" + "\n"
      report = report + "  implied nodes  : " + "\{solver.graph.implications}" +
        "\n"
      report = report + "  SVG bytes      : " + "\{res.graph_svg.length()}" + "\n"
      (report, res.graph_svg)
    }
  }
}
