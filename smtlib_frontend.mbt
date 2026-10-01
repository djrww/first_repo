///|
/// Minimal SMT-LIB 2 front-end.
///
/// Parses the subset of the SMT-LIB 2 language needed for the linear arithmetic compliance
/// examples: `set-logic`, `declare-const` (Bool / Int / Real), `assert`, `check-sat`,
/// `get-model`, `exit`, and the core operators `and`, `or`, `not`, `=>`, `=`, `<`, `<=`,
/// `>`, `>=`, `+`, `-`, `*` (linear uses only). Unknown commands are skipped in a
/// balanced way and reported in `unsupported_commands`; anything that cannot be modelled
/// (unknown sorts, non-linear terms, function declarations with arguments) produces a parse
/// error and the caller must not trust the result.
///
/// The parser is deliberately self-contained: it works on `String::to_array()` and builds
/// numerals digit by digit, so it does not depend on locale- or backend-specific string
/// conversion routines.

///|
/// SMT-LIB sorts supported by this front-end.
pub(all) enum SmtSort {
  BoolSort
  IntSort
  RealSort
} derive(Eq)

///|
/// A parsed SMT-LIB expression.
pub(all) enum SmtExpr {
  SmtBoolLit(Bool)
  SmtNumLit(Double)
  /// Index into `SmtProblem.decls`.
  SmtSymRef(Int)
  /// Operator application (including nullary symbols such as `true`, which are turned into
  /// literals during parsing).
  SmtApply(String, Array[SmtExpr])
}

///|
/// One `declare-const` declaration. Exactly one of `bool_var` / `arith_index` is set.
pub(all) struct SmtDecl {
  name : String
  sort : SmtSort
  /// 1-based Boolean variable id, or -1 for arithmetic declarations.
  bool_var : Int
  /// 0-based arithmetic variable index, or -1 for Boolean declarations.
  arith_index : Int
}

///|
/// A parsed SMT-LIB problem (declarations plus the top-level assertions).
pub(all) struct SmtProblem {
  logic : String
  decls : Array[SmtDecl]
  num_bool_vars : Int
  num_arith_vars : Int
  /// Whether each arithmetic variable was declared `Int` (true) or `Real` (false).
  is_integer : Array[Bool]
  assertions : Array[SmtExpr]
  /// Commands that were skipped because this front-end does not model them.
  unsupported_commands : Array[String]
  /// Hard errors; a problem with a non-empty list must not be solved.
  parse_errors : Array[String]
}

///|
/// Names of the declarations in order, for reporting.
pub fn SmtProblem::decl_names(self : SmtProblem) -> Array[String] {
  let out : Array[String] = []
  for d in self.decls {
    out.push(d.name)
  }
  out
}

///|
/// Split SMT-LIB text into tokens: parentheses are single tokens, `;` starts a comment that
/// runs to the end of the line, and `"..."` string literals are kept as one token.
fn smtlib_tokenize(text : String) -> Array[String] {
  let chars = text.to_array()
  let tokens : Array[String] = []
  let n = chars.length()
  let mut i = 0
  while i < n {
    let c = chars[i]
    if c.is_ascii_whitespace() {
      i = i + 1
    } else if c == ';' {
      while i < n && chars[i] != '\n' {
        i = i + 1
      }
    } else if c == '(' || c == ')' {
      tokens.push(String::from_array([c]))
      i = i + 1
    } else if c == '"' {
      let start = i
      i = i + 1
      while i < n && chars[i] != '"' {
        i = i + 1
      }
      if i < n {
        i = i + 1
      }
      tokens.push(String::from_array(chars[start:i]))
    } else {
      let start = i
      while i < n &&
            !chars[i].is_ascii_whitespace() &&
            chars[i] != '(' &&
            chars[i] != ')' &&
            chars[i] != ';' {
        i = i + 1
      }
      tokens.push(String::from_array(chars[start:i]))
    }
  }
  tokens
}

///|
/// Numeric value of an ASCII digit character, or -1 when `c` is not a digit.
fn smt_char_digit_value(c : Char) -> Int {
  if c == '0' {
    0
  } else if c == '1' {
    1
  } else if c == '2' {
    2
  } else if c == '3' {
    3
  } else if c == '4' {
    4
  } else if c == '5' {
    5
  } else if c == '6' {
    6
  } else if c == '7' {
    7
  } else if c == '8' {
    8
  } else if c == '9' {
    9
  } else {
    -1
  }
}

///|
/// Parse a non-negative decimal numeral (`12`, `1.5`, `0.25`), or `None` when `s` is not a
/// numeral. SMT-LIB numerals are unsigned; negation is written `(- x)`.
fn smt_parse_numeral(s : String) -> Double? {
  if s.length() == 0 {
    return None
  }
  let chars = s.to_array()
  let mut value = 0.0
  let mut frac_scale = 0.1
  let mut in_frac = false
  let mut digits = 0
  for i = 0; i < chars.length(); i = i + 1 {
    let c = chars[i]
    if c == '.' {
      if in_frac {
        return None
      }
      in_frac = true
    } else {
      let d = smt_char_digit_value(c)
      if d < 0 {
        return None
      }
      digits = digits + 1
      let dv = d.to_double()
      if in_frac {
        value = value + dv * frac_scale
        frac_scale = frac_scale * 0.1
      } else {
        value = value * 10.0 + dv
      }
    }
  }
  if digits == 0 {
    None
  } else {
    Some(value)
  }
}

///|
/// Recursive-descent parser state over a token array.
struct SmtParser {
  tokens : Array[String]
  mut pos : Int
  errors : Array[String]
}

fn SmtParser::new(tokens : Array[String]) -> SmtParser {
  { tokens, pos: 0, errors: [] }
}

fn SmtParser::peek(self : SmtParser) -> String {
  if self.pos < self.tokens.length() {
    self.tokens[self.pos]
  } else {
    ""
  }
}

fn SmtParser::advance(self : SmtParser) -> String {
  let t = self.peek()
  if self.pos < self.tokens.length() {
    self.pos = self.pos + 1
  }
  t
}

fn SmtParser::expect(self : SmtParser, tok : String) -> Bool {
  if self.peek() == tok {
    self.pos = self.pos + 1
    true
  } else {
    self.errors.push("expected \{tok} at token \{self.pos}")
    false
  }
}

///|
/// Parse one expression; `decls` is used to resolve symbols to declaration indices.
fn SmtParser::parse_expr(self : SmtParser, decls : Array[SmtDecl]) -> SmtExpr? {
  let tok = self.peek()
  if tok == "" {
    self.errors.push("unexpected end of input")
    return None
  }
  if tok == "(" {
    self.pos = self.pos + 1
    let op = self.advance()
    let args : Array[SmtExpr] = []
    let mut ok = true
    while self.peek() != ")" && self.pos < self.tokens.length() && ok {
      match self.parse_expr(decls) {
        Some(a) => args.push(a)
        None => ok = false
      }
    }
    if !self.expect(")") {
      ok = false
    }
    if !ok {
      return None
    }
    return Some(SmtApply(op, args))
  }
  self.pos = self.pos + 1
  if tok == "true" {
    return Some(SmtBoolLit(true))
  }
  if tok == "false" {
    return Some(SmtBoolLit(false))
  }
  match smt_parse_numeral(tok) {
    Some(d) => return Some(SmtNumLit(d))
    None => ()
  }
  for i = 0; i < decls.length(); i = i + 1 {
    if decls[i].name == tok {
      return Some(SmtSymRef(i))
    }
  }
  self.errors.push("unknown symbol \{tok}")
  None
}

///|
/// Parse an SMT-LIB script. Returns `None` when the script contains a hard error
/// (unbalanced parentheses, unsupported sort, unknown symbol, non-numeral literal);
/// unsupported *commands* are politely skipped and recorded instead.
pub fn parse_smtlib(text : String) -> SmtProblem? {
  let parser = SmtParser::new(smtlib_tokenize(text))
  let decls : Array[SmtDecl] = []
  let assertions : Array[SmtExpr] = []
  let unsupported : Array[String] = []
  let is_integer : Array[Bool] = []
  let mut logic = "UNKNOWN"
  let mut num_bool = 0
  let mut num_arith = 0
  while parser.pos < parser.tokens.length() {
    if !parser.expect("(") {
      break
    }
    let cmd = parser.advance()
    match cmd {
      "set-logic" => {
        logic = parser.advance()
        let _ = parser.expect(")")
      }
      "declare-const" => {
        let name = parser.advance()
        let sort_tok = parser.advance()
        let _ = parser.expect(")")
        if sort_tok == "Bool" {
          num_bool = num_bool + 1
          decls.push({
            name,
            sort: BoolSort,
            bool_var: num_bool,
            arith_index: -1,
          })
        } else if sort_tok == "Int" || sort_tok == "Real" {
          let is_int = sort_tok == "Int"
          decls.push({
            name,
            sort: if is_int { IntSort } else { RealSort },
            bool_var: -1,
            arith_index: num_arith,
          })
          is_integer.push(is_int)
          num_arith = num_arith + 1
        } else {
          parser.errors.push("unsupported sort \{sort_tok} in (declare-const \{name} ...)")
        }
      }
      "assert" => {
        match parser.parse_expr(decls) {
          Some(e) => assertions.push(e)
          None => ()
        }
        let _ = parser.expect(")")
      }
      "check-sat" | "get-model" | "exit" => {
        let _ = parser.expect(")")
      }
      _ => {
        // Skip the whole command, counting parentheses so a nested command cannot
        // desynchronise the stream.
        unsupported.push(cmd)
        let mut depth = 1
        while depth > 0 && parser.pos < parser.tokens.length() {
          let t = parser.advance()
          if t == "(" {
            depth = depth + 1
          } else if t == ")" {
            depth = depth - 1
          }
        }
      }
    }
  }
  if parser.errors.length() > 0 {
    return None
  }
  {
    logic,
    decls,
    num_bool_vars: num_bool,
    num_arith_vars: num_arith,
    is_integer,
    assertions,
    unsupported_commands: unsupported,
    parse_errors: [],
  }
}

///|
/// Human-readable one-line summary of a parsed problem, used in compliance reports.
pub fn SmtProblem::summary(self : SmtProblem) -> String {
  "\{self.logic}: \{self.num_bool_vars} Bool, \{self.num_arith_vars} arithmetic, \{self.assertions.length()} assertion(s), \{self.unsupported_commands.length()} skipped command(s)"
}
