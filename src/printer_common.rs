/*! Pretty-printing functions for abstract syntax.

Pretty-printing is the inverse operation of parsing, converting abstract syntax 
to concrete syntax. Parsing the output of printing should result in the original
abstract syntax. Though the converse does not hold, printing after parsing should
produce a semantically equivalent program.

Ease of implementation is prioritized over runtime efficiency and readability of 
the resulting text. Strings are appended recursively, resulting in quadratic
complexity in the worst case. For this reason, printing large texts with this
function should be avoided during performance measurements. Strings are fully
parenthesized, but a smarter algorithm could consult the relative precedence
of each operation to omit parentheses when they are redundant.
*/
use crate::ast::{Formula,Program,Term, LogicProgram,Defn,FormulaNode,ProgramNode,DefnNode,TermNode};
use FormulaNode::*; use ProgramNode::*; use DefnNode::*; use TermNode::*;

/** Pretty-print a term */
pub fn term(trm: &Term) -> String {
  let mut s = "(".to_string();
  match &trm.node {
    ValTerm(v) => {s.push_str("'"); s.push_str(v)},
    VarTerm(x) => {s.push_str(x)},
  }
  s.push_str(")");
  s
}

/** Pretty-print a formula. */
pub fn formula(fml: &Formula) -> String {
  let mut s = "(".to_string();
  match &fml.node {
    True() => s.push_str("true"),
    Pred(ps) => s.push_str(&ps.clone()),
    Equal(e1, e2) => {
      s.push_str(&term(e1));
      s.push_str("=");
      s.push_str(&term(e2));
    }
    Imply(p, q) => {
        s.push_str(&formula(p));
        s.push_str("->");
        s.push_str(&formula(q))
    },
    And(p, q) => {
        s.push_str(&formula(p));
        s.push_str("&");
        s.push_str(&formula(q))
    },
    Or(p, q) => {
        s.push_str(&formula(p));
        s.push_str("|");
        s.push_str(&formula(q))
    },
    MBox(a, p) => {
        s.push_str("[");
        s.push_str(&program(a));
        s.push_str("]");
        s.push_str(&formula(p))
    },
    MDiamond(a, p) => {
        s.push_str("<");
        s.push_str(&program(a));
        s.push_str(">");
        s.push_str(&formula(p));
    }
  }
  s.push_str(")");
  s
}

/** Pretty-print a program from PDL. */
pub fn program(prog: &Program) -> String {
  let mut s = "(".to_string();
  match &prog.node {
    Symbol(ss) => s.push_str(&ss.clone()),
    Test(p) => {
        s.push_str("?");
        s.push_str(&formula(p))
    },
    Seq(a, b) => {
        s.push_str(&program(a));
        s.push_str(";");
        s.push_str(&program(b))
    },
    Choice(a, b) => {
        s.push_str(&program(a));
        s.push_str("U");
        s.push_str(&program(b))
    },
    Loop(a, j) => {
        s.push_str(&program(a));
        s.push_str("*@inv(");
        s.push_str(&formula(j));
        s.push_str(")")
    },
  }
  s.push_str(")");
  s
}

/** Pretty-print a definition. */
pub fn defn(d: &Defn) -> String {
  match &d.node {  
    ProgDefn(c, a) => {
        let mut s = "\n".to_string();
        s.push_str(&c.clone());
        s.push_str(" ::= ");
        s.push_str(&program(a));
        s.push_str(".");
        s
    },
    PredDefn(clauses) => {
        let mut s = formula(&clauses[0]);
        for i in 1..clauses.len() {
            s.push_str(".\n");
            s.push_str(&formula(&clauses[i]));
        }
        s.push_str(".");
        s
    },
    // q : enum {q0,q1,q2,q3,q4,q5}.
    VarDefn(x, vs) => {
        let mut s = "\n".to_string();
        s.push_str(x);
        s.push_str(" : enum {");
        s.push_str(&vs[0]);
        for i in 1..vs.len() {
          s.push_str(",");
          s.push_str(&vs[i]);
        }
        s.push_str("}.");
        s
    }
  }
}

/** Pretty print a logic program, both body and query. */
pub fn logic_program(lp: &LogicProgram) -> String {
  let mut s = "".to_string();
  for d in &lp.body {
    s.push_str(&defn(d));
  }
  s.push_str("\n\n?- ");
  s.push_str(&formula(&lp.query));
  s
}
