/*! Shared testing functionality.

Provides abbreviated syntax for constructing expressions in test cases.
Provides the AST of any examples which are reused across multiple test files.
*/
use glp::ast;
use std::time::Duration;
use ast::{FormulaNode,Formula};
use ast::{ProgramNode,Program};
use ast::{TermNode,Term};
use ast::{DefnNode,Defn};
use ast::LogicProgram;
use ast::{Span, Spanned};

pub fn span<T>(x: T) -> Spanned<T> {
    Spanned { node: x, span: Span::DEFAULT }
}

/* Results of profiling a single item */
pub struct Profile {
  pub steps: i64,
  pub times: Vec<Duration>,
}

impl Profile {
    pub fn new() -> Self {
        Profile {steps: -1, times: vec![]}
    }
    
    pub fn add(&mut self, steps: i64, time: Duration) {
        let mut times = self.times.clone();
        times.push(time);
        *self = Profile{ steps, times }
    }

    pub fn add_single(&mut self, other: &Self) -> () {
        self.steps = self.steps + other.steps;
        self.times[0] = self.times[0] + other.times[0];
    }

    pub fn avg_time(&self) -> Duration {
        let mut acc = Duration::new(0,0);
        for v in &self.times {
            acc = acc + *v;
        }
        acc / (self.times.len().try_into().unwrap())
    }
}

 
/** Value */
pub fn vl(s:&str) -> Box<Term> { Box::new(span(TermNode::ValTerm(s.to_string())))}
/** Variable */
pub fn vr(s:&str) -> Box<Term> { Box::new(span(TermNode::VarTerm(s.to_string())))}

/** Trivially true formula (verum) */
pub fn v() -> Box<Formula> { Box::new(span(FormulaNode::True())) }
/** Predicate */
pub fn p(s:&str) -> Box<Formula> { Box::new(span(FormulaNode::Pred(s.to_string())))}
/** Implication */
pub fn i(p: Box<Formula>, q: Box<Formula>) -> Box<Formula> { Box::new(span(FormulaNode::Imply(p,q)))}
/** And */
pub fn a(p: Box<Formula>, q: Box<Formula>) -> Box<Formula> { Box::new(span(FormulaNode::And(p,q)))}
/** Or */
pub fn o(p: Box<Formula>, q: Box<Formula>) -> Box<Formula> { Box::new(span(FormulaNode::Or(p,q)))}
/** Box */
pub fn b(a: Box<Program>, p: Box<Formula>) -> Box<Formula> { Box::new(span(FormulaNode::MBox(a,p)))}
/** Equality */
pub fn eq(l: Box<Term>, r: Box<Term>) -> Box<Formula> { Box::new(span(FormulaNode::Equal(l,r)))}


/** Symbol */
pub fn s(s:&str) -> Box<Program> { Box::new(span(ProgramNode::Symbol(s.to_string())))}
/** Test */
pub fn t(f:Box<Formula>) -> Box<Program> { Box::new(span(ProgramNode::Test(f)))}
/** Seq */
pub fn seq(a: Box<Program>, b: Box<Program>) -> Box<Program> { Box::new(span(ProgramNode::Seq(a,b)))}
/** Choice */
pub fn u(a: Box<Program>, b: Box<Program>) -> Box<Program> { Box::new(span(ProgramNode::Choice(a,b)))}
/** Loop */
pub fn l(a: Box<Program>, j:Box<Formula>) -> Box<Program> { Box::new(span(ProgramNode::Loop(a,j)))}

/** Program Definition */
pub fn prog(s: &str, a: Box<Program>) -> Box<Defn> { Box::new(span(DefnNode::ProgDefn(s.to_string(), a)))}
/** Predicate Definition */
pub fn pred(p: Box<Formula>) -> Box<Defn> { Box::new(span(DefnNode::PredDefn(vec![*p])))}
/** Predicate Definitions */
pub fn preds(ps: Vec<Box<Formula>>) -> Box<Defn> {
    let mut v : Vec<Formula> = Vec::new();
    for p in ps {
        v.push(*p);
    }
    Box::new(span(DefnNode::PredDefn(v)))
}
/** State Variable Definition */
pub fn sv(s: &str, ss: Vec<&str>) -> Box<Defn> {
    let mut vs : Vec<String>= vec![];
    for sr in ss {
        vs.push(sr.to_string());
    }
    Box::new(span(DefnNode::VarDefn(s.to_string(),vs)))
}

/** Logic program with one definition */
pub fn lp(d:Box<Defn>,q:Box<Formula>) -> Box<LogicProgram> { Box::new(LogicProgram {body: vec![*d], query: q})}
/** Logic program with any number of definitions */
pub fn lps(ds:Vec<Box<Defn>>, q:Box<Formula>) -> Box<LogicProgram> { 
    let mut v : Vec<Defn> = Vec::new();
    for d in ds {
        v.push(*d);
    }
    Box::new(LogicProgram {body: v, query: q})
}

/**  Full-size example from FLOPS2026 paper.
 *  Definitions get resorted during normalization step. */ 
pub fn flops_parsed() -> Box<LogicProgram> {
    let the_vec = 
        vec![
            // angel-turn:  angel-turn ::= (?ab;la U ?bc;la U ?cd;la U ?da;la) U (?ad;ra U ?ba;ra U ?cb;ra U ?dc;ra).
            prog("angel-turn", u(
             u(seq(t(p("ab")),s("la")),u(seq(t(p("bc")),s("la")),u(seq(t(p("cd")),s("la")),seq(t(p("da")),s("la")))))
            ,u(seq(t(p("ad")),s("ra")),u(seq(t(p("ba")),s("ra")),u(seq(t(p("cb")),s("ra")),seq(t(p("dc")),s("ra"))))))),
            // demon-turn:    demon-turn ::= l U r.
            prog("demon-turn",u(s("l"),s("r"))),
            // def of l:  [l]ab <- ac, [l]bc <- bd, [l]cd <- ca, [l]da <- db.
            preds(vec![
                i(p("ac"),b(s("l"),p("ab"))),
                i(p("bd"),b(s("l"),p("bc"))),
                i(p("ca"),b(s("l"),p("cd"))),
                i(p("db"),b(s("l"),p("da")))]),
            // def of la:   [la]db <- ab, [la]ac <- bc, [la]bd <- cd, [la]ca <- da.
            preds(vec![
                i(p("ab"),b(s("la"),p("db"))),
                i(p("bc"),b(s("la"),p("ac"))),
                i(p("cd"),b(s("la"),p("bd"))),
                i(p("da"),b(s("la"),p("ca")))]),
            // def of r:  [r]ad <- ac, [r]ba <- bd, [r]cb <- ca, [r]dc <- db.
            preds(vec![
                i(p("ac"),b(s("r"),p("ad"))),
                i(p("bd"),b(s("r"),p("ba"))),
                i(p("ca"),b(s("r"),p("cb"))),
                i(p("db"),b(s("r"),p("dc")))]),
            // def of ra:   [ra]dd <- ad, [ra]aa <- ba, [ra]bb <- cb, [ra]cc <- dc.
            preds(vec![
                i(p("ad"),b(s("ra"),p("bd"))),
                i(p("ba"),b(s("ra"),p("ca"))),
                i(p("cb"),b(s("ra"),p("db"))),
                i(p("dc"),b(s("ra"),p("ac")))]),

        ];
    // query:  ?- ac -> [(demon-turn;angel-turn)*@inv(ac|bd|ca|db)] (ac|bd|ca|db) 
    let the_query = i(p("ac"),b(l(seq(s("demon-turn"),s("angel-turn")),
        o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))),
        o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))));
    lps(the_vec, the_query)
}