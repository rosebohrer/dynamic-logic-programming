/*! Implement static analyses and static semantics for DDLP.

 These analyses are primarily used to ensure that programs are well-formed before running. */
use crate::ast::{Formula,Program,FormulaNode,ProgramNode};
use FormulaNode::*; use ProgramNode::*;

/** Implements the definition A ::= pred | true */
pub fn is_atom(f: &Formula) -> bool {
   match &f.node {
    True() => true,
    Pred(_) => true,
    _ => false,
   }
}

/** Implements the definition AV ::= A | AV & AV */
pub fn is_atoms(f: &Formula) -> bool {
   match &f.node {
    And(p, q) => is_atoms(p) && is_atoms(q),
    _ => is_atom(f),
   }
}

/** Implements the definition invs ::= \/AV */
pub fn is_loop_invariants(f: &Formula) -> bool {
   match &f.node {
    Or(p, q) => is_loop_invariants(p) && is_loop_invariants(q),
    _ => is_atoms(f),
   }
}

/** Implements the definition G ::= A | G1 & G2 | G1 \/ G2 | A -> G | <\gamma<>>G | [\gamma[]]G */
pub fn is_goal(f: &Formula) -> bool {
   match &f.node {
     True() => true,
     Pred(_) => true, 
     Equal(_, _) => true,
     And(p, q)=> is_goal(p) && is_goal(q),
     Or(p, q) => is_goal(p) && is_goal(q),
     Imply(p, q) => is_atom(p) && is_goal(q),
     MBox(a, p) => is_box_goal_prog(a) && is_goal(p),
     MDiamond(a, p) => is_diamond_goal_prog(a) && is_goal(p),
   }
}

/** Implements the definition D ::= A | G -> D | D1 /\ D2 | <\delta<>>AV | [\delta[]]AV */
pub fn is_clause(f: &Formula) -> bool {
   match &f.node {
     True() => true,
     Pred(_) => true, 
     Equal(_, _) => true,
     And(p, q)=> is_clause(p) && is_clause(q),
     Or(_, _) => false,
     Imply(p, q) => is_goal(p) && is_clause(q),
     MBox(a, p) => is_box_clause_prog(a) && is_atoms(p),
     MDiamond(a, p) => is_diamond_clause_prog(a) && is_atoms(p),
   }
}

/** Implements the definition \delta[] ::= c | \delta[]; \delta[] | \delta[] U \delta[] | \delta[]*@inv(\/ AV) | ?A */
pub fn is_box_goal_prog(p: &Program) -> bool {
    match &p.node {
     Symbol(_) => true,
     Seq(a, b) => is_box_goal_prog(a) && is_box_goal_prog(b),
     Choice(a, b) => is_box_goal_prog(a) && is_box_goal_prog(b),
     Loop(a, j) => is_box_goal_prog(a) && is_loop_invariants(j),
     Test(p) => is_atom(p),
    }
}

/** Implements the definition \delta<>::= c | \delta<>; \delta<> | \delta<> U \delta<> | \delta<>* | ?G */
pub fn is_diamond_goal_prog(p: &Program) -> bool {
    match &p.node {
     Symbol(_) => true,
     Seq(a, b) => is_diamond_goal_prog(a) && is_diamond_goal_prog(b),
     Choice(a, b) => is_diamond_goal_prog(a) && is_diamond_goal_prog(b),
     Test(p) => is_goal(p),
     Loop(a, j) => is_diamond_goal_prog(a) && True() == j.node,
    }
}

/** Implements the definition \gamma[] ::= c | \gamma[]; \gamma[] | \gamma[] U \gamma[] | ?G */
pub fn is_box_clause_prog(p: &Program) -> bool {
    match &p.node {
     Symbol(_) => true,
     Seq(a, b) => is_box_clause_prog(a) && is_box_clause_prog(b),
     Choice(a, b) => is_box_clause_prog(a) && is_box_clause_prog(b),
     Test(p) => is_goal(p),
     Loop(_, _) => false,
    }
}

/** Implements the definition \gamma<> ::= c | \gamma[]; \gamma[] | ?A */
pub fn is_diamond_clause_prog(p: &Program) -> bool {
    match &p.node {
     Symbol(_) => true,
     Seq(a, b) => is_diamond_clause_prog(a) && is_diamond_clause_prog(b),
     Test(p) => is_atom(p),
     Choice(_, _) => false,
     Loop(_, _) => false,
    }
}