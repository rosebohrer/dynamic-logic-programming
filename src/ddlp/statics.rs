/*! Implement static analyses and static semantics for DDLP.

 These analyses are primarily used to ensure that programs are well-formed before running. */
use crate::ast::{Formula,Program,LogicProgram,Defn,FormulaNode,ProgramNode,DefnNode,Spanned,Span,CompileResult};
use crate::printer_common;
use crate::statics_common;
use FormulaNode::*; use ProgramNode::*; use DefnNode::*;
use std::collections::HashSet;

/** Whether argument is atomic formula */
pub fn is_atom(f: &Formula) -> bool {
   match &f.node {
    Pred(_) => true,
    _ => false,
   }
}

/** Whether argument is a head formula, i.e., atom or box of atoms. */
pub fn is_head(f: &Formula) -> bool {
  match &f.node {
    Pred(_) => true,
    MBox(s, p) => is_atom_program(s) && is_atom(p),
    _ => false,
  }
}

/** Whether argument is atomic program */
pub fn is_atom_program(p: &Program) -> bool {
    match &p.node {
        Symbol(_) => true,
        _ => false,
    }
}

/** Whether argument is clause formula according to Section 3.2 of FLOPS'26
  
 Implements the definition:
   D ::= true | p | G → p | ∀ c D | D1 ∧ D2 | [δ]p
 */
pub fn is_clause(f: &Formula) -> bool {
   match &f.node {
      True() => true,  
      Pred(_) => true,
      Imply(p, q) => is_goal(p) && is_atom(q),
      And(p, q) => is_clause(p) && is_clause(q),
      MBox(a, p) => is_delta(a) && is_atom(p),
      MDiamond(_, _) => false,
      Or(_, _) => false,
      Equal(_, _) => false,
   }
}

/** Whether argument is an implication of head formulas.

That is, determine whether it is suitable as a clause of a predicate implementation.
*/
pub fn is_simple_clause(f: &Formula) -> bool {
   match &f.node {
     Imply(p, q) => is_head(p) && is_simple_clause(q),
     _ => is_head(f),
   }
}

/** Whether argument is goal formula according to Section 3.2 of FLOPS'26
 
Implements the definition:
  G ::= true | p | G1 ∧ G2 | G1 ∨ G2 | ∀ c G | D → G | [γ]G
*/
pub fn is_goal(f: &Formula) -> bool {
   match &f.node {
     True() => true,
     Pred(_) => true,
     Imply(p, q) => is_clause(p) && is_goal(q),
     And(p, q) => is_goal(p) && is_goal(q),
     Or(p, q) => is_goal(p) && is_goal(q),
     MBox(a, p) => is_gamma(a) && is_goal(p),
     MDiamond(_, _) => false,
     Equal(_, _) => false,
   }
}

 /** Whether argument is invariant formula according to Section 3.2 of FLOPS'26

 Implements the definition:
   J ::= true | p | ∀ c J | J → p | J ∧ J | [ι]p 
 */
pub fn is_inv(f: &Formula) -> bool {
   match &f.node {
     True() => true,
     Pred(_) => true,
     Imply(p, q) => is_inv(p) && is_atom(q),
     And(p, q) => is_inv(p) && is_inv(q),
     MBox(a, p) => is_iota(a) && is_atom(p),
     Or(_, _) => false,
     MDiamond(_, _) => false,
     Equal(_, _) => false,
   }
}

/** Whether argument is a disjunction of invariants.

That is, determine whether it is suitable as an invariant annotation on a loop
*/
pub fn is_invs(f: &Formula) -> bool {
   match &f.node {
     Or(p, q) => is_invs(p) && is_invs(q),
     _ => is_inv(f),
   }
}

/** Whether argument is a delta-program (clause program) according to Section 3.2 of FLOPS'26
 
 Implements the definition:
   δ ::= c | ?G | δ1 ∪ δ2 
 */
pub fn is_delta(p: &Program) -> bool {
   match &p.node {
     Symbol(_) => true,
     Test(p) => is_goal(p),
     Choice(a, b) => is_delta(a) && is_delta(b),
     Loop(_, _) => false,
     Seq(_, _) => false,
   }
}
 
/** Whether argument is a gamma-program (goal program) according to Section 3.2 of FLOPS'26
 
Implements the definition
  γ ::= c | ?D | γ1 ∪ γ2 | γ∗@inv(J) | γ1; γ2
*/
pub fn is_gamma(p: &Program) -> bool {
   match &p.node {
    Symbol(_) => true,
    Test(p) => is_clause(p),
    Choice(a, b) => is_gamma(a) && is_gamma(b),
    Loop(a, j) => is_gamma(a) && is_invs(j),
    Seq(a, b) => is_gamma(a) && is_gamma(b),
   }
}
 
/** Whether argument is an iota-program (invariant program) according to Section 3.2 of FLOPS'26
 
Implements the definition
  ι ::= c | ?J | ι ∪ ι | ι∗@inv(J)
*/
pub fn is_iota(p: &Program) -> bool {
   match &p.node {
    Symbol(_) => true,
    Test(p) => is_inv(p),
    Choice(a, b) => is_iota(a) && is_iota(b),
    Loop(a, j) => is_iota(a) && is_invs(j),
    Seq(_, _) => false,
   }
}

/** Given the head of a box predicate, extract program. */
fn head_prog(f: &Formula) -> Program {
    match &f.node {
        MBox(a, _) => *a.clone(),
        _ => { panic!("bug"); }
    }
}

/** Whether program definition follows all well-formedness conditions.

Adds defined program to collection of defined symbols as a side effect. */
pub fn is_well_formed_prog_defn(defined_syms: &mut HashSet<String>, c: &String, a: &Program, span: Span) -> CompileResult<()> {
    if defined_syms.contains(&c.to_string()) {
        // Redundant definitions not allowed 
        let node = format!("Redundant definitions are not allowed, but tried to redefine symbol: {}", c);
        return Err(Spanned{node, span});
    } else if statics_common::FI::of_prog(&a).contains(c) {
        // Recursive definitions not allowed
        let node = format!("Recursive definitions are not allowed, but recursion found in definition of symbol: {}", c);
        return Err(Spanned{node, span});
    } else {
        defined_syms.insert(c.to_string());
        // Program symbols can appear in either clause or goal conditions. 
        // This will require a to be either gamma or delta. However,
        // it would be overly restrictive to require both, so we do not
        // check either condition here, we wait until runtime instead.
        return Ok(());
    }
}

// @TODO: Check whether duplicate symbol checking for box symbols is handled appropriately or not.
// Deduplicate handling of boxes vs. atoms.
/** Whether head formula is a box. 

If so, add it to collection of defined symbols as side effect.*/
fn found_box(clause_syms: &mut HashSet<String>, first_head: &Formula) -> bool {
    if let MBox(s, _) = &first_head.node {
        if let Symbol(c) = &s.node {
            if !clause_syms.contains(&c.to_string())  {
                clause_syms.insert(c.to_string());
                true 
            } else { false }
        } else { false }
    } else { false }
}

/** Whether predicate definition follows all well-formedness conditions.

Adds defined predicate to collection of clause symbols as a side effect. */
pub fn is_well_formed_pred_defn(clause_syms: &mut HashSet<String>, clauses: &Vec<Formula>, span: Span) -> CompileResult<()> {
    if clauses.is_empty() {
        // empty definitions not allowed
        return Err(Spanned{node: "Predicate definition must contain at least one clause.".to_string(), span}); 
    } 
    let first_head = statics_common::conclusion(&clauses[0]);
    let is_head_box = found_box(clause_syms, &first_head);
    for clause in clauses {
        if !is_simple_clause(&clause) {
            let node = format!("Predicates must contain simple clauses of form H1 -> ... -> HN where every formula Hk has either form p or form [c]p.\nInstead, found clause: {}", printer_common::formula(clause));
            return Err(Spanned{node, span: clause.span});
        }
        let second_head = &statics_common::conclusion(&clause);
        match second_head.node {
            Pred(_) if !is_head_box => {
                let concl = statics_common::conclusion(&clause);
                if statics_common::conclusion(&clause) != first_head { 
                    let node = format!("Every clause of the predicate must have the same conclusion.\nMismatch found: {}\nvs. {}", printer_common::formula(&concl), printer_common::formula(&first_head));
                    return Err(Spanned{node, span: clause.span});
                }} ,
            MBox(_, _) if is_head_box => {
                //All branches must define the same symbol, perhaps with different postconditions.
                if head_prog(&statics_common::conclusion(&clause)) != head_prog(&first_head) { 
                    let hp1 = head_prog(&statics_common::conclusion(&clause));
                    let hp2 = head_prog(&first_head);
                    let node = format!("Every clause of the predicate must define the same symbol.\nMismatch found: {} vs. {}", printer_common::program(&hp1), printer_common::program(&hp2));
                    return Err(Spanned{node, span: clause.span});
                }
            },
            _ => { 
                // Cannot mix different head symbols 
                let node = format!("Every clause of predicate must have matching conclusion.\nMismatch found: {}\nvs. {}", printer_common::formula(&first_head), printer_common::formula(second_head));
                return Err(Spanned{node, span: clause.span}); 
            } 
        }
    }
    return Ok(());
}

/** Whether definition follows all well-formedness conditions.

Adds defined identifier to appropriate collection as a side effect. */
pub fn is_well_formed_defn(clause_syms: &mut HashSet<String>, defined_syms: &mut HashSet<String>, d: &Defn) -> CompileResult<()> {
    match &d.node {
        PredDefn(clauses) => is_well_formed_pred_defn(clause_syms, clauses, d.span),
        ProgDefn(c, a) => is_well_formed_prog_defn(defined_syms, c, a, d.span),
        VarDefn(_, _) => return Err(Spanned{node: "Variable definitions only supported in PDLP.".to_string(), span: d.span}),
    }
}

/** Whether query follows all well-formedness conditions. */
pub fn is_well_formed_query(f: &Formula) -> CompileResult<()> {
    if is_goal(f) {
        Ok(())
    } else {
        let node = format!("Query must be goal formula: {}\nGoal formulas are G in the following grammar:\nG ::= true | p | G1 ∧ G2 | G1 ∨ G2 | ∀ c G | D → G | [γ]G\nD ::= true | p | G → p | ∀ c D | D1 ∧ D2 | [δ]p\nδ ::= c | ?G | δ1 ∪ δ2 \nγ ::= c | ?D | γ1 ∪ γ2 | γ∗@inv(J) | γ1; γ2", printer_common::formula(f));
        Err(Spanned{node, span: f.span})
    }
}

/** Whether logic program follows all well-formedness conditions. 
 
This function is intended to be called after parsing and before execution. 
Similarly to a type-checker, it should rule out any syntactically-valid
programs that are not subject to execution. */
pub fn is_well_formed_lp(lp: &LogicProgram) -> CompileResult<()> {
    let mut clause_syms: HashSet<String> = HashSet::new();
    let mut defined_syms: HashSet<String> = HashSet::new();
    // core loop
    for defn in &lp.body {
        match is_well_formed_defn(&mut clause_syms, &mut defined_syms, defn) {
            Ok(_) => (),
            Err(e) => { return Err(e); },
        }
    }
    return is_well_formed_query(&lp.query);
}