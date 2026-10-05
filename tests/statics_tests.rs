/** Tests the statics module. */

pub mod common;
use glp::statics_common;
use glp::ddlp::statics;
use glp::{ast,parser};
use ast::{Span,LogicProgram,FormulaNode};
use common::*;
    
#[cfg(test)]
mod tests {
    use super::*;

    use parser::pdlp::defns as parseds;

    /** Atom is atom */
    #[test]
    fn is_atom_yes() { assert!(statics::is_atom(&p("hello"))); }

    /** Box is not atom */
    #[test]
    fn is_atom_no() { assert!(!statics::is_atom(&b(s("a"),p("b")))); }

    /** Symbol is atom program */
    #[test]
    fn is_atom_program_yes() { assert!(statics::is_atom_program(&s("hello")));}

    /** Test is not atom program */
    #[test]
    fn is_atom_program_no() { assert!(!statics::is_atom_program(&t(p("a")))); }

    /** Implication of predicates is clause */
    #[test]
    fn is_clause_yes() { assert!(statics::is_clause(&i(p("a"), p("b")))); }

    /** Implication of disjunctions is not a clause */
    #[test]
    fn is_clause_no() { assert!(!statics::is_clause(&i(o(p("a"),p("b")),o(p("c"),p("d"))))); }

    /** Conjunction of predicates is goal. */
    #[test]
    fn is_goal_yes() { assert!(statics::is_goal(&a(p("a"), p("b")))); }

    /** Implication of disjunctions is not a goal */
    #[test]
    fn is_goal_no() { assert!(!statics::is_goal(&i(o(p("a"),p("b")),o(p("c"),p("d"))))); }

    /** Predicate is invariant */
    #[test]
    fn is_inv_yes() { assert!(statics::is_inv(&p("ab"))); }

    /** Disjunction is not invariant */
    #[test]
    fn is_inv_no() { assert!(!statics::is_inv(&o(p("cd"),p("ab")))); }

    /** Disjunction is disjunction-of-invariants */
    #[test]
    fn is_invs_yes() { assert!(statics::is_invs(&o(p("cd"),p("ab")))); }

    /** Implication of disjunctions is not disjunction-of-invariants */
    #[test]
    fn is_invs_no() { assert!(!statics::is_invs(&i(o(p("a"),p("b")),o(p("c"),p("d"))))); }

    /** Test of predicate is gamma-program */
    #[test]
    fn is_gamma_yes() { assert!(statics::is_gamma(&t(p("a")))); }

    /** Test of disjunction is not gamma-program */
    #[test]
    fn is_gamma_no() { assert!(!statics::is_gamma(&t(o(p("a"),p("b"))))); }

    /** Test of predicate is delta-program */
    #[test]
    fn is_delta_yes() { assert!(statics::is_delta(&t(p("a")))); }

    /** Seq is not delta program */
    #[test]
    fn is_delta_no() { assert!(!statics::is_delta(&seq(s("a"),s("b")))); }

    /** Test of predicate is iota-program */
    #[test]
    fn is_iota_yes() { assert!(statics::is_iota(&t(p("a")))); }

    /** Seq is not iota-program */
    #[test]
    fn is_iota_no() { assert!(!statics::is_iota(&seq(s("a"),s("b")))); }

    /** Atomic predicate is head formula */
    #[test]
    fn is_head_atom() { assert!(statics::is_head(&p("foo"))); }

    /** Box predicate is head formula */
    #[test]
    fn is_head_box() { assert!(statics::is_head(&b(s("a"), p("foo")))); }

    /** Imply is not head formula */
    #[test]
    fn not_head_imply() { assert!(!statics::is_head(&i(p("a"),p("b")))); }

    /** implication of box predicate is simple clause */
    #[test]
    fn is_simple_clause_yes() { assert!(statics::is_simple_clause(&i(p("ab"),b(s("c"),p("d"))))); }

    /** Nested conjunction breaks apart */
    #[test]
    fn conjuncts4() {
        let four_fmls: Vec<ast::Formula> = vec![*p("a"), *p("b"), *p("c"), *p("d")];
        assert_eq!(statics_common::conjuncts(&a(a(p("a"),p("b")),a(p("c"),p("d")))), four_fmls);
    }

    /** Nested disjunction breaks apart */
    #[test]
    fn disjuncts4() {
        let four_fmls: Vec<ast::Formula> = vec![*p("a"), *p("b"), *p("c"), *p("d")];
        assert_eq!(statics_common::disjuncts(&o(o(p("a"),p("b")),o(p("c"),p("d")))), four_fmls);
    }

    /** Nested choice breaks apart */
    #[test]
    fn choices4() {
        let four_progs: Vec<ast::Program> = vec![*s("a"), *s("b"), *s("c"), *s("d")];
        assert_eq!(statics_common::choices(&u(u(s("a"),s("b")),u(s("c"),s("d")))), four_progs);
    }

    /** Multiple assumptions are collected */
    #[test]
    fn assumptions4() {
        let four_fmls: Vec<ast::Formula> = vec![*p("a"), *p("b"), *p("c"), *p("d")];
        assert_eq!(statics_common::assumptions(&i(p("a"), i(p("b"), i(p("c"), i(p("d"),p("e")))))), four_fmls);
    }

    /** Nested implication's conclusion is found */
    #[test]
    fn conclusion() { assert_eq!(statics_common::conclusion(&i(p("a"), i(p("b"), i(p("c"), i(p("d"),p("e")))))), *p("e")); }

    /** Identifiers of formula are collected */
    #[test]
    fn of_formula() { assert!(statics_common::FI::of_formula(&a(a(p("a"),p("b")),a(p("c"),p("d")))).contains(&"a".to_string())); }

    /** Identifiers of program are collected */
    #[test]
    fn of_prog() {
        assert!(statics_common::FI::of_prog(&l(seq(s("demon-turn"),s("angel-turn")),
            o(p("ac"),o(p("bd"),o(p("ca"),p("db")))))).contains(&"demon-turn".to_string()));
    }

    /** Small example passes all well-formedness checks */
    #[test]
    fn well_formed_mini() {
        let mini_parsed = 
        lps(vec![
            preds(vec![
                    i(p("db"),b(s("l"),p("da")))
                    ]),], 
            i(p("ac"),b(l(seq(s("demon-turn"),s("angel-turn")),
            o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))),
            o(p("ac"),o(p("bd"),o(p("ca"),p("db")))))));
        assert_eq!(statics::is_well_formed_lp(&mini_parsed), Ok(()));
    }
 
    /** Test parsing and normalization of predicate with multiple clauses */
    #[test]
    fn normalize_two_defns()  {
        let t = ast::respan(Span::DEFAULT, FormulaNode::True());
        let lp = LogicProgram { body: parseds("[d]c <- a. [d]c <- b.").unwrap(), query: Box::new(t)};
        let norm = statics_common::normalize(lp);
        assert_eq!(norm.unwrap().body, vec![*preds(vec![i(p("a"),b(s("d"),p("c"))),i(p("b"),b(s("d"),p("c")))])]);
    }

    /** Full FLOPS'2026 paper example passes all well-formedness checks */
    #[test]
    fn well_formed_full() {
        assert_eq!(statics::is_well_formed_lp(&flops_parsed()), Ok(()));
    }
}