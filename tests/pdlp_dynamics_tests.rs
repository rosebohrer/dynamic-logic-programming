/** Test the dynamics module by running sample programs. */
pub mod common;

use glp::{parser,examples,ast,statics_common};
use glp::pdlp::dynamics;
//use glp::pdlp::printer;
//use glp::command_line::CommandLineArgs;
use dynamics::{StaticMachine,Machine,Goal};
use common::*;

#[cfg(test)]
mod tests {
    use super::*;
    use parser::pdlp::logic_program as parselp;

    /** New machine should not be proved */
    #[test]
    fn new_machine_not_proved() {
        let sm = StaticMachine::new();
        let m = Machine::new(&sm);
        assert!(!m.is_proved());
    }

    /** Create logic program with empty body and given query */
    fn lp_emp(b: Box<ast::Formula>) -> ast::LogicProgram {
        ast::LogicProgram { body: vec![], query: b }
    }
        
    /** Test conversion of logic program data structure to machine structure */
    #[test]
    fn machine_of_lp() {
        let mut sm = StaticMachine::new();
        let m_flops = Machine::of_lp(&mut sm, &flops_parsed());
        assert_eq!(m_flops.sm.prog_defns.len(), 2);
        assert_eq!(m_flops.sm.prog_defns.get("demon-turn"),Some(u(s("l"),s("r"))).as_deref());
        assert_eq!(m_flops.sm.atom_preds.len(), 0);
        assert_eq!(m_flops.sm.box_preds.len(), 4);
        let Some (def_of_l) = m_flops.sm.box_preds.get("l") else { panic!("Bad test") };
        assert_eq!(def_of_l[0], *i(p("ac"),b(s("l"),p("ab"))));
        assert_eq!(def_of_l[1], *i(p("bd"),b(s("l"),p("bc"))));
        assert_eq!(def_of_l[2], *i(p("ca"),b(s("l"),p("cd"))));
        assert_eq!(def_of_l[3], *i(p("db"),b(s("l"),p("da"))));
        let flops_goal = Goal { assumps: vec![*p("ac")], concl: *b(l(seq(s("demon-turn"),s("angel-turn")),
            o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))),
            o(p("ac"),o(p("bd"),o(p("ca"),p("db")))))};
        assert_eq!(m_flops.dm.goals[0], flops_goal);
        assert_eq!(m_flops.dm.goals.len(), 1);
    }

    /** Empty program steps to completed proof. */
    #[test]
    fn step_true() {
        let lp_true = lp_emp(v());
        let mut sm = StaticMachine::new();
        let mut m_true = Machine::of_lp(&mut sm, &lp_true);
        let true_succs  = m_true.steps();
        assert_eq!(true_succs.len(), 1);
        assert_eq!(true_succs[0].sm.prog_defns.len(), 0);
        assert_eq!(true_succs[0].sm.atom_preds.len(), 0);
        assert_eq!(true_succs[0].sm.box_preds.len(), 0);
        assert_eq!(true_succs[0].dm.goals.len(), 0);
        assert!(true_succs[0].is_proved());
    }

    /** If assumption is in the context, proof closes in one step */
    #[test]
    fn step_assump_closes() {
        let lp_init = lp_emp(i(p("a"),i(p("b"), i(p("c"), p("b")))));
        let mut sm = StaticMachine::new();
        let init_succs = Machine::of_lp(&mut sm, &lp_init).steps();
        assert_eq!(init_succs.len(), 1);
        assert_eq!(init_succs[0].dm.goals.len(), 0);
    }

    /** Stuck machine should have 0 successors, as opposed to succ with 0 goals */
    #[test]
    fn step_stuck() {
        let lp_stuck = lp_emp(i(p("a"), p("b")));
        let mut sm = StaticMachine::new();
        let stuck_succs = Machine::of_lp(&mut sm, &lp_stuck).steps();
        assert_eq!(stuck_succs.len(), 0);
    }

    /** Sequential program steps to nested modality */
    #[test]
    fn step_seq() {
        let lp_seq = lp_emp(b(seq(s("a"),s("b")),p("p")));
        let mut sm = StaticMachine::new();
        let seq_succs = Machine::of_lp(&mut sm, &lp_seq).steps();
        assert_eq!(seq_succs.len(), 1);
        assert_eq!(seq_succs[0].dm.goals[0], Goal { assumps: vec![], concl: *b(s("a"),b(s("b"),p("p")))});
    }

    /** Choice program steps to two goals. */
    #[test]
    fn step_choice() {
        let lp_choice = lp_emp(b(u(s("a"),s("b")),p("p")));
        let mut sm = StaticMachine::new();
        let choice_succs = Machine::of_lp(&mut sm, &lp_choice).steps();
        assert_eq!(choice_succs.len(), 1);
        assert_eq!(choice_succs[0].dm.goals[0], Goal { assumps: vec![], concl: *a(b(s("a"),p("p")),b(s("b"),p("p")))});
    }

    /** Test steps to assumption */
    #[test]
    fn step_test() {
        let lp_test = lp_emp(b(t(p("a")),p("b")));
        let mut sm = StaticMachine::new();
        let test_succs = Machine::of_lp(&mut sm, &lp_test).steps();
        assert_eq!(test_succs.len(), 1);
        assert_eq!(test_succs[0].dm.goals[0], Goal { assumps: vec![], concl: *i(p("a"), p("b"))});
    }

    /** Loop steps to precondtion, invariant preservations, and postconditions*/
    #[test]
    fn step_loop() {
        let lp_loop = lp_emp(b(l(s("a"),o(p("p"),o(p("q"),p("r")))),p("z")));
        let mut sm = StaticMachine::new();
        let loop_succs = Machine::of_lp(&mut sm, &lp_loop).steps();
        assert_eq!(loop_succs.len(), 1);
        assert_eq!(loop_succs[0].dm.goals.len(), 7);
        assert_eq!(loop_succs[0].dm.goals[0], Goal { assumps: vec![], concl: *o(p("p"),o(p("q"),p("r")))});
        
        assert_eq!(loop_succs[0].dm.goals[1], Goal { assumps: vec![*p("p")], concl: *b(s("a"), o(p("p"),o(p("q"),p("r"))))});
        assert_eq!(loop_succs[0].dm.goals[2], Goal { assumps: vec![*p("q")], concl: *b(s("a"), o(p("p"),o(p("q"),p("r"))))});
        assert_eq!(loop_succs[0].dm.goals[3], Goal { assumps: vec![*p("r")], concl: *b(s("a"), o(p("p"),o(p("q"),p("r"))))});
        
        assert_eq!(loop_succs[0].dm.goals[4], Goal { assumps: vec![*p("p")], concl: *p("z")});
        assert_eq!(loop_succs[0].dm.goals[5], Goal { assumps: vec![*p("q")], concl: *p("z")});
        assert_eq!(loop_succs[0].dm.goals[6], Goal { assumps: vec![*p("r")], concl: *p("z")});
    }

    /** And steps to two goals*/
    #[test]
    fn step_and() {
        let lp_and = lp_emp(a(p("p"),p("q")));
        let mut sm = StaticMachine::new();
        let and_succs = Machine::of_lp(&mut sm, &lp_and).steps();
        assert_eq!(and_succs.len(), 1);
        assert_eq!(and_succs[0].dm.goals[0], Goal {assumps: vec![], concl: *p("p")});
        assert_eq!(and_succs[0].dm.goals[1], Goal {assumps: vec![], concl: *p("q")});
    }

    /** Or steps to two alternatives, each with one goal. */
    #[test]
    fn step_or() {
        let lp_or = lp_emp(o(p("p"),p("q")));
        let mut sm = StaticMachine::new();
        let or_succs = Machine::of_lp(&mut sm, &lp_or).steps();
        assert_eq!(or_succs.len(), 2);
        assert_eq!(or_succs[0].dm.goals[0], Goal {assumps: vec![], concl: *p("p")});
        assert_eq!(or_succs[1].dm.goals[0], Goal {assumps: vec![], concl: *p("q")});
    }

    /** Implication steps to assumption. */
    #[test]
    fn step_imp() {
        let sm = StaticMachine::new();
        let mut imp_mach = Machine::new(&sm);
        // Wrap implication in or because a raw implication would get converted to assump.
        imp_mach.inquire(&o(i(p("p"), p("q")),i(p("p"), p("q"))));
        // Both branches are an implication p -> q
        imp_mach = imp_mach.steps()[0].clone();
        let imp_succs = imp_mach.steps();
        assert_eq!(imp_succs.len(), 1);
        assert_eq!(imp_succs[0].dm.goals[0], Goal {assumps: vec![*p("p")], concl: *p("q")});
    }

    /** And on the left steps to two assumptions. */
    #[test]
    fn step_left_and() {
        let lp_left_and = lp_emp(i(a(p("a"),p("b")),p("c")));
        let mut sm = StaticMachine::new();
        let left_and_succs = Machine::of_lp(&mut sm, &lp_left_and).steps();
        assert_eq!(left_and_succs.len(), 1);
        assert_eq!(left_and_succs[0].dm.goals[0], Goal{assumps: vec![*p("a"),*p("b")], concl: *p("c")});
    }

    /** Stepping on left follows left-to-right order. */
    #[test]
    fn step_left_and_ltr() {
        // check that order of operations is left-to-right
        let lp_left_and_ltr = lp_emp(i(a(p("a"),p("b")), i(a(p("c"),p("d")),p("e"))));
        let mut sm = StaticMachine::new();
        let left_and_ltr_succs = Machine::of_lp(&mut sm, &lp_left_and_ltr).steps();
        assert_eq!(left_and_ltr_succs.len(), 1);
        assert_eq!(left_and_ltr_succs[0].dm.goals[0], Goal {assumps: vec![*p("a"),*p("b"),*a(p("c"),p("d"))], concl: *p("e")});
    }

    /* Step applies on the left even when surrounded by formulas to which no rules apply. */
    #[test]
    fn step_choice_surround() {
        // check that surrounding assumptions are ok
        let lp_choice_surround = lp_emp(i(p("a"),i(a(p("b"),p("c")),i(p("d"),i(p("e"),p("f"))))));
        let mut sm = StaticMachine::new(); 
        let choice_surround_succs = Machine::of_lp(&mut sm, &lp_choice_surround).steps();
        assert_eq!(choice_surround_succs.len(), 1);
        assert_eq!(choice_surround_succs[0].dm.goals[0], Goal {assumps: vec![*p("a"), *p("b"), *p("c"), *p("d"), *p("e")], concl: *p("f")});
    }

    /** Explicitly defined symbol steps to its definition. */
    #[test]
    fn step_prog_defn() {
        let mut sm = StaticMachine::new();
        sm.define(&prog("a", u(s("b"),s("c"))));
        let mut sym_mach = Machine::new(&sm);
        sym_mach.inquire(&b(s("a"),p("d")));
        let sym_mach_succs = sym_mach.steps();
        assert_eq!(sym_mach_succs.len(), 1);
        assert_eq!(sym_mach_succs[0].dm.goals[0], Goal{assumps: vec![], concl: *b(u(s("b"),s("c")),p("d"))});        
    }

    /** Atomic predicate steps to one alternative per clause, one goal per assumption. */
    #[test]
    fn step_atom_pred() {
        let mut sm = StaticMachine::new();
        sm.define(&preds(vec![i(p("b"),i(p("c"),p("a"))),i(b(s("d"),p("e")),p("a"))]));
        let mut atom_pred_mach = Machine::new(&sm);
        atom_pred_mach.inquire(&p("a"));
        let atom_pred_mach_succs = atom_pred_mach.steps();
        assert_eq!(atom_pred_mach_succs.len(), 2);
        assert_eq!(atom_pred_mach_succs[0].dm.goals.len(), 2);
        assert_eq!(atom_pred_mach_succs[1].dm.goals.len(), 1);
        assert_eq!(atom_pred_mach_succs[0].dm.goals[0], Goal{assumps: vec![], concl: *p("b")});
        assert_eq!(atom_pred_mach_succs[0].dm.goals[1], Goal{assumps: vec![], concl: *p("c")});
        assert_eq!(atom_pred_mach_succs[1].dm.goals[0], Goal{assumps: vec![], concl: *b(s("d"),p("e"))});
    }

    /* Box pred steps to one alternative per applicable clause, one goal per assumption. */
    #[test]
    fn step_box_pred() {
        let mut sm = StaticMachine::new();
        sm.define(&preds(vec![b(s("c"),p("a"))]));
        sm.define(&preds(vec![i(p("a"), p("b"))]));
        let mut symbol_pred_mach = Machine::new(&sm);
        symbol_pred_mach.inquire(&b(s("c"),p("b")));
        let symbol_pred_mach_succs = symbol_pred_mach.steps();
        assert_eq!(symbol_pred_mach_succs.len(), 1);
        assert_eq!(symbol_pred_mach_succs[0].dm.goals[0], Goal{assumps: vec![*p("a")], concl: *p("b")});
    }
    
    /* If both symbol and atom predicate are defined, symbol predicate takes priority. */
    #[test]
    fn step_both_pred() {
        let mut sm = StaticMachine::new();
        sm.define(&preds(vec![i(p("b"),i(p("c"),p("a"))),
                              i(b(s("d"),p("e")),p("a"))]));
        sm.define(&pred(i(p("c"), b(s("b"),p("e")))));
        let mut symbol_and_atom_mach = Machine::new(&sm);
        symbol_and_atom_mach.inquire(&i(p("c"),b(s("b"),p("a"))));
        let symbol_and_atom_succs = symbol_and_atom_mach.steps();
        assert_eq!(symbol_and_atom_succs.len(), 1);
        assert_eq!(symbol_and_atom_succs[0].dm.goals[0], Goal{assumps: vec![*p("e")], concl: *p("a")});
    }

    /* 
    * DYNAMICS TESTS  - run() method
    * */
    /** Query "a" should immediately get stuck. */
    #[test]
    fn run_stuck() {
        let lp_stuck = lp_emp(p("a"));
        let mut sm = StaticMachine::new();
        let mut stuck_mach = Machine::of_lp(&mut sm, &lp_stuck);
        stuck_mach.run();
        assert!(stuck_mach.is_stuck());
    }

    /** Query "a -> a" should succeed immediately. */
    #[test]
    fn run_selfimp() {
        let lp_selfimp = lp_emp(i(p("a"),p("a")));
        let mut sm = StaticMachine::new();
        let mut selfimp_mach = Machine::of_lp(&mut sm, &lp_selfimp);
        selfimp_mach.run();
        assert!(selfimp_mach.is_proved());
    }

    /** Query "(a&b)&(c&d) -> c" should succeed */
    #[test]
    fn run_abcd_imp_c() {
        let lp_abcd_imp_c = lp_emp(i(a(a(p("a"),p("b")),a(p("c"),p("d"))),p("c")));
        let mut sm = StaticMachine::new();
        let mut abcd_imp_c_mach = Machine::of_lp(&mut sm, &lp_abcd_imp_c);
        abcd_imp_c_mach.run();
        assert!(abcd_imp_c_mach.is_proved());
    }

    /** Query "(a&b)&(c&d) -> b&c" should succeed */
    #[test]
    fn run_abcd_imp_bc() {
        let lp_abcd_imp_bc = lp_emp(i(a(a(p("a"),p("b")),a(p("c"),p("d"))),a(p("b"),p("c"))));
        let mut sm = StaticMachine::new();
        let mut abcd_imp_bc_mach = Machine::of_lp(&mut sm, &lp_abcd_imp_bc);
        abcd_imp_bc_mach.run();
        assert!(abcd_imp_bc_mach.is_proved());
    }
    
    /** A should imply A|B|C|D*/
    #[test]
    fn run_or_abcd() {
        let lp_or_abcd = lp_emp(i(p("a"),o(o(p("a"),p("b")),o(p("c"),p("d")))));
        let mut sm = StaticMachine::new();
        let mut or_abcd_mach = Machine::of_lp(&mut sm, &lp_or_abcd);
        or_abcd_mach.run();
        assert!(or_abcd_mach.is_proved());
    }

    /* Atomic predicate should keep trying clauses until one succeeds. */
    #[test]
    fn run_atom_backtrack() {
        let lp_atom_backtrack = ast::LogicProgram { body: vec![*preds(vec![i(p("b"),p("a")),i(p("c"),p("a")),i(p("d"),p("a"))])], query: i(p("c"),p("a"))};
        let mut sm = StaticMachine::new();
        let mut atom_backtrack_mach = Machine::of_lp(&mut sm, &lp_atom_backtrack);  
        atom_backtrack_mach.run();
        assert!(atom_backtrack_mach.is_proved());
    }

    /* Box predicate should keep trying alternatives until one succeeds. */
    #[test]
    fn run_pred_backtrack() {
        let lp_pred_backtrack = ast::LogicProgram { 
        body: vec![*preds(vec![i(p("b"), b(s("p"),p("a"))),i(p("c"), b(s("p"),p("a"))),i(p("d"),b(s("p"),p("a")))])],
        query: i(p("c"), b(s("p"),p("a")))};
        let mut sm = StaticMachine::new();
        let mut pred_backtrack_mach = Machine::of_lp(&mut sm, &lp_pred_backtrack);
        pred_backtrack_mach.run();
        assert!(pred_backtrack_mach.is_proved());
    }

    /** DFA for regular expression (A|B)* should succeed. */
    #[test]
    fn run_dfa_abs() {
        let lp_dfa_abs = statics_common::normalize(*parselp(examples::DFA_ABS).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut dfa_abs_mach = Machine::of_lp(&mut sm, &lp_dfa_abs);
        dfa_abs_mach.run();
        assert!(dfa_abs_mach.is_proved());
    }

    /** DFA for regular expression (bb)* should succeed. */
    #[test]
    fn run_dfa_2b() {
        let lp_dfa_2b = statics_common::normalize(*parselp(examples::DFA_2B).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut dfa_2b_mach = Machine::of_lp(&mut sm, &lp_dfa_2b);
        dfa_2b_mach.run();
        assert!(dfa_2b_mach.is_proved());
    }

    /** Or inside of and should prove */
    #[test]
    fn run_or_inside_and() {
        let lp_or_inside_and = lp_emp(i(p("a"),a(o(p("a"),p("b")),o(p("a"),p("a")))));
        let mut sm = StaticMachine::new();
        let mut or_inside_and_mach = Machine::of_lp(&mut sm, &lp_or_inside_and);
        or_inside_and_mach.run();
        assert!(or_inside_and_mach.is_proved());
    }

    /** Single character NFA */
    #[test]
    fn run_char_nfa() {
        let lp_paper_nfa = statics_common::normalize(*parselp(examples::NFA_CHAR).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_nfa_mach = Machine::of_lp(&mut sm, &lp_paper_nfa);
        paper_nfa_mach.run();
        assert!(paper_nfa_mach.is_proved());
    }
    
    /** NFA simplified */
    #[test]
    fn run_popl_nfa_simp() {                              
        let lp_paper_nfa = statics_common::normalize(*parselp(examples::POPL_NFA_SIMP).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_nfa_mach = Machine::of_lp(&mut sm, &lp_paper_nfa);
        paper_nfa_mach.run();
        assert!(paper_nfa_mach.is_proved());
    } 

    /** POPL paper nfa */
    #[test]
    fn run_popl_nfa() {                              
        let lp_paper_nfa = statics_common::normalize(*parselp(examples::POPL_NFA).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_nfa_mach = Machine::of_lp(&mut sm, &lp_paper_nfa);
        paper_nfa_mach.run();
        assert!(paper_nfa_mach.is_proved());
    }

    /** Simplified fragment of pursuit-evasion game from FLOPS2026 paper should prove */
    #[test]
    fn run_popl_peg_simp() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::POPL_PEG_SIMP).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }
    
    /** Simplified fragment of pursuit-evasion game from FLOPS2026 paper should prove */
    #[test]
    fn run_popl_peg() {                              
        let lp_paper_peg = statics_common::normalize(*parselp(examples::POPL_PEG).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }

    /** One-counter example should prove. */
    #[test]
    fn run_one_counter_conj() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::ONE_COUNTER_CONJ).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }

    /** One-counter example should prove. */
    #[test]
    fn run_one_counter_curry() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::ONE_COUNTER_CURRY).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }

    /** Two-counter example should prove. */
    #[test]
    fn run_two_counter() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::TWO_COUNTERS).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }

    /** Nim: three piles of capacity 3 */
    #[test]
    fn run_nim_three_three_simp() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::NIM_THREE_THREE_SIMP).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }

    /* Nim: three piles of capacity 3 */
    #[test]
    fn run_nim_three_three() {
        let lp_paper_peg = statics_common::normalize(*parselp(examples::NIM_THREE_THREE).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut paper_peg_mach = Machine::of_lp(&mut sm, &lp_paper_peg);
        paper_peg_mach.run();
        assert!(paper_peg_mach.is_proved());
    }
}