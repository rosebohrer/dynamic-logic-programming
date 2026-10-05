pub mod common;
use glp::frontends::fsm;
use glp::statics_common;
    
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use glp::ddlp::dynamics::{Machine,StaticMachine};
    use glp::parser::pdlp::logic_program as parselp; 

    fn nfa_2b() -> fsm::NFA { 
        fsm::NFA {
            q: HashSet::from(["s".to_string(), "a".to_string(), "d".to_string()]),
            sigma: HashSet::from(["a".to_string(), "b".to_string()]),
            delta: HashSet::from([
                fsm::Transition::NonEmpty("s".to_string(),"b".to_string(),"a".to_string()),
                fsm::Transition::NonEmpty("a".to_string(),"b".to_string(),"s".to_string()),
                fsm::Transition::NonEmpty("d".to_string(),"b".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("a".to_string(),"a".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("s".to_string(),"a".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("d".to_string(),"a".to_string(),"d".to_string()),
            ]),
            q0: "s".to_string(),
            f: HashSet::from(["s".to_string()]),
        }
    }
    fn inv_2b() -> HashSet<String> {
        HashSet::from(["s".to_string()])
    }
    fn regex_2b() -> fsm::Regex {
        fsm::Regex::Star(Box::new(
            fsm::Regex::Sequence(
                Box::new(fsm::Regex::Char("b".to_string())),
                Box::new(fsm::Regex::Char("b".to_string()))
            )
        ))
    }

    fn nfa_abs() -> fsm::NFA {
        fsm::NFA {
            q: HashSet::from(["s".to_string(),"d".to_string()]),
            sigma: HashSet::from(["a".to_string(),"b".to_string(),"c".to_string()]),
            delta: HashSet::from([
                fsm::Transition::NonEmpty("s".to_string(),"a".to_string(),"s".to_string()),
                fsm::Transition::NonEmpty("d".to_string(),"a".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("s".to_string(),"b".to_string(),"s".to_string()),
                fsm::Transition::NonEmpty("d".to_string(),"b".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("s".to_string(),"c".to_string(),"d".to_string()),
                fsm::Transition::NonEmpty("d".to_string(),"c".to_string(),"d".to_string()),                
            ]),
            q0: "s".to_string(),
            f: HashSet::from(["s".to_string()]),
        }
    }
    fn inv_abs() -> HashSet<String>  {
        HashSet::from(["s".to_string()])
    }
    fn regex_abs() -> fsm::Regex {
        fsm::Regex::Star(Box::new(
            fsm::Regex::Choice(
                Box::new(fsm::Regex::Char("a".to_string())),
                Box::new(fsm::Regex::Char("b".to_string())))))
    }
    
    #[test]
    fn fsm_2b_right_str() { 
        let src = nfa_2b().to_source();
        let expect_src = "a -> [a]d.\nd -> [a]d.\ns -> [a]d.\na -> [b]s.\nd -> [b]d.\ns -> [b]a.\ns -> final.\n";
        assert_eq!(src, expect_src); 
        let q = nfa_2b().query(&regex_2b(), &inv_2b());
        let expect_q = "?- s -> [(((b);(b)))*@inv(s)]s.";
        assert_eq!(q, expect_q);
    }

    #[test]
    fn fsm_abs_right_str() { 
        let src = nfa_abs().to_source();
        let expect_src = "d -> [a]d.\ns -> [a]s.\nd -> [b]d.\ns -> [b]s.\nd -> [c]d.\ns -> [c]d.\ns -> final.\n";
        assert_eq!(src, expect_src); 
        let q = nfa_abs().query(&regex_abs(), &inv_abs());
        let expect_q = "?- s -> [(((a)U(b)))*@inv(s)]s.";
        assert_eq!(q, expect_q);
    }

    #[test]
    fn fsm_2b_runs() {
        let lp_source = format!("{}\n\n{}", nfa_2b().to_source(), nfa_2b().query(&regex_2b(), &inv_2b()));
        let lp_2b = statics_common::normalize(*parselp(&lp_source).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut m = Machine::of_lp(&mut sm, &lp_2b);
        m.run();
        assert!(m.is_proved());
    }

    #[test]
    fn fsm_abs_runs() {
        let lp_source = format!("{}\n\n{}", nfa_abs().to_source(), nfa_abs().query(&regex_abs(), &inv_abs()));
        let lp_abs = statics_common::normalize(*parselp(&lp_source).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut m = Machine::of_lp(&mut sm, &lp_abs);
        m.run();
        assert!(m.is_proved());
    }
}