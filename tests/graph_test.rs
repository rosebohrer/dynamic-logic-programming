pub mod common;
use glp::frontends::graph;
use glp::ddlp::dynamics;
use glp::statics_common;
use graph::*;

#[cfg(test)]
mod tests {
    use super::*;
    use dynamics::{Machine,StaticMachine};
    use glp::parser::pdlp::logic_program as parselp; 

    fn graph_paper_peg() -> graph::Graph { 
        let (va, vb, vc, vd) = ("a".to_string(),"b".to_string(),"c".to_string(),"d".to_string());
        graph::Graph {
        v: vec![va.clone(), vb.clone(), vc.clone(), vd.clone()],
        e: vec![(va.clone(), vb.clone()), (va.clone(), vd.clone()),
                (vb.clone(), vc.clone()), (vb.clone(), va.clone()),
                (vc.clone(), vd.clone()), (vc.clone(), vb.clone()),
                (vd.clone(), va.clone()), (vd.clone(), vc.clone())],
        pos0: Position {a: va.clone(), d: vc.clone()}, 
        strat: vec![
            (Position{a: va.clone(), d: vb.clone(),}, vd.clone()),
            (Position{a: vb.clone(), d: vc.clone(),}, va.clone()),
            (Position{a: vc.clone(), d: vd.clone(),}, vb.clone()),
            (Position{a: vd.clone(), d: va.clone(),}, vc.clone()),

            (Position{a: va.clone(), d: vd.clone(),}, vb.clone()),
            (Position{a: vb.clone(), d: va.clone(),}, vc.clone()),
            (Position{a: vc.clone(), d: vb.clone(),}, vd.clone()),
            (Position{a: vd.clone(), d: vc.clone(),}, va.clone()),
        ],
        inv: vec![
            Position {a: "a".to_string(), d: "c".to_string(),}, 
            Position {a: "b".to_string(), d: "d".to_string(),},
            Position {a: "c".to_string(), d: "a".to_string(),},
            Position {a: "d".to_string(), d: "b".to_string(),}],
        }
    }

    #[test]
    fn graph_paper_peg_right_str() { 
        let src = graph_paper_peg().to_ddlp_source();
        let want = "d ::= d0 U d1.\na-a -> [d0]a-b.\nb-a -> [d0]b-b.\nc-a -> [d0]c-b.\nd-a -> [d0]d-b.\na-a -> [d1]a-d.\nb-a -> [d1]b-d.\nc-a -> [d1]c-d.\nd-a -> [d1]d-d.\na-b -> [d0]a-c.\nb-b -> [d0]b-c.\nc-b -> [d0]c-c.\nd-b -> [d0]d-c.\na-b -> [d1]a-a.\nb-b -> [d1]b-a.\nc-b -> [d1]c-a.\nd-b -> [d1]d-a.\na-c -> [d0]a-d.\nb-c -> [d0]b-d.\nc-c -> [d0]c-d.\nd-c -> [d0]d-d.\na-c -> [d1]a-b.\nb-c -> [d1]b-b.\nc-c -> [d1]c-b.\nd-c -> [d1]d-b.\na-d -> [d0]a-a.\nb-d -> [d0]b-a.\nc-d -> [d0]c-a.\nd-d -> [d0]d-a.\na-d -> [d1]a-c.\nb-d -> [d1]b-c.\nc-d -> [d1]c-c.\nd-d -> [d1]d-c.\na-b -> [a]d-b.\nb-c -> [a]a-c.\nc-d -> [a]b-d.\nd-a -> [a]c-a.\na-d -> [a]b-d.\nb-a -> [a]c-a.\nc-b -> [a]d-b.\nd-c -> [a]a-c.\na-turn ::= ?a-b; a U ?b-c; a U ?c-d; a U ?d-a; a U ?a-d; a U ?b-a; a U ?c-b; a U ?d-c; a.";
        assert_eq!(src, want);
    }

    #[test]
    fn graph_paper_peg_runs() {
        let lp_source = format!("{}\n\n{}", graph_paper_peg().to_ddlp_source(), graph_paper_peg().ddlp_query());
        let lp_paper_peg = statics_common::normalize(*parselp(&lp_source).unwrap()).unwrap();
        let mut sm = StaticMachine::new();
        let mut m = Machine::of_lp(&mut sm, &lp_paper_peg);
        m.run();
        assert!(m.is_proved());
    }
}