/** Tests the parser module by comparing output to expected ASTs */
use glp::{parser,examples,statics_common};
pub mod common;
use common::*;
    
#[cfg(test)]
mod tests {
    use super::*;
    
    use glp::ast::{Program,Formula,Defn};
    use parser::pdlp::formula as parsef;
    use parser::pdlp::program as parsep;
    use parser::pdlp::defn as parsed;
    use parser::pdlp::defns as parseds;
    use parser::pdlp::logic_program as parselp;
    use parser::pdlp::query as parseq;

    /* Helper functions for round-trip tests that parsing result of prints produces identical results. */    
    /** Compute whether printing and parsing a formula are inverses */
    fn rt_fml(fml: &Formula) -> bool {
      let fml_clone = fml.clone();
      let printed = glp::printer_common::formula(fml);
      let parsed = parsef(&printed);
      parsed == Ok(Box::new(fml_clone))
    }

    /** Compute whether printing and parsing a programs are inverses */
    fn rt_prog(prog: &Program) -> bool {
      let prog_clone = prog.clone();
      let printed = glp::printer_common::program(prog);
      let parsed = parsep(&printed);
      parsed == Ok(Box::new(prog_clone))
    }

    /** Compute whether printing and parsing a definition are inverses */
    fn rt_defn(dfn: &Defn) -> bool {
      let dfn_clone = dfn.clone();
      let printed = glp::printer_common::defn(dfn);
      let parsed = parsed(&printed);
      parsed == Ok(Box::new(dfn_clone))
    }

    /** Atomic predicate parses */
    #[test]
    fn parse_pred() { assert_eq!(parsef("a"), Ok(p("a"))); }
    
    /** Conjunction parses */
    #[test]
    fn parse_and() { assert_eq!(parsef("a&b"), Ok(a(p("a"),p("b")))); }
    
    /** Disjunction parses */
    #[test]
    fn parse_or() { assert_eq!(parsef("a|b"), Ok(o(p("a"),p("b")))); }
    
    /** Implication parses with standard forward symbol */
    #[test]
    fn parse_imply() { assert_eq!(parsef("a->b"), Ok(i(p("a"),p("b")))); }
    
    /** Implication parses with backwards arrow symbol.*/
    #[test]
    fn parse_imply_rev() { assert_eq!(parsef("b<-a"), Ok(i(p("a"),p("b")))); }
    
    /** Box modality parses */
    #[test]
    fn parse_box() { assert_eq!(parsef("[a]b"), Ok(b(s("a"),p("b")))); }

    /** Clause with = in it parses */
    #[test]
    fn parse_clause_eq() { 
      assert_eq!(parsef("pa=a->[accw]pa=d"), 
       Ok(i(eq(vr("pa"),vr("a")), b(s("accw"), eq(vr("pa"),vr("d"))))))
    }
  
    /** Hoare triple notation parses */
    #[test]
    fn parse_hoare_triple() { assert_eq!(parsef("{a}b{c}"), Ok(i(p("a"),b(s("b"),p("c")))))}

    /** Program symbol parses */
    #[test]
    fn parse_symbol() { assert_eq!(parsep("a"), Ok(s("a"))); }
    
    /** Test program parses */
    #[test]
    fn parse_test() { assert_eq!(parsep("?a"), Ok(t(p("a")))); }
    
    /** Sequence program parses */
    #[test]
    fn parse_seq() { assert_eq!(parsep("a;b"), Ok(seq(s("a"),s("b")))); }
    
    /** Loop without invariant annotation parses */
    #[test]
    fn parse_loop() { assert_eq!(parsep("a*"), Ok(l(s("a"),v()))); }
    
    /** Loop with invariant annotation parses */
    #[test]
    fn parse_loop_with_inv() { assert_eq!(parsep("a*@inv(b)"), Ok(l(s("a"),p("b")))); }
    
    /** Choice program parses */
    #[test]
    fn parse_choice() { assert_eq!(parsep("a U b"), Ok(u(s("a"),s("b")))); }
    
    /** Explicit program definition parses */
    #[test]
    fn parse_progdefn() { assert_eq!(parsed("c::=d."),Ok(prog("c",s("d")))); }
    
    /** Atomic predicate definition parses with pred helper function */
    #[test]
    fn parse_pred_sing() { assert_eq!(parsed("a."),Ok(pred(p("a")))); }
    
    /** Atomic predicatie definition parses with preds helper function */
    #[test]
    fn parse_preds_sing() { assert_eq!(parsed("a."),Ok(preds(vec![p("a")]))); }    
    
    /** State variable definition parses */
    #[test]
    fn parse_state_var() { assert_eq!(parsed("pa : enum {a, b, c, d}"), Ok(sv("pa",vec!["a","b","c","d"]))); }
      
    /** Logic program parses with lp helper function */
    #[test]
    fn parse_lp_sing() { assert_eq!(parselp("a.?-b."),Ok(lp(pred(p("a")),p("b")))); }

    /** Parser removes comment on the same line as code */
    #[test]
    fn parse_comment_same_line() {
      assert_eq!(parselp("a. #This is a comment\n?-b."),Ok(lp(pred(p("a")),p("b"))));
    }

    /** Parser removes comment on its own line */
    #[test]
    fn parse_comment_own_line() {
      assert_eq!(parselp("#This is a comment\na. ?-b."),Ok(lp(pred(p("a")),p("b"))));
    }

    /** Logic program parses with lps helper function */
    #[test]
    fn parse_lps_sing() { assert_eq!(parselp("a.?-b."),Ok(lps(vec![pred(p("a"))],p("b")))); }
    
    /** Test parsing of predicate with multiple clauses */
    #[test]
    fn parse_two_clauses() {
      assert_eq!(parseds("[d]c <- a. [d]c <- b."), Ok(vec![
        *pred(i(p("a"),b(s("d"),p("c")))),
        *pred(i(p("b"),b(s("d"),p("c"))))]));
    }

    /** Smaller pieces of FLOPS example parse individually */
    #[test]
    fn paper_peg_pieces() {
        // Building up fragments of a larger program.
        assert_eq!(parsef("[l]ab <- ac"),Ok(i(p("ac"),b(s("l"),p("ab")))));
        assert_eq!(parsed("demon-turn ::= l U r."), Ok(prog("demon-turn",u(s("l"),s("r")))));
        let eachp = parseds("[l]ab <- ac. [l]bc <- bd. [l]cd <- ca. [l]da <- db.").unwrap();
        assert_eq!(statics_common::normalize_body(eachp), Ok(vec![*preds(vec![
            i(p("ac"),b(s("l"),p("ab"))),
            i(p("bd"),b(s("l"),p("bc"))),
            i(p("ca"),b(s("l"),p("cd"))),
            i(p("db"),b(s("l"),p("da")))])]));
        assert_eq!(parsed("angel-turn ::= (?ab;la U ?bc;la U ?cd;la U ?da;la) U (?ad;ra U ?ba;ra U ?cb;ra U ?dc;ra)."), Ok(
            prog("angel-turn", u(
                 u(seq(t(p("ab")),s("la")),u(seq(t(p("bc")),s("la")),u(seq(t(p("cd")),s("la")),seq(t(p("da")),s("la")))))
                ,u(seq(t(p("ad")),s("ra")),u(seq(t(p("ba")),s("ra")),u(seq(t(p("cb")),s("ra")),seq(t(p("dc")),s("ra")))))))));
        assert_eq!(parseq("?- ac -> [(demon-turn;angel-turn)*@inv(ac|bd|ca|db)](ac|bd|ca|db)."),
            Ok(i(p("ac"),b(l(seq(s("demon-turn"),s("angel-turn")),
              o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))),
              o(p("ac"),o(p("bd"),o(p("ca"),p("db"))))))));
    }
 
    /** FLOPS 2026 example parses in its entirety */
    #[test]
    fn paper_peg() {    
        assert_eq!(statics_common::normalize(*parselp(examples::FLOPS_PEG).unwrap()), Ok(*flops_parsed()));
    }

    /** Large formula round-trips correctly */
    #[test]
    fn rt_big_fml() {
      let conj1 = a(a(p("a"),p("b")),a(p("c"),p("d")));
      let disj1 = o(o(conj1.clone(), conj1.clone()), o(conj1.clone(), conj1.clone()));
      let impl1 = i(i(disj1.clone(), disj1.clone()), i(disj1.clone(), disj1.clone()));
      let box1 = b(s("e"), impl1.clone());
      let conj2 = a(box1.clone(), box1.clone());
      let disj2 = o(conj2.clone(), conj2.clone());
      let impl2 = i(disj2.clone(), disj2.clone());
      let box2 = b(s("e"), impl2.clone());
      assert!(rt_fml(&box2));
    }

    /** Large program round-trips correctly */
    #[test]
    fn rt_big_prog() {
      let test1 = t(p("a"));
      let choice1 = u(s("b"),test1.clone());
      let seq1 = seq(choice1.clone(), choice1.clone());
      let loop1 = l(seq1.clone(), a(p("c"),o(p("d"),p("e"))));
      let choice2 = u(u(loop1.clone(),loop1.clone()),u(loop1.clone(),loop1.clone()));
      let seq2 = seq(seq(choice2.clone(),choice2.clone()),seq(choice2.clone(),choice2.clone()));
      let loop2 = l(seq2.clone(), o(a(p("f"),p("g")),a(p("h"),p("i"))));
      assert!(rt_prog(&loop2));
    }

    /** Definition round-trips correctly */
    #[test]
    fn rt_dfns() {
      let dfn1 = prog("prog", seq(u(s("some"),t(p("p"))),l(s("text"),p("h"))));
      assert!(rt_defn(&dfn1));
      let dfn2 = pred(i(p("b"),p("a")));
      assert!(rt_defn(&dfn2));
      let dfn3 = pred(i(b(s("a"),p("b")),b(s("c"),p("d"))));
      assert!(rt_defn(&dfn3));
    }

}