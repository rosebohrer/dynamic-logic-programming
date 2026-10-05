/*! Convert source code and commands into abstract syntax trees.

Precedence-climbing parsing algorithm implemented using parsing expression 
grammars via the PEG crate. The precedence! macro does most of the heavy
lifting, generating the parser given precedence and associativity specifications.
This module is responsible for parsing interactive-mode commands in addition to 
the core language syntax.
*/
use crate::ast::*;
use DefnNode::*; use ProgramNode::*; use FormulaNode::*; use TermNode::*;

fn to_i32(u: usize) -> i32 { 
    match i32::try_from(u) {
        Ok(v) => v,
        Err(_) => -1
    }
}

fn spanned<T>(i:usize,j:usize,t:T) -> Spanned<T> {
    let len = j-i;
    Spanned { node: t, span: Span { start: to_i32(i), len: to_i32(len) }}
}

fn mk_spanned<T>(span: Span, node:T) -> Spanned<T> {
    Spanned{ node, span }
}

fn span_union<T1,T2>(s1: &Spanned<T1>, s2: &Spanned<T2>) -> Span{
    let s1 = s1.span;
    let s2 = s2.span;
    let off = s2.start - s1.start;
    let full_len = s2.len + off;
    Span { start: s1.start, len: full_len}
}

peg::parser!( 
  /** Demonic dynamic logic programming parser */
  pub grammar pdlp() for str {
    rule comment() -> () = "#" ([^ '\n' | '\r']*)
    
    /** Parse whitespace. */
    rule _ -> () = (_:([' ' | '\t' | '\n' | '\r']) /  comment())* {()}

    /** Parse an identifier. 
    
      Identifiers can contain hyphens but they must not be at the start nor end, 
      otherwise they would conflict with parsing for -> and <- 
      */
    rule id() -> String = n:$(['a'..='z' | 'A'..='Z' | '_'] 
      (( ("-"*) ['a'..='z' | 'A'..='Z' |'0'..='9' | '_']+))*) 
      { n.to_string() }

    /** Parse a program definition. */
    pub rule prog_defn() -> Box<Defn> = _ pos1:position!() n:id() _ "::=" _  a:program() _ "." pos2:position!() _ { 
        Box::new(spanned(pos1,pos2,ProgDefn(n,a))) 
    }

    /** Parse a clause of a predicate definition. */
    pub rule pred_defn() -> Box<Defn> = _ pos1:position!() ps:(formula() ** (_ "," _)) (_ "."  _) pos2:position!()  { 
        let mut acc : Box<Formula> = ps[0].clone();
        for i in 1..ps.len() {
            let f = &ps[i];
            acc = Box::new(respan(f.span, FormulaNode::And(acc, f.clone())));
        }
        Box::new(spanned(pos1,pos2,PredDefn(vec![*acc]))) 
    }

    rule one_state() -> String = _ x:$(id()) _ {x.to_string()}
    rule state_list() -> Vec<String> =  (one_state() ** ",")

    /** Parse a state variable definition (enumeration). */
    // q : enum {q0,q1,q2,q3,q4,q5}.
    pub rule var_defn() -> Box<Defn> = _ pos1:position!() x:id() _ ":" _ "enum" _ "{" _ vs:state_list() _ "}" pos2:position!() _ { 
        Box::new(spanned(pos1,pos2,VarDefn(x, vs)))
    }
    /** Parse a single definition. */
    pub rule defn() -> Box<Defn> = prog_defn() / pred_defn() / var_defn()
    
    /** Parse multiple definitions. */
    pub rule defns() -> Vec<Defn> =
      ds:(defn()*) {
        let mut v : Vec<Defn> = Vec::new();
        for d in ds {
            v.push(*d);
        }
        v
      }

    /** Parse a single query, including ?- prompt. */
    pub rule query() -> Box<Formula> =  _ "?-" _ p:formula() _ "." _ {p}

    /** Parse a complete batch-mode program: definitions and one query. */
    pub rule logic_program() -> Box<LogicProgram> =
      body:defns() query:query() { 
        Box::new(LogicProgram {body, query})
    }
    
    /** Parse a formula. */
    pub rule formula() -> Box<Formula> = precedence!{
        p:@ _ "->" _ q:(@) { 
            let span = span_union(&p, &q);
            Box::new(mk_spanned(span,Imply(p,q)))
        }
        p:@ _ "<-" _ q:(@) { 
            let span = span_union(&p, &q);
            Box::new(mk_spanned(span,Imply(q,p)))
        }
        --
        p:@ _ "|" _ q:(@) { 
            let span = span_union(&p, &q);
            Box::new(mk_spanned(span,Or(p,q)))
        }
        --
        p:@ _ "&" _ q:(@) { 
            let span = span_union(&p, &q);
            Box::new(mk_spanned(span,And(p,q)))
        }
        --
        _ pos1:position!() "[" _ a:program() _ "]" _ p:@ { 
            // span calculuation code differs slightly because the location of prefix "[" must be captured
            let spanned1 = Spanned{span: Span { start: to_i32(pos1), len: 1}, node: True() }; 
            let span = span_union(&spanned1, &p);
            Box::new(mk_spanned(span,MBox(a,p)))
        }
        _ pos1:position!() "<" _ a:program() _ ">" _ p:@ { 
            // span calculuation code differs slightly because the location of prefix "[" must be captured
            let spanned1 = Spanned{span: Span { start: to_i32(pos1), len: 1}, node: True() }; 
            let span = span_union(&spanned1, &p);
            Box::new(mk_spanned(span,MDiamond(a,p)))
        }
        --
        _ pos1:position!() "(" _ a:formula() _ ")" pos2:position!() _ { 
            Box::new(spanned(pos1, pos2, a.node))
        }
        _ pos1:position!() "{" _ pre:formula()  _ "}" _ p:program() _ "{" _ post:formula() _ "}" pos2:position!() 
          { let b = Box::new(spanned(pos1,pos2,MBox(p,post)));
            Box::new(spanned(pos1,pos2,Imply(pre, b))) }
        _ pos1:position!() "<{" _ pre:formula()  _ "}>" _ p:program() _ "{" _ post:formula() _ "}" pos2:position!() 
          { let b = Box::new(spanned(pos1,pos2,MDiamond(p,post)));
            Box::new(spanned(pos1,pos2,Imply(pre, b))) }
        _ af:atom_fml() _ { af}
        //_ pos1:position!() p:id() pos2:position!() _  { Box::new(spanned(pos1,pos2,Pred(p)))}
        //--
        //_ pos1:position!() a:term() _ "=" _ b:term() pos2:position!() _ { Box::new(spanned(pos1,pos2,Equal(a,b)))}
    }

    /* Parse the invariant annotation following a loop */
    // @TODO: set length of span correctly
    rule inv_part() -> Box<Formula> =
      _ "@inv" _ "(" _ f:formula() _ ")" { f }

    pub rule term() -> Box<Term> =   
      _ pos1:position!() "'" x:id() pos2:position!(){ Box::new(spanned(pos1,pos2,ValTerm(x))) } 
    / _ pos1:position!() x:id() pos2:position!() { Box::new(spanned(pos1,pos2,VarTerm(x))) }

    rule tbranch() -> Box<Term> = "=" _ l:term() {l} 

    pub rule atom_fml() -> Box<Formula> =
      _ pos1:position!() l:term() _ rr:(tbranch())? pos2:position!() _  {
        match (l.node.clone(), rr) {
            (TermNode::ValTerm(ss), None) => {
                let v = if ss == "true" { True() } else { Pred(ss) };
                Box::new(spanned(pos1,pos2,v))
            },
            (TermNode::VarTerm(ss), None) => {
                let v = if ss == "true" { True() } else { Pred(ss) };
                Box::new(spanned(pos1,pos2,v))
            },
            (_, Some(r)) => Box::new(spanned(pos1,pos2,Equal(Box::new(*l),r)))
        }
      }

    /** Parse a program. */
    pub rule program() -> Box<Program> = precedence!{
        a:@ _ "U" _ b:(@) { 
            let span = span_union(&a, &b);
            Box::new(mk_spanned(span,Choice(a, b))) 
        }
        --
        a:@ _ ";" _ b:(@) { 
            let span = span_union(&a, &b);
            Box::new(mk_spanned(span,Seq(a, b)))
        }
        --
        a:@ _ "*" j:(inv_part())? _ { 
            match (a, j)  {
                (a, None) => {
                    // incorrect calculation but we expect everything to have annotations for now.
                    Box::new(mk_spanned(a.span, Loop(a.clone(), Box::new(mk_spanned(a.span,True())))))
                },
                (a, Some(x)) => {
                    let span = span_union(&a, &x);
                    Box::new(mk_spanned(span, Loop(a, x)))
                },
            }
        } 
        --
        _ pos1:position!() "?" _ p:(formula()) { 
            let spanned1 = Spanned{span: Span { start: to_i32(pos1), len: 1}, node: True() }; 
            let span = span_union(&spanned1, &p);
            Box::new(mk_spanned(span, Test(p))) 
        }
        --
        _ pos1:position!() "(" _ a:program() _ ")" pos2:position!() _ { 
            Box::new(spanned(pos1, pos2, a.node))
        }
        _ pos1:position!() c:id() pos2:position!() _ { Box::new(spanned(pos1,pos2,Symbol(c))) }
    }

    /** Parse a user command for the interactive REPL. */
    pub rule repl_command() -> REPLCommand = precedence!{
        "help" _ { REPLCommand::Help() }
        "quit" _ { REPLCommand::Quit() }
        "print" _ { REPLCommand::Print() }
        "def" _ d:defns() _ { REPLCommand::Define(d) }
        "?-" _ f:formula() _ { REPLCommand::Query(f) }
    }

    /** EDSL frontend requires DDLP syntax to be valid Rust expression syntax, which is then recorded into 
     * a string for runtime parsing. The following parsing code implements parsing this string of EDSL syntax.
     * 
     * See the EDSL macro implementation [[edsl.rs]] for documentation of the EDSL syntax.
     */

    //@TODO: Need a syntax for state variable / enumeration definitions
    //@TODO: The spans for the edsl are not very meaningful. It would be better to use macros to record
    // where the macro call takes place and record that information in the spans, rather than the parsed string.
    /** Parse a formula in EDSL syntax. */
    pub rule edsl_formula() -> Box<Formula> = precedence!{
        p:@ pos1:position!()  _ ">=" _ pos2:position!() q:(@) { Box::new(spanned(pos1,pos2,Imply(p,q)))}
        p:@ pos1:position!()  _ "<=" _ pos2:position!() q:(@) { Box::new(spanned(pos1,pos2,Imply(q,p)))}
        --  
        p:@ pos1:position!() _ "|" _ pos2:position!() q:(@) { Box::new(spanned(pos1,pos2,Or(p,q)))}
        --
        p:@ pos1:position!() _ "&" _ pos2:position!() q:(@) { Box::new(spanned(pos1,pos2,And(p,q)))}
        --
        p:@ pos1:position!() _ "[" _ a:edsl_program() _ "]"  pos2:position!()  { Box::new(spanned(pos1,pos2,MBox(a,p)))}
        p:@ pos1:position!() _ "<<=" _ a:edsl_program() _   pos2:position!()  { Box::new(spanned(pos1,pos2,MDiamond(a,p)))}
        --
        _ pos1:position!() "(" _ a:edsl_formula() _ ")" pos2:position!() _ { a }
        _ pos1:position!() p:id() pos2:position!() _  { Box::new(spanned(pos1,pos2,Pred(p)))}
        --
        _ pos1:position!() a:edsl_term() _ "==" _ b:edsl_term() pos2:position!() _ { Box::new(spanned(pos1,pos2,Equal(a,b)))}
    }

    pub rule edsl_term() -> Box<Term> =   
      _ pos1:position!() "''" x:id() pos2:position!(){ Box::new(spanned(pos1,pos2,ValTerm(x))) } 
    / _ pos1:position!() x:id() pos2:position!() { Box::new(spanned(pos1,pos2,VarTerm(x))) }


    /** Parse a program in EDSL syntax. */
    pub rule edsl_program() -> Box<Program> = precedence!{
        a:@ pos1:position!()  _ "||" _ pos2:position!() b:(@)  { Box::new(spanned(pos1,pos2,Choice(a, b))) }
        --
        a:@ pos1:position!()  _ "/" _ pos2:position!() b:(@)  { Box::new(spanned(pos1,pos2,Seq(a, b))) }
        --
        a:@ pos1:position!()  _ "*" j:(edsl_formula())? pos2:position!() _ { 
            match (a, j)  {
                (a, None) => Box::new(spanned(pos1,pos2,Loop(a, Box::new(spanned(pos1,pos2,True()))))),
                (a, Some(x)) => Box::new(spanned(pos1,pos2,Loop(a, x))),
            }
        } 
        --
        _ pos1:position!() p:(edsl_formula()) _ "?"  pos2:position!() { Box::new(spanned(pos1,pos2,Test(p))) }
        --
        _ pos1:position!() "(" _ a:edsl_program() _ ")" pos2:position!() _ { a }
        _ pos1:position!() c:id() pos2:position!() _ { Box::new(spanned(pos1,pos2,Symbol(c))) }
    }

    /** Parse a program definition in EDSL syntax. */
    pub rule edsl_prog_defn() -> Box<Defn> = pos1:position!() n:id() _ "<=" _  a:edsl_program() _ ";" pos2:position!() _ { 
        Box::new(spanned(pos1,pos2,ProgDefn(n,a))) 
    }

    /** Parse a clause of a predicate definition in EDSL syntax. */
    pub rule edsl_pred_defn() -> Box<Defn> = pos1:position!() ps:(edsl_formula() ** (_ "," _)) (_ ";"  _) pos2:position!()  { 
        let mut acc : Box<Formula> = ps[0].clone();
        for i in 1..ps.len() {
            let f = &ps[i];
            acc = Box::new(respan(f.span, FormulaNode::And(acc, f.clone())));
        }
        Box::new(spanned(pos1,pos2,PredDefn(vec![*acc]))) 
    }

    /** Parse a single definition in EDSL syntax. */
    pub rule edsl_defn() -> Box<Defn> = edsl_prog_defn() / edsl_pred_defn()
    
    /** Parse multiple definitions in EDSL syntax. */
    pub rule edsl_defns() -> Vec<Defn> =
      ds:(edsl_defn()*) {
        let mut v : Vec<Defn> = Vec::new();
        for d in ds {
            v.push(*d);
        }
        v
      }

    /** Parse logic program in EDSL syntax. */
    pub rule edsl_logic_program() -> Box<LogicProgram> =
      body:edsl_defns() query:edsl_formula() { 
        Box::new(LogicProgram {body, query})
    }
});