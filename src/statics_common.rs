/*! Implement static analyses and static semantics that are shared between DDLP and PDLP.

 These analyses are primarily used to ensure that programs are well-formed before running. */
use crate::ast::{Formula,Program,Term,LogicProgram,Defn,FormulaNode,ProgramNode,DefnNode,TermNode,Spanned,Span,CompileResult};
use FormulaNode::*; use ProgramNode::*; use DefnNode::*; use TermNode::*;
use std::collections::{HashSet,HashMap};
use crate::ast::respan as respan;


/** Stores all the free identifiers of an expression */
pub struct FI {  
  symbols: HashSet<String>, // Program symbols
  preds: HashSet<String>, // Predicates (both box and atomic)
  state_vars: HashSet<String>, // Variables that make up the state
}

impl FI {
    /** Empty collection of identifiers */
    fn empty() -> Self {
        FI { symbols: HashSet::new(), preds: HashSet::new(), state_vars: HashSet::new() }
    }

    /** Add symbols of program to collection. */
    fn accum_prog(&mut self, a: &Program) {
        match &a.node {
            Symbol(c) => {self.symbols.insert(c.to_string()); },
            Test(p) => self.accum_formula(p),
            Seq(a, b) => {self.accum_prog(a); self.accum_prog(b)},
            Choice(a, b) => {self.accum_prog(a); self.accum_prog(b)},
            Loop(a, j) => {self.accum_prog(a); self.accum_formula(j)},
        }
    }

    /** Add symbols of term to collection */
    fn accum_term(&mut self, t: &Term) {
        match &t.node {
            ValTerm(_) => {},
            VarTerm(x) => {self.state_vars.insert(x.to_string());},
        }
    }

    /** Add symbols of formula to collection */
    fn accum_formula(&mut self, f: &Formula) {
        match &f.node {
            True() => {()},
            Equal(e1, e2) => {self.accum_term(e1); self.accum_term(e2)},
            Pred(p) => {self.preds.insert(p.to_string()); ()},
            Imply(p, q) => {self.accum_formula(p); self.accum_formula(q)},
            And(p, q) => {self.accum_formula(p); self.accum_formula(q)},
            Or(p, q) => {self.accum_formula(p); self.accum_formula(q)},
            MBox(a, p) => {self.accum_prog(a); self.accum_formula(p)},
            MDiamond(a, p) => {self.accum_prog(a); self.accum_formula(p)},
        }
    }

    /** Collection of symbols mentioned in program */
    pub fn of_prog(a: &Program) -> Self {
        let mut s = Self::empty();
        s.accum_prog(a);
        s
    }

    /** Collection of symbols mentioned in formula */
    pub fn of_formula(f: &Formula) -> Self {
        let mut s = Self::empty();
        s.accum_formula(f);
        s
    }

    /** Whether collection contains given identifier */
    pub fn contains(&self, s: &String) -> bool {
        self.preds.contains(s) || self.symbols.contains(s)
    }

    pub fn state_vars_intersect(&self, vars: &HashSet<String>) -> bool {
        !self.preds.is_empty() || self.state_vars.intersection(vars).count() > 0
    }
    /** State variables computation */
    pub fn state_vars(&self) -> HashSet<String> {
        self.state_vars.clone()
    }
}


/** All disjuncts of given formula.

If formula is not a disjunction, return it as-is. */
pub fn disjuncts(f: &Formula) -> Vec<Formula> {
    let mut ds: Vec<Formula> = Vec::new();
    fn dis(acc: &mut Vec<Formula>, f: &Formula) {
        match &f.node {
            Or(a, b) => {dis(acc, a); dis(acc, b)},
            _ => acc.push(f.clone()),
        }
    }
    dis(&mut ds, f);
    ds
}

/** All conjuncts of given formula.

If formula is not a conjunction, return it as-is. */
pub fn conjuncts(f: &Formula) -> Vec<Formula> {
    let mut cs: Vec<Formula> = Vec::new();
    fn conj(acc: &mut Vec<Formula>, f: &Formula) {
        match &f.node {
            And(a, b) => {conj(acc, a); conj(acc, b)},
            _ => acc.push(f.clone()),
        }
    }
    conj(&mut cs, f);
    cs
}

/** Add dummy location information to AST node */
pub fn sp<T>(t: T) -> Spanned<T> {
  Spanned {node: t, span: Span::DEFAULT }
}
 
/** Build disjunction formula from disjuncts */
pub fn of_disjuncts(inv: &Vec<Formula>) -> Formula {
  let mut fml: Option<Formula> = None;
  for invb in inv {
    let branch = invb.clone();
    match fml {
      None => {fml = Some(branch)},
      Some(f) => {fml = Some(sp(FormulaNode::Or(Box::new(f), Box::new(branch))))}
    }
  }
  return fml.unwrap();
}

/** Build conjunction formula from conjuncts */
pub fn of_conjuncts(inv: &Vec<Formula>) -> Formula {
  let mut fml: Option<Formula> = None;
  for invb in inv {
    let branch = invb.clone();
    match fml {
      None => {fml = Some(branch)},
      Some(f) => {fml = Some(sp(FormulaNode::And(Box::new(f), Box::new(branch))))}
    }
  }
  return fml.unwrap();
}

/** All branches of given choice program.

If program is not a choice, return it as-is. */
pub fn choices(f: &Program) -> Vec<Program> {
    let mut cs: Vec<Program> = Vec::new();
    fn choice(acc: &mut Vec<Program>, prog: &Program) {
        match &prog.node {
            Choice(a, b) => {choice(acc, a); choice(acc, b)},
            _ => acc.push(prog.clone()),
        }
    }
    choice(&mut cs, f);
    cs
}

/** Final conclusion of a nested implication formula.

If formula is not an implication, return it as-is. */
pub fn conclusion(f: &Formula) -> Formula {
    match &f.node {
        Imply(_, q) => conclusion(q),
        _ => f.clone(),
    }
}

/** All assumptions of a nested implication formula. 

If formula is not an implication, returns empty vector.
Conjunctions are left intact. */
pub fn assumptions(f: &Formula) -> Vec<Formula> {
    let mut assumps: Vec<Formula> = Vec::new();
    fn assump(acc: &mut Vec<Formula>, f: &Formula) {
        match &f.node {
            Imply(p, q) => {acc.push(*p.clone()); assump(acc, &q)},
            _ => (),
        }
    }
    assump(&mut assumps, f);
    assumps
}

/** All conjuncts of all assumptions of nested implication formula. */
pub fn assumption_conjs(f: &Formula) -> Vec<Formula> {
    let mut all_conjs: Vec<Formula> = vec![];
    let assumps = assumptions(f);
    for assump in assumps {
        let mut these_conjs = conjuncts(&assump);
        all_conjs.append(&mut these_conjs);
    }
    all_conjs
}

/** Collects predicates that are spread across multiple definitions */
pub fn normalize(lp: LogicProgram) -> CompileResult<LogicProgram> {
    let LogicProgram {body, query} = lp;
    match normalize_body(body) {
        Ok(res) => Ok(LogicProgram {body: res, query}),
        Err(e) => Err(e),
    }
}

/** Collects predicates that are spread across multiple definitions */
pub fn normalize_body(body: Vec<Defn>) -> CompileResult<Vec<Defn>> {
    let mut state_vars: HashMap<String, Spanned<Vec<String>>> = HashMap::new();
    let mut progs: HashMap<String, Program> = HashMap::new();
    let mut atom_preds: HashMap<String, Vec<Formula>> = HashMap::new();
    let mut box_preds: HashMap<String, Vec<Formula>> = HashMap::new();
    let mut diamond_preds: HashMap<String, Vec<Formula>> = HashMap::new();
    for d in body {
        match d.node {
            VarDefn(x, vs) => {
                if state_vars.contains_key(&x.to_string()) {
                    return Err(Spanned{node: "Repeat definitions of state variables are not allowed.".to_string(), span: d.span})
                } else {
                    state_vars.insert(x.to_string(), respan(d.span, vs.clone()));
                }
            }
            ProgDefn(c, a) => {
                if progs.contains_key(&c.to_string()) {
                    return Err(Spanned{node: "Repeat definitions of programs are not allowed.".to_string(), span: d.span})
                } else {
                    progs.insert(c.to_string(), *a.clone());
                }
            }
            PredDefn(mut clauses) => {
                let first_head = conclusion(&clauses[0]);
                if let MBox(s, _) = &first_head.node {
                    if let Symbol(c) = &s.node {
                        box_preds.entry(c.to_string())
                            .and_modify(|acc: &mut Vec<Formula>| acc.append(&mut clauses))
                            .or_insert(clauses);
                    } else { return Err(Spanned{node: "Expected formula to be head but it is not.".to_string(), span: d.span}) }
                } else if let MDiamond(s, _) = &first_head.node {
                    if let Symbol(c) = &s.node {
                        diamond_preds.entry(c.to_string())
                            .and_modify(|acc: &mut Vec<Formula>| acc.append(&mut clauses))
                            .or_insert(clauses);
                    } else { return Err(Spanned{node: "Expected formula to be head but it is not.".to_string(), span: d.span}) }
                } else if let Pred(s) = &first_head.node {
                    atom_preds.entry(s.to_string())
                        .and_modify(|acc: &mut Vec<Formula>| acc.append(&mut clauses))
                        .or_insert(clauses);
                } else { return Err(Spanned{node: "Expected formula to be head but it is not.".to_string(), span: d.span}) }
            }
        }
    }
    let mut state_var_keys: Vec<String> = state_vars.keys().cloned().collect();
    let mut prog_keys: Vec<String> = progs.keys().cloned().collect();
    let mut atom_keys: Vec<String> = atom_preds.keys().cloned().collect();
    let mut box_keys: Vec<String> = box_preds.keys().cloned().collect();
    let mut diamond_keys: Vec<String> = diamond_preds.keys().cloned().collect();
    state_var_keys.sort(); prog_keys.sort(); atom_keys.sort(); box_keys.sort(); diamond_keys.sort();
    let mut defns : Vec<Defn> = Vec::new();
    for k in state_var_keys {
        let got = state_vars.get(&k).unwrap();
        defns.push(respan(got.span, VarDefn(k.clone(), got.node.clone())));
    }
    for k in prog_keys {
        let got = progs.get(&k).unwrap();
        defns.push(respan(got.span, ProgDefn(k.clone(), Box::new(got.clone()))));
    }
    for k in atom_keys {
        let got = atom_preds.get(&k).unwrap().to_vec();
        defns.push(respan(got[0].span, PredDefn(got)));
    }
    for k in box_keys {
        let got = box_preds.get(&k).unwrap().to_vec();
        defns.push(respan(got[0].span, PredDefn(got)));
    }
    for k in diamond_keys {
        let got = diamond_preds.get(&k).unwrap().to_vec();
        defns.push(respan(got[0].span, PredDefn(got)));
    }
    Ok(defns)
}