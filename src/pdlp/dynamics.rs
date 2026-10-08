/*! Execute logic programs.

The core data structure Machine captures a logic program and its runtime state.
The Goal data structure is used within a Machine to store a formula in a
convenient normal form. The essential methods are the constructor Machine::of_lp
and the execution method Machine::run().

The conceptual and textual overlap with ddlp::dynamics is nontrivial. However, the two
files are maintained separately because
  1) The order of evaluation differs substantially, with left-to-right symbolic execution in DDLP and
     right-to-left execution in PDLP. The data structures required for each are different.
  2) Performance evaluation for optimizations of the PDLP interpreter are easier if the implementations
     are kept largely separate so that DDLP provides a stable baseline for comparison.  
*/
use crate::ast::{Formula,Program,FormulaNode,ProgramNode,DefnNode,LogicProgram,Defn,Term};
use crate::ast::respan as respan;
use crate::ddlp::statics;
use crate::pdlp::{printer,synthesizer::Synthesizer};
use crate::command_line::CommandLineArgs;
use crate::debugger::Debugger;
use crate::ast::{Span,Spanned};
use FormulaNode::*; use ProgramNode::*; use DefnNode::*;
use std::collections::{HashMap,HashSet};
use crate::statics_common;

/** A normal-form (sub)goal to be solved.
Normal form is A1 & ... & AN -> G for goal formula G and clause formulas Ai.
So explicitly separate out Ai's and G. 
No guarantee is made on the order of assumptions in the vector.
They may be reversed, e.g., for performance.
*/
#[derive(Clone,PartialEq,Debug)]
pub struct Goal {
    pub assumps: Vec<Formula>,
    pub concl: Formula,
}

impl Goal {
  /** Initial goal in empty machine to distinguish it from proved machine. */
  pub const INIT: Self = Goal { assumps: vec![], concl: Spanned { node: True(), span: Span::DEFAULT }};

  /** Convert a formula to a goal */
  pub fn of_formula(fml: &Formula) -> Self {
      if let Imply(p, q) = &fml.node {
          let Goal { mut assumps, concl } = Self::of_formula(&q);
          assumps.insert(0,*p.clone());
          Goal { assumps, concl }
      } else { Goal { assumps: vec![], concl: fml.clone() } }
  }

  /** Drop modality of conclusion */
  pub fn unbox_concl(&mut self) {
    match &self.concl.node {
      MBox(_, p) => { self.concl = *p.clone(); },
      _ => (),
    }
  }
}

/** The static part of a machine. See documentation of each field. */
#[derive(Clone,Debug)]
pub struct StaticMachine {
  ////// Static components - do not change at runtime
    /** Represents all explicit state variable definitions, recording the available 
     values for each. Though the *value* of a variable changes throughout program 
     execution, the sets of defined variables and allowed values are static */
    pub var_defns: HashMap<String, Vec<String>>,
    /** Represents all explicitly-defined programs c ::= a as a map of c -> a */
    pub prog_defns: HashMap<String, Program>,
    /** Represents all predicates whose heads are atoms. 
    letting p be an atom with clauses <q_i>, the map stores all p -> <q_i> */
    pub atom_preds: HashMap<String, Vec<Formula>>,
    /** Represents all predicates whose heads are box formulas.
    Letting head [c]p_i be defined by clauses q_ij, the representation is a 
    map c ->  <q_ij>. 
    A given box predicate has a single c, possibly (usually) with multiple p_i. 
    A single predicate can be defined with a mixture of box and diamond clauses, 
    in which case it appears in both maps. */
    pub box_preds: HashMap<String, Vec<Formula>>,
    /** Represents all predicates whose heads are diamond formulas.
    Letting head <c>p_i be defined by clauses q_ij, the representation is a 
     map c ->  <q_ij>. 
    A given diamond predicate has a single c, possibly (usually) with multiple p_i. 
    A single predicate can be defined with a mixture of box and diamond clauses, 
    in which case it appears in both maps. */
    pub diamond_preds: HashMap<String, Vec<Formula>>,
}


impl StaticMachine {
  /** Create new empty static machine */
  pub fn new() -> StaticMachine {
    let var_defns = HashMap::new();
    let prog_defns = HashMap::new();
    let atom_preds = HashMap::new();
    let box_preds = HashMap::new();
    let diamond_preds = HashMap::new();
    StaticMachine { var_defns, prog_defns, atom_preds, box_preds, diamond_preds }    
  }

  fn add_clauses(map: &mut HashMap<String, Vec<Formula>>, key: String, mut value: Vec<Formula>) {
    map.entry(key).and_modify(|acc| { acc.append(&mut value) }).or_insert(value);
  }

  /** If there is no predicate of form p -> [key]q, add [key]true. */
  fn ensure_box_defined(&mut self, span: Span, key: &String) {
    let mut found_me = false;
    if let Some(fmls) = self.box_preds.get(key) {
      for fml in fmls {
        if fml.node == True() {
          found_me = true;
          break;
        }
      }
    }
    if !found_me {
      let sym = Box::new(respan(span, Symbol(key.to_string())));
      let post = Box::new(respan(span, True()));
      let def_clause = respan(span, MBox(sym, post));
      Self::add_clauses(&mut self.box_preds, key.clone(), vec![def_clause]);
    }
  }

  /** Add a definition to a machine */
  pub fn define(&mut self, d: &Defn) {
    match &d.node {
      ProgDefn(c, a) => {self.prog_defns.insert(c.to_string(), *a.clone()); ()},
      PredDefn(clauses) if statics::is_atom(&statics_common::conclusion(&clauses[0])) => {
            let Pred(p) = &statics_common::conclusion(&clauses[0]).node else {panic!("Atom not predicate")} ; 
            Self::add_clauses(&mut self.atom_preds, p.clone(), clauses.clone());
            ()
         },
      // Predicates that define a box/diamond formula
      PredDefn(clauses) => {
          let mut box_inner:  Vec<Formula> = vec![];
          let mut diamond_inner: Vec<Formula> = vec![];
          for clause in clauses {
              if let MBox(_, _) = statics_common::conclusion(clause).node {                  
                box_inner.push(clause.clone());
              } else if let MDiamond(_, _) = statics_common::conclusion(clause).node {  
                diamond_inner.push(clause.clone());
              } else {()} // should never occur for well-formed lp
          }
          let key: String = 
              if let MBox(prog, _) = statics_common::conclusion(&clauses[0]).node {
                  if let Symbol(c) = prog.node {
                      c
                  } else { "IMPOSSIBLE".to_string() }
              } else if let MDiamond(prog, _) = statics_common::conclusion(&clauses[0]).node {
                  if let Symbol(c) = prog.node {
                      c
                  } else { "IMPOSSIBLE".to_string() }
              } else { "IMPOSSIBLE".to_string() };
          if !box_inner.is_empty() {
            Self::add_clauses(&mut self.box_preds, key.clone(), box_inner.clone());
          }
          if !diamond_inner.is_empty() {
            Self::add_clauses(&mut self.diamond_preds, key.clone(), diamond_inner);
            self.ensure_box_defined(d.span, &key);
          }
      },
      VarDefn(x, vs) => {self.var_defns.insert(x.clone(),vs.clone());},
    } 
  }
}


#[derive(Clone,Debug)]
pub struct DynamicMachine {
    ////// Dynamic components - change at runtime
    /** The (sub)goals remaining to be solved. Search proceeds left-to-right.
      A new machine is represented by the single goal True. 
      A proved machine is represented by the empty goal vector. */
    pub goals: Vec<Goal>,
    /** Stack for backtracking proof search. Each entry in the outermost vector corresponds to a point
    where branching occurs in the search. The entry contains all remaining alternatives at that point in
    the search. Each alternative is a vector of all subgoals at that moment. */
    /** TODO: Optimization: in the loop rule, try to prune any branches that are obviously unprovable, to reduce copying later */
    pub stack: Vec<Vec<Vec<Goal>>>,
    /** Remember debug print level, step count, etc. */
    pub d: Debugger,
    /** Extracts a program which satisfies the query through proof search */
    pub syn: Synthesizer,
}

impl DynamicMachine {
  pub fn new() -> Self {
    let goals = vec![Goal::INIT]; // Non-empty so that is_proved() = false
    let stack = vec![];
    let d = Debugger::default();
    let syn = Synthesizer::default();
    DynamicMachine {goals, stack, d, syn}
  }
}

/** The runtime configuration of a logic program. See documentation of each field. */
#[derive(Debug)]
pub struct Machine<'a> {
    pub sm: &'a StaticMachine,
    pub dm: DynamicMachine,
}

impl<'a> Machine<'a> {
  /** Don't deep-copy the program part, just the dynamic part */
  pub fn clone(self: &mut Machine<'a>) -> Machine<'a> {
    let sm = &self.sm;
    let dm = self.dm.clone();
    Machine { sm, dm }
  }

  /** Add a query to a machine as a new subgoal. */
  pub fn inquire(&mut self, f: &Formula) {
    // Special case: if we started with singleton goal True() for empty machine, overwrite. 
    if self.dm.goals.len() == 1 && self.dm.goals[0] == Goal::INIT {
      self.dm.goals[0] = Goal::of_formula(f);
    } else {
      self.dm.goals.push(Goal::of_formula(f));
    }
  }
  
  /** Load static machine */
  pub fn set_static(&mut self, sm: &'a StaticMachine) {
    self.sm = sm;
  }

  /** Remember the command line arguments. */
  pub fn set_command_line(&mut self, ca: &CommandLineArgs) {
    self.dm.d = Debugger::of_command_line(ca);
  }

  /** Create an empty machine.
  
  Mainly used in interactive mode where there are initially no definitions or goals.
  Machine::of_lp is recommended when running a known program.
  */
  pub fn new(sm: &'a StaticMachine) -> Self {
    Machine { sm,  dm: DynamicMachine::new() }
  }

  /** Assumes well-formed logic program */
  pub fn of_lp(sm: &'a mut StaticMachine, lp: &LogicProgram) -> Self {
    for defn in &lp.body {
      sm.define(defn);
    }
    let mut m = Self::new(sm);
    m.inquire(&lp.query);
    m
  }

    /** Replace goal i with goal vector. */
  fn splice_goals(&mut self, i: usize, insert_goals: Vec<Goal>) -> Self {
    let mut new_goals: Vec<Goal> = vec![];
    let Machine { sm, dm } = self.clone();
    let DynamicMachine {d, goals, stack, syn} = dm;
    for j in 0..i {
        new_goals.push(goals[j].clone());
    }
    new_goals.append(&mut insert_goals.clone());
    for j in i+1..goals.len() {
        new_goals.push(goals[j].clone());
    }
    Machine { sm, dm: DynamicMachine {d, goals: new_goals, stack, syn} }
  }

  /** Replace assumption i of goal g with vector of assumptions */
  fn splice_assumps(&self, g: &Goal, i: usize, mut insert_assumps: Vec<Formula>) -> Goal {
    let mut assumps: Vec<Formula> = vec![];
    for j in 0..i {
      assumps.push(g.assumps[j].clone());
    }
    assumps.append(&mut insert_assumps);
    for j in i+1..g.assumps.len() {
      assumps.push(g.assumps[j].clone());
    }
    Goal { assumps, concl: g.concl.clone()}
  }

  /** Whether the machine has succeeded in proving its goal.
  
  Note that this method returns true upon creating an empty machine with 
  the new() constructor because no goal has been set. 
  */
  pub fn is_proved(&self) -> bool {
    self.dm.goals.len() == 0
  }
  
  /** Whether machine has gotten stuck during search and failed to prove. */
  pub fn is_stuck(&mut self) -> bool {
    self.dm.goals.len() != 0 && self.dm.stack.len() == 0 && self.steps().len() == 0
  }

  /** Compute lossless steps applicable to given assumption of a goal. */
  fn left_steps_at_assump(&self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, i: usize, j: usize) {
    let g = &self.dm.goals[i];
    // Hypothesis rule
    if g.assumps.contains(&g.concl) {
      close.push(vec![]);
      return;
    }
    match &g.assumps[j].node {
      And(l, r) => {lossless.push(vec![self.splice_assumps(&g, j, vec![*l.clone(),*r.clone()])]); return;},
      _ => (),
    }
  }
  
  /** Compute steps applicable to any assumption of a goal. */
  fn left_steps_at_goal(&self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, i: usize) {
    let assumps = &self.dm.goals[i].assumps;
    for j in 0..assumps.len() {
      self.left_steps_at_assump(close, lossless, i, j);
      if !close.is_empty() || !lossless.is_empty() {
        return;
      }
    }
  }

  /** If string is defined as an atom predicate, count branches. Else 0. */
  fn atom_pred_arity(&self, p: &String) -> usize {
    match self.sm.atom_preds.get(p) {
      Some(defn) => defn.len(),
      _ => 0,
    }
  }
  
  /** Implement invocation of atom predicates */
  fn atom_pred_case(&self, out: &mut Vec<Vec<Goal>>, g: &Goal, p: &String) {
    match self.sm.atom_preds.get(p) {
      Some(defn) => {
        for clause in defn {
          let mut vec: Vec<Goal> = vec![];
          let assumps = statics_common::assumptions(&clause);
          for assump in assumps {
            vec.push(Goal {assumps: g.assumps.clone(), concl: assump.clone()});
          }
          out.push(vec)
        }
      },
      None => (),
    }
  }

  /** Implement expansion of explicit program definitions. */
  fn box_prog_defn_case(&self, lossless: &mut Vec<Vec<Goal>>, g: &Goal, c: &String, p: Formula) {
    match self.sm.prog_defns.get(c) {
      Some(defn) => lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: respan(defn.span, MBox(Box::new(defn.clone()), Box::new(p)))}]),
      None => (),
    }
  }

  /** Implement expansion of explicit program definitions. */
  fn diamond_prog_defn_case(&self, lossless: &mut Vec<Vec<Goal>>, g: &Goal, c: &String, p: Formula) {
    match self.sm.prog_defns.get(c) {
      Some(defn) => lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: respan(defn.span, MDiamond(Box::new(defn.clone()), Box::new(p)))}]),
      None => (),
    }
  }

  /* @TODO: Search by assumption formulas too not just the program symbol */
  /** If symbol is defined as box predicate with given postcondition, count branches. Else 0 */
  fn symbol_pred_arity(&self, symbol: &String) -> usize {
    let box_arity = 
      if self.sm.box_preds.contains_key(symbol) {
        self.sm.box_preds[symbol].len()
      } else {
        0
      };
    let diamond_arity =
      if self.sm.diamond_preds.contains_key(symbol) {
        self.sm.diamond_preds[symbol].len()
      } else {
        0
      };
    box_arity + diamond_arity
  }

  /** Implement invocation of symbol predicates ending with diamond formulas. */
  fn diamond_pred_case(&self, out: &mut Vec<Vec<Goal>>, g: &Goal, symbol: &String, post: &Formula) {
    let mut ctxt : HashSet<Formula> = HashSet::new();
    for x in &g.assumps {
      ctxt.insert(x.clone());
    }
    let clauses = &self.sm.diamond_preds[symbol];
    for clause in clauses {
      let mut skip = false;
      let assumps = statics_common::assumption_conjs(&clause);
      for assump in &assumps {
        if !ctxt.contains(assump) {
          skip = true;
          break;
        }
      }
      if skip {
        continue;
      }
      let s0 = g.concl.span;
      let concl = statics_common::conclusion(&clause);
      let MDiamond(_, cpost) = &concl.node else { panic!("Bad pattern match in diamond predicate call impl.")};
      let concl_impl = respan(s0, Imply(cpost.clone(), Box::new(respan(s0,post.node.clone()))));
      out.push(vec![Goal {
        assumps: g.assumps.clone(),
        concl: respan(s0, MBox(Box::new(respan(s0,Symbol(symbol.clone()))),Box::new(concl_impl)))
        }]);
    }
  }

  fn box_pred_bound_vars(s: Span, clauses: &Vec<Spanned<FormulaNode>>) -> HashSet<String> {
    let mut acc = respan(s,True());
    for clause in clauses {
      let conc = statics_common::conclusion(clause);
      if let MBox(_, p) = &conc.node {
        acc = respan(s, And(Box::new(acc), p.clone()));
      }
    }
    statics_common::FI::of_formula(&acc).state_vars()
  }

  /** Implement invocation of symbol predicates ending with box  formulas. */
  fn box_pred_case(&self, out: &mut Vec<Vec<Goal>>, g: &Goal, symbol: &String, post: &Formula) {
    let mut ctxt : HashSet<Formula> = HashSet::new();
    let mut kept_assumps : Vec<Formula> = Vec::new();
    let mut fresh_assumps : Vec<Formula> = Vec::new();
    let clauses = &self.sm.box_preds[symbol];
    let bnd_vars = Self::box_pred_bound_vars(g.concl.span, clauses);
    for x in &g.assumps {
      ctxt.insert(x.clone());
      if !statics_common::FI::of_formula(x).state_vars_intersect(&bnd_vars) {
        kept_assumps.push(x.clone());
      }
    }
    for clause in clauses {
      let mut skip = false;
      let assumps = statics_common::assumption_conjs(&clause);
      for assump in &assumps {
        if !ctxt.contains(assump) {
          skip = true;
          break;
        }
      }
      if skip {
        continue;
      }
      let s0 = g.concl.span;
      let MBox(_, fa) = statics_common::conclusion(&clause).node else { panic!("Type error") };
      fresh_assumps.push(*fa);
      kept_assumps.append(&mut fresh_assumps);
      out.push(vec![Goal {
        assumps: kept_assumps.clone(),
        concl: respan(s0, post.node.clone()),}]);
    }
  }

  /** Return whether g contains any assumptions that assign a value inconsistent with l1=r1 */
  fn conj_contradicts_assumptions(&self, g: &Goal, l1: &Term, r1: &Term) -> bool {
    for assump in &g.assumps {
      match &assump.node {
        Equal(l2, r2) => {
          if *l1 == **l2 && *r1 != **r2 {
            return true;
          }
        },
        _ => {},
      }
    }
    false
  }

  /** Return whether any x is assigned inconsistently by some conjunct of p and assumption of g */
  fn contradicts_assumptions(&self, g: &Goal, p: &Formula) -> bool {
    let conjs = statics_common::conjuncts(p);
    for conj in &conjs {
      match &conj.node {
        Equal(l1, r1) => {
          if self.conj_contradicts_assumptions(g, &*l1, &*r1) {
            return true;
          }
        },
        _ => {continue;}
      }
    }
    false
  }
  /** Lossless steps applicable to conclusion of given goal. */
  fn right_steps_at_goal(&mut self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, lossy: &mut Vec<Vec<Goal>>, i: usize) {
    let g = &self.dm.goals[i];
    let s0 = g.concl.span;
    match &g.concl.node {
      MBox(prog, p) => {
        match &prog.node {
          Seq(a, b) => {
            let (s1, s2) = (a.span, b.span);
            lossless.push(vec![Goal { 
              assumps: g.assumps.clone(), 
              concl: respan(s1, MBox(a.clone(), Box::new(respan(s2, MBox(b.clone(), p.clone())))))}]);
          },
          Choice(a, b) => {
            let (s1, s2) = (a.span, b.span);
            lossless.push(vec![Goal {
              assumps: g.assumps.clone(),
              concl: respan(s0, And(Box::new(respan(s1,MBox(a.clone(), p.clone()))), Box::new(respan(s2,MBox(b.clone(), p.clone())))))
            }])
          },
          Test(q) => {
            lossless.push(vec![Goal {
              assumps: g.assumps.clone(),
              concl: respan(s0, Imply(q.clone(), p.clone()))}]);
          },
          Loop(a, inv) => {
            let invs = statics_common::disjuncts(&inv);
            let mut preserves: Vec<Goal> = vec![];
            let mut posts: Vec<Goal> = vec![];
            let mut all_goals: Vec<Goal> = vec![];
            for j in invs {
              preserves.push(Goal {assumps: vec![j.clone()], concl: respan(g.concl.span,MBox(a.clone(), inv.clone())) });
              posts.push(Goal {assumps: vec![j], concl: *p.clone() });
            }
            let pre: Goal = Goal { assumps: g.assumps.clone(), concl: *inv.clone()};
            all_goals.push(pre); all_goals.append(&mut preserves); all_goals.append(&mut posts);
            lossless.push(all_goals);
          },
          Symbol(c) => {
            match self.symbol_pred_arity(&c) {
              1 => self.box_pred_case(lossless, &g, &c, p),
              0 => self.box_prog_defn_case(lossless, &g, &c, *p.clone()),
              _ => self.box_pred_case(lossy, &g, &c, p),
            }
          },
        }
      },
      MDiamond(prog, p) => {
        match &prog.node {
          Seq(a, b) => {
            let s2 = b.span;
            lossless.push(vec![Goal { 
              assumps: g.assumps.clone(), 
              concl: respan(s0, MDiamond(a.clone(), Box::new(respan(s2, MDiamond(b.clone(), p.clone())))))}]);
          },
          Choice(a, b) => {
            let (s1, s2) = (a.span, b.span);
            lossless.push(vec![Goal {
              assumps: g.assumps.clone(),
              concl: respan(s0, Or(Box::new(respan(s1,MDiamond(a.clone(), p.clone()))),
                                   Box::new(respan(s2,MDiamond(b.clone(), p.clone()))))),
            }])
          },
          Test(q) => {
            lossless.push(vec![Goal {
              assumps: g.assumps.clone(),
              concl: respan(s0, And(q.clone(), p.clone()))
            }])
          },
          Loop(a, b) => {
            let s1 = a.span;
            lossless.push(vec![Goal {
              assumps: g.assumps.clone(),
              concl: respan(s0, Or(p.clone(), 
                Box::new(respan(s1, MDiamond(a.clone(), Box::new(respan(s0, 
                  MDiamond(Box::new(respan(s0, Loop(a.clone(),b.clone()))),p.clone()))))))))
            }])
          },
          Symbol(c) => {
            match self.symbol_pred_arity(&c) {
              1 => self.diamond_pred_case(lossless, &g, &c, p),
              0 => self.diamond_prog_defn_case(lossless, &g, &c, *p.clone()),
              _ => self.diamond_pred_case(lossy, &g, &c.clone(), p),
            }
          },
        }
      },
      And(p, q) => {
        lossless.push(vec![
          Goal {assumps: g.assumps.clone(), concl: *p.clone()},
          Goal {assumps: g.assumps.clone(), concl: *q.clone()},]);
      },
      Imply(p, q) => {
        if self.contradicts_assumptions(&g.clone(), &p) {
          close.push(vec![]);
        } else {
          let mut assumps = g.assumps.clone();
          assumps.push(*p.clone());
          lossless.push(vec![Goal {assumps, concl: *q.clone()},])
        }
      },
      Or(p, q) => {
        lossy.push(vec![Goal {assumps: g.assumps.clone(), concl:*p.clone()}]);
        lossy.push(vec![Goal {assumps: g.assumps.clone(), concl:*q.clone()}]);
      },
      True() => close.push(vec![]),
      Pred(p) => {
        match self.atom_pred_arity(&p) {
          1 => self.atom_pred_case(lossless, &g, &p),
          0 => (),
          _ => self.atom_pred_case(lossy, &g, &p.clone()),
        }
      },
      _ => (),
    }
  }
  /** All steps applicable to given goal.

  Returns a nested vector <v_i> of successors to goal g_j.
  Each step replaces the single goal g_j by all of v_i.
  For example, v_i = <> represents closing a goal,
   v_i = <g_j'> represents replacing g_j by g_j', and
   v_i = <g_1, g_2> replaces g_j by two goals g_1 and g_2.
 */
  fn steps_at_goal(&mut self, i: usize) -> Vec<Vec<Goal>>{
    let mut closing_steps = vec![];
    let mut lossless_steps = vec![];
    let mut lossy_steps = vec![];
    self.left_steps_at_goal(&mut closing_steps, &mut lossless_steps, i);
    self.right_steps_at_goal(&mut closing_steps, &mut lossless_steps, &mut  lossy_steps, i);
    if !closing_steps.is_empty() {
      return closing_steps;
    } else if !lossless_steps.is_empty() {
      return lossless_steps;
    } else {
      return lossy_steps;
    }
  }

  /** Given a machine, what are all possible machines it can step to? */
  pub fn steps(&mut self) -> Vec<Self> {
    let mut successors: Vec<Self> = vec![];
    if self.dm.goals.is_empty() {
      return successors;
    }
        
    /* Enforce left-to-right execution order. If the first goal is stuck, the entire
     * proof is stuck and it's better to discover early. */
    let goal_vecs = self.steps_at_goal(0);
    for goal_vec in &goal_vecs {
      let new_mach = self.splice_goals(0, goal_vec.to_vec());
      successors.push(new_mach);
    }
    successors
  }
  /** Perform proof search. */
  pub fn run(&mut self)  {
    loop {
      if self.dm.d.verbosity().is_debug() {
        //println!("{}", printer::machine(self));
        self.dm.d.step();
      }
      if self.dm.d.terminated() {
        return;
      }
      if self.is_proved() {
        return;
      }
      let mut succs = self.steps();
      if succs.len() == 1 {
        *self = succs.remove(0);
      } else if succs.len() > 1 {
        // removes first element in place.
        *self = succs.remove(0);
        let mut alts = vec![];
        for succ in succs {
          alts.push(succ.dm.goals);
        }
        self.dm.stack.push(alts);
      } else {
        while !self.dm.stack.is_empty() && self.dm.stack.last().expect("NONEMPTY").is_empty() {
          self.dm.stack.pop();
        }
        if self.dm.stack.is_empty() {
          return;
        } else {
          let mut alts = self.dm.stack.pop().expect("NONEMPTY");
          let alt = alts.remove(0);
          self.dm.goals = alt;
          self.dm.stack.push(alts);
        }
      }
    }
  }
}
