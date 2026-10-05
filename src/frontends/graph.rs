/** Generates programs from 2-player pursuit-evasion games on graphs (PEGs).
 * 
 * PEGs are better matched to full PDL than to the demonic fragment, so the encoding 
 * of PEGs in DDLP is inexact: angelic nondeterminism is approximated by guarded demonic nondeterminism.
 * 
 * A PEG specification consists of a directed graph, initial positions for players, strategy for the 
 * Angel player to follow, and invariant position set which should be satisfied after every round.
 */
use crate::ast;
use crate::statics_common;
use crate::statics_common::sp;
use crate::printer_common;
use std::collections::HashMap;
use ast::{Formula,FormulaNode};

/** Vertices are identified by their names, which are strings */
type Vertex = String;

/** A position of a game represents the current state of play. 
 * For a PEG, a game position consists of a pair of locations, 
 * respectively for the (a)ngel and (d)emon players.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct Position {
    /** Name of the vertex where Angel is located */
    pub a: Vertex,
    /** Name of the vertex where Demon is located */
    pub d: Vertex,
}

impl Position {
    /** Convert a position to the name of the predicate that represents it in DDLP code */
    pub fn to_pred(&self) -> String {
        format!("{}-{}", self.a, self.d)
    }
    /** Convert a position to the code that represents it in PDLP code  */
    pub fn to_conj(&self) -> String {
        format!("(a='{} & d='{})", self.a, self.d)
    }
}

/**
 * The Graph struct encodes a complete specification for a graph PEG, including the
 * directed graph structure, the starting position, the strategy taken by Angel,
 * and the invariant set ensured by the strategy.
 * 
 * It is assumed that every vertex has at least one neighbor. Code which violates this
 * assumption can crash with an out-of-bounds error.
 * 
 * The order of elements in the component vectors is not semantically significant;
 * vectors are used to ensure the order of iteration is stable across consecutive
 * executions of the same code, which simplifies unit testing.
 * All of the vectors are mathematically sets; 
 * they are only implemented as vectors to ensure the iteration order is stable.
 */
// Assumption: no isolated nodes
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct Graph {
  /** The collection of vertices that exist in this graph. */
  pub v: Vec<Vertex>,
  /** The collection of directed edges along which players may move.
   * Both players have access to the same motions.
   */
  pub e: Vec<(Vertex, Vertex)>,
  /** The fixed position at which the players start the game. */
  pub pos0: Position,
  /** The strategy by which Angel moves are determined. Angel's move is determined solely
   * by the position. The pair ((a, d), v), where v is a neighbor of a, means Angel moves
   * from a to v. We expect the move to be unique, i.e., no (a, d) should have multiple v's.
   */
  pub strat: Vec<(Position, Vertex)>,
  /** The invariant is a collection of positions: if Angel's winning strategy is correct, then
   * it should ensure that the invariant set is never left, regardless of Demon's actions.
   */
  pub inv: Vec<Position>,
}

impl Graph {
    /** The base identifier used for the program symbol that represents Demon's turn being taken. */
    const DEMON_TURN: &str = "d";
    /** The base identifier used for the program symbol that represents Angel's turn being taken. */
    const ANGEL_TURN: &str = "a";

    /** String representation of vertex n */
    fn verti(n: usize) -> String { format!("v{}", n).to_string() }

    /** On n-vertex graph: suppose demon at b, is angel safe to move to a? */
    fn friendly_verts(n: usize, a: usize, b: usize) -> bool {
        let apred = if a == 0 { n - 1} else {a - 1};
        let anext = if a + 1 == n { 0 } else { a + 1};
        !(a == b || apred == b || anext == b)
    }

    /** Generate a cycle graph with n vertices, assumes v >= 3 */
    pub fn cycle(n: usize) -> Graph {
      let mut v: Vec<String> = vec![];
      for i in 0..n {
        v.push(Self::verti(i));
      }
      let mut e: Vec<(String,String)> = vec![]; 
      for i in 0..n {
        let vert_to = if i + 1 == n { 0 } else { i + 1 };
        e.push((Self::verti(i), Self::verti(vert_to)));
        e.push((Self::verti(vert_to), Self::verti(i)));
      }
      let pos0: Position = Position {a: Self::verti(0), d: Self::verti(2)};
      let mut strat: Vec<(Position, Vertex)> = vec![];
      for aindex in 0..n {
        for dindex in 0..n {
          let pre = if aindex == 0 { n-1 } else { aindex-1 };
          let next = if aindex+1 == n { 0 } else { aindex+1 };
          let pos = Position{a: Self::verti(aindex), d: Self::verti(dindex)};
          if Self::friendly_verts(n, dindex, next) {
            strat.push((pos.clone(), Self::verti(next)));
          }
          if Self::friendly_verts(n, dindex, pre) {
            strat.push((pos, Self::verti(pre)));
          }
        }
      }
      let mut inv: Vec<Position> = vec![];
      /* Strategy allows Angel to move either way as long as not dangerous. */
      for u in 0..n {
        let unext = if u+1 == n { 0 } else { u+1 };
        for v in 0..n {
            let vnext = if v+1 == n { 0 } else { v+1 };
            if u == v || unext == v || vnext == u {
                continue;
            }
            inv.push(Position{a: Self::verti(u), d: Self::verti(v)});
            inv.push(Position{a: Self::verti(v), d: Self::verti(u)});
        }
      }
      Graph {v, e, pos0, strat, inv}
    }

    /**  Vector of all invariants represented as formulas */
    fn inv_fmls_pdlp(&self) -> Vec<Formula>  {
        let mut invs: Vec<Formula> = Vec::new();
        for i in 0..self.inv.len() {
            invs.push(sp(FormulaNode::Pred(self.inv[i].to_conj())));
        }
        invs
    }

    /** Generate a string representing the graph correctness property as a query.
     * The string checks that the invariant is preserved, i.e., it has the format:
     * ?-  /\_{pos \in inv}  (pos -> [demon's turn]<angel's turn> inv)
    */
    pub fn pdlp_query(&self) -> String {
        let invs = self.inv_fmls_pdlp();
        let big_inv = printer_common::formula(&statics_common::of_disjuncts(&invs));
        let mut code = "".to_string();
        for i in 0..self.inv.len() {
            let stri = printer_common::formula(&invs[i]);
            let conj = if i == 0 { "?- " } else {"& "};
            code.push_str(&format!("{}({} -> [{}]<{}>({}))\n",
              conj, stri, Self::DEMON_TURN, Self::ANGEL_TURN, big_inv));
        }
        code.push_str(".");        
        code
    }

    /** Generate a string representing the graph correctness property as a query.
     * The query checks that from the initial position, the invariant is satisfied
     * indefinitely, i.e., it has the format:
     * ?- pos0 -> [(demon's turn';angel's turn)*@inv(invariant property)] invariant property
     */
    pub fn ddlp_query(&self) -> String {
        let mut code = "".to_string();
        let mut invs: Vec<Formula> = Vec::new();
        for i in 0..self.inv.len() {
            invs.push(sp(FormulaNode::Pred(self.inv[i].to_pred())));
        }
        let inv = printer_common::formula(&statics_common::of_disjuncts(&invs));
        code.push_str("?- ");
        code.push_str(&self.pos0.to_pred().to_string());
        code.push_str(" -> [(");
        code.push_str(Self::DEMON_TURN);
        code.push_str(";");
        code.push_str(Self::ANGEL_TURN);
        code.push_str("-turn)*@inv(");
        code.push_str(&inv.to_string());
        code.push_str(")]");
        code.push_str(&inv.to_string());
        code.push_str(".");
        code
    }

    /** Collect all the edges of the graph into Vertex -> Vec<Vertex> a map */
    fn edge_map(&self) -> HashMap<Vertex, Vec<Vertex>> {
        let mut emap: HashMap<Vertex, Vec<Vertex>> = HashMap::new();
        for (u, v) in &self.e {
          emap.entry(u.clone())
            .and_modify(|acc| acc.push(v.clone()))
            .or_insert(vec![v.clone()]);
        }
        emap 
    }

    /** Compute keys of map in a deterministic order */
    fn map_keys(emap: &HashMap<Vertex, Vec<Vertex>>) -> Vec<String> {
        let mut emap_keys : Vec<String> = emap.keys().cloned().collect();
        emap_keys.sort();
        emap_keys
    }

    /** Compute the highest degree of any vertex in the key set.  */
    fn map_degree(emap: &HashMap<Vertex, Vec<Vertex>>, emap_keys: &Vec<String>) -> usize {
        let mut degree: usize = 0;
        for k in emap_keys {
            let v = emap.get(k).unwrap();
            if v.len() > degree {
                degree = v.len();
            }
        }
        degree
    }

    /** Generate string for enum declaration code */
    pub fn declare_enum(&self, name: &str) -> String {
        let mut s = "".to_string();
        let nvals = self.v.len();
        s.push_str(&format!("{} : enum {{",name));
        for j in 0..nvals {
            let delim = if j + 1 == nvals { "}\n" } else { ", "};
            s.push_str(&format!("{}{}", Self::verti(j), delim));
        }
        s
    }

    /**
     * Generates a string for the body of the PDLP program that represents the PEG.
     * let E(u) = vec{v | (u,v) in E}
     * D = max_u |E(u)|
     * Then the program follows this format:
     * wu -> [demon_i]wv where v = E(u)[i], default E(u)[0] if E(u)[i] does not exist for that u.
     * d ::= Union_1^D d_i
     * uv -> <a>wv for (uv, w) in strat
     */
    pub fn to_pdlp_source(&self) -> String {
        let emap: HashMap<Vertex, Vec<Vertex>> = self.edge_map();
        let emap_keys: Vec<String> = Self::map_keys(&emap);
        let degree = Self::map_degree(&emap, &emap_keys);        
        let mut demons: Vec<String> = Vec::new();
        for i in 0..degree {
            demons.push(format!("{}{}",Self::DEMON_TURN,i));
        }
        let mut code = format!("{}{}{} ::= ", 
            self.declare_enum("a"), 
            self.declare_enum("d"),
            Self::DEMON_TURN);
        for i in 0..demons.len()-1 {
            code.push_str(&format!("{} U ", &demons[i]));
        }
        code.push_str(&format!("{}.\n", &demons[demons.len()-1]));
        for k in &emap_keys {
            let val = emap.get(k).unwrap();
            for i in 0..val.len() {
                for w in &self.v {
                    let v = if i < val.len() { &val[i] } else { &val[0] };
                    let wu = Position { a: w.to_string(), d: k.to_string()};
                    let wv = Position { a: w.to_string(), d: v.to_string()};
                    code.push_str(&format!("{} -> [{}]{}.\n", &wu.to_conj(), &demons[i], &wv.to_conj()));
                }
            }
        }
        for (uv, w) in &self.strat {
            let wv = Position {a: w.to_string(), d: uv.d.clone()};
            code.push_str(&format!("{} -> <{}>{}.\n",&uv.to_conj(), Self::ANGEL_TURN, &wv.to_conj()));
        }
        code
    }
    
    /** Both body and query */
    pub fn to_full_pdlp_source(&self) -> String {
        let body = self.to_pdlp_source();
        let query = self.pdlp_query();
        format!("{}\n\n{}", body, query)
    }

    /**
     * Generates a string for the body of the DDLP program that represents the PEG.
     * let E(u) = vec{v | (u,v) in E}
     * D = max_u |E(u)|
     * Then the program follows this format:
     * a-turn ::= cup_(uv in dom(strat)) ?uv; a
     * d ::= Union_1^D d_i
     * wu -> [demon_i]wv where v = E(u)[i], default E(u)[0] if E(u)[i] does not exist for that u.
     * uv -> [angel]wv for (uv, w) in strat
     */
    pub fn to_ddlp_source(&self) -> String {
        let emap: HashMap<Vertex, Vec<Vertex>> = self.edge_map();
        let emap_keys: Vec<String> = Self::map_keys(&emap);
        let degree = Self::map_degree(&emap, &emap_keys);
        let mut demons: Vec<String> = Vec::new();
        for i in 0..degree {
            demons.push(format!("{}{}",Self::DEMON_TURN,i));
        }
        let mut code = "".to_string();
        code.push_str(Self::DEMON_TURN);
        code.push_str(" ::= ");
        for i in 0..demons.len()-1 {
            code.push_str(&demons[i]);
            code.push_str(" U ");
        }
        code.push_str(&demons[demons.len()-1]);
        code.push_str(".\n");
        for k in &emap_keys {
            let val = emap.get(k).unwrap();
            for i in 0..val.len() {
                for w in &self.v {
                    let v = if i < val.len() { &val[i] } else { &val[0] };
                    let wu = Position { a: w.to_string(), d: k.to_string()};
                    let wv = Position { a: w.to_string(), d: v.to_string()};
                    code.push_str(&wu.to_pred());
                    code.push_str(" -> [");
                    code.push_str(&demons[i]);
                    code.push_str("]");
                    code.push_str(&wv.to_pred());
                    code.push_str(".\n");
                }
            }
        }
        for (uv, w) in &self.strat {
            let wv = Position {a: w.to_string(), d: uv.d.clone()};
            code.push_str(&uv.to_pred());
            code.push_str(" -> [");
            code.push_str(Self::ANGEL_TURN);
            code.push_str("]");
            code.push_str(&wv.to_pred());
            code.push_str(".\n");
        }
        let mut angel_branches: Vec<String> = Vec::new();
        code.push_str(Self::ANGEL_TURN);
        code.push_str("-turn ::= ");
        for (uv, _) in &self.strat {
            angel_branches.push(format!["?{}; {}", uv.to_pred(), Self::ANGEL_TURN.to_string()]);
        }
        for i in 0..angel_branches.len()-1 {
            code.push_str(&angel_branches[i]);
            code.push_str(" U ");
        }
        code.push_str(&angel_branches[angel_branches.len()-1]);
        code.push_str(".");
        code
    }
    
    /** Both body and query */
    pub fn to_full_ddlp_source(&self) -> String {
        let body = self.to_ddlp_source();
        let query = self.ddlp_query();
        format!("{}\n\n{}", body, query)
    }

}