use std::cmp::max;

use im::{hashmap, hashset, HashMap, HashSet};

use crate::expr::{free_vars_defn, Defn, Expr, Loc, Reg};
use heuristic_graph_coloring::*;

pub fn reg_alloc(defn: &Defn, free_xs: &HashSet<String>, regs: &[Reg], offset: usize) -> Alloc {
    let res = alloc_locals(defn, free_xs, regs, offset).concat(alloc_params(defn));
    // println!("TRACE: reg_alloc with {regs:?} = {res:?}");
    res
}

#[derive(Debug)]
pub struct Alloc(HashMap<String, Loc>, usize);

impl Alloc {
    pub fn lookup_var(&self, x: &str) -> Loc {
        match self.0.get(x) {
            None => panic!("Unbound variable {}", x),
            Some(loc) => *loc,
        }
    }

    pub fn used_regs(&self) -> Vec<Reg> {
        let regs: HashSet<Reg> = self
            .0
            .values()
            .filter_map(|l| if let Loc::Reg(r) = l { Some(*r) } else { None })
            .collect();
        let mut regs: Vec<Reg> = regs.into_iter().collect();
        regs.sort();
        regs
    }

    pub fn stack_size(&self) -> usize {
        self.0
            .values()
            .filter_map(|l| match l {
                Loc::Stack(i) if *i >= 0 => Some(*i),
                _ => None,
            })
            .max()
            .unwrap_or(0) as usize
    }

    fn concat(self, other: Alloc) -> Alloc {
        let n = max(self.1, other.1);
        Alloc(self.0.into_iter().chain(other.0).collect(), n)
    }

    pub fn num_regs(&self) -> usize {
        self.1
    }
}

// --------------------------------------------------------------------------------------------------
// Compute the Alloc for local variables of a function definition
// --------------------------------------------------------------------------------------------------

fn alloc_locals(defn: &Defn, free_xs: &HashSet<String>, regs: &[Reg], offset: usize) -> Alloc {
    let mut graph = ConflictGraph::new();
    // 1. add conflicts for free vars
    for x in free_xs {
        graph.add_variable(x);
        for y in free_xs {
            if x != y {
                graph.add_conflict(x, y);
            }
        }
    }
    // 2. add conflicts for body
    let params = HashSet::from(&defn.params);
    live(&mut graph, &defn.body, &hashset! {}, &params, &hashset! {});

    // 3. allocate local binders and free vars
    Alloc(graph.allocate(regs, offset), regs.len())
}

// --------------------------------------------------------------------------------------------------
// Compute the Alloc for parameters of a function definition
// --------------------------------------------------------------------------------------------------

fn alloc_params(defn: &Defn) -> Alloc {
    let mut alloc = hashmap! {};

    let defn_name = if let Some(name) = &defn.name {
        name
    } else {
        ""
    };
    let mut params = vec![defn_name];

    for param in &defn.params {
        params.push(param)
    }
    for (i, param) in params.into_iter().enumerate() {
        let pos = -2 - (i as i32);
        alloc.insert(param.to_string(), Loc::Stack(pos));
    }
    Alloc(alloc, 0)
}

// --------------------------------------------------------------------------------------------------
// Find the live-variables and conflicts of an `Expr`
// --------------------------------------------------------------------------------------------------

#[allow(unused_variables)]
fn live(
    graph: &mut ConflictGraph,
    e: &Expr,
    binds: &HashSet<String>,
    params: &HashSet<String>,
    out: &HashSet<String>,
) -> HashSet<String> {
    // We do not allow for duplicate variables in this
    match e {
        Expr::Num(_) | Expr::Input | Expr::True | Expr::False => out.clone(),
        Expr::Let(x, e1, e2) => {
            // out2 = live(e2, out)
            // out1 = live(e1, out2 - x)
            // Add conflicts in graphs
            //
            // For each y in out2 graph.add_conflict(x, y) we also need to create a vertex for x
            let out2 = live(graph, e2, binds, params, out);
            let out1 = live(graph, e1, binds, params, &out2.without(x));
            // Add conflicts
            graph.add_variable(x);
            for y in out2.clone() {
                graph.add_conflict(x, &y);
            }
            return out1;
        }
        Expr::Add1(e)
        | Expr::Sub1(e)
        | Expr::Neg(e)
        | Expr::Break(e)
        | Expr::Print(e)
        | Expr::Get(e, _) => live(graph, e, binds, params, out),
        Expr::Loop(e) => {
            let new_out = live(graph, e, binds, params, out);
            let return_set = out.clone().union(new_out);
            return return_set;
            // Need to make sure that conflicts at the bottom and the top are accounted for
        }
        Expr::Var(x) => live_var(x, params, out),
        Expr::Plus(e1, e2)
        | Expr::Mult(e1, e2)
        | Expr::Eq(e1, e2)
        | Expr::Le(e1, e2)
        | Expr::Vek(e1, e2) => {
            // new_set = live(e2, out)
            // live(e1, new_set)
            let new_set = live(graph, e2, binds, params, out);
            live(graph, e1, binds, params, &new_set)
        }
        Expr::If(e1, e2, e3) => {
            // new_set1 = live(e2, out)
            // new_set2 = live(e3, out)
            // new_set 3 = new_set1 U new_set2
            // live(e1, new_set3)
            let new_set1 = live(graph, e2, binds, params, out);
            let new_set2 = live(graph, e3, binds, params, out);
            let new_set3 = new_set1.clone().union(new_set2.clone());
            println!(
                "The then expression is {:?} and the live vars are {:?}",
                e2,
                new_set1.clone()
            );
            println!(
                "The else expression is {:?} and the live vars are {:?}",
                e3,
                new_set2.clone()
            );
            println!("The union is {:?}", new_set3.clone());

            live(graph, e1, binds, params, &new_set3)
        }
        Expr::Set(x, e1) => {
            // out + x + live(e1)
            let out1 = live(graph, e1, binds, params, out);
            out1.union(hashset! {x.clone()})
        }
        Expr::Block(es) => {
            // Union of live of all es in reverse?
            let mut new_set = out.clone();
            for e in es {
                new_set = new_set
                    .clone()
                    .union(live(graph, e, binds, params, &new_set));
            }
            return new_set;
        }
        Expr::Call(f, es) => {
            // Similar to plus, but we have to union up everything starting from f
            let mut new_set = out.clone().union(hashset! {f.clone()});
            for e in es {
                new_set = new_set
                    .clone()
                    .union(live(graph, e, binds, params, &new_set));
            }
            return new_set;
        }
        Expr::Fun(defn) => out
            .clone()
            .union(free_vars_defn(defn).difference(params.clone())),
    }
}

fn live_var(x: &String, params: &HashSet<String>, out: &HashSet<String>) -> HashSet<String> {
    if params.contains(x) {
        out.clone()
    } else {
        out.clone().union(hashset! {x.clone()})
    }
}

// --------------------------------------------------------------------------------------------------
// Conflict Graph Structure: used to record conflicts between variables and then compute coloring
// --------------------------------------------------------------------------------------------------

struct ConflictGraph {
    /// Number of vertices in the graph
    vars: usize,
    /// Edges in the graph
    edges: HashSet<(usize, usize)>,
    /// Map from identifiers to vertex index
    idents: HashMap<String, usize>,
}

impl ConflictGraph {
    fn new() -> Self {
        Self {
            vars: 0,
            edges: HashSet::new(),
            idents: HashMap::new(),
        }
    }

    fn add_variable(&mut self, x: &str) -> usize {
        let x = *self.idents.entry(x.to_string()).or_insert_with(|| {
            let idx = self.vars;
            self.vars += 1;
            idx
        });
        x
    }

    fn add_conflict(&mut self, x: &str, y: &str) {
        let x = self.add_variable(x);
        let y = self.add_variable(y);
        self.edges.insert((x, y));
    }

    fn color(&self) -> HashMap<String, usize> {
        let mut graph = VecVecGraph::new(self.vars);
        for (x, y) in &self.edges {
            graph.add_edge(*x, *y);
        }
        let node_colors = color_greedy_by_degree(&graph);
        let mut colors = HashMap::new();
        for (x, i) in &self.idents {
            colors.insert(x.clone(), node_colors[*i]);
        }
        colors
    }

    #[allow(unused_mut)]
    #[allow(unused_variables)]
    fn allocate(&self, regs: &[Reg], offset: usize) -> HashMap<String, Loc> {
        let n = regs.len();
        let colors = self.color();
        let mut alloc = HashMap::new();
        // Same color = Same locs
        // More colors than regs means we need stacks
        // More regs means easier to allocate
        let num_colors = if colors.len() == 0 {
            0
        } else {
            *colors
                .values()
                .max()
                .expect("Invalid coloring done on graph")
        };
        let num_colors = num_colors + 1;
        let entries: Vec<(&String, &usize)> = colors.iter().collect();
        if n >= num_colors {
            // More regs than colors means just allocate off
            for i in 0..entries.len() {
                let (variable, coloring) = entries[i];
                let register = regs[*coloring];
                alloc.insert(variable.to_string(), Loc::Reg(register));
            }
        } else {
            // More colors than regs, we need stack spots
            // Colors are 0, 1 and 2 and regs are 0 and 1
            // So if coloring is < n we can use regs otherwise go for colors
            let mut stack_pos = offset + 1;
            let mut offset_map: HashMap<usize, usize> = HashMap::new(); // Map from coloring to
                                                                        // offset
            for i in 0..entries.len() {
                let (variable, coloring) = entries[i];
                if *coloring >= n {
                    // Use a stack spot here
                    // Check if this mapping exists
                    // if offset_map.contains_key(coloring) {
                    // If it does get it from the offset
                    // map
                    // alloc.insert(
                    // variable.to_string(),
                    // Loc::Stack(*offset_map.get(coloring).unwrap() as i32),
                    // );
                    // }
                    // Otherwise create a new mapping and insert it
                    //  else {
                    alloc.insert(variable.to_string(), Loc::Stack(stack_pos as i32));
                    // offset_map.insert(*coloring, stack_pos);
                    stack_pos = stack_pos + 1;
                    // }
                } else {
                    let register = regs[*coloring];
                    alloc.insert(variable.to_string(), Loc::Reg(register));
                }
            }
        }

        //todo!("use `colors` to fill in the values for `alloc`");

        alloc
    }
}

// --------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_more_colors() {
        let mut cg = ConflictGraph::new();
        cg.add_conflict("x", "y");
        cg.add_conflict("y", "z");
        cg.add_conflict("x", "z");
        cg.add_conflict("z", "w");
        // let coloring = cg.color();
        // println!("{:?}", coloring);
        let coloring = cg.allocate(&[Reg::R8, Reg::R9], 0);
        println!("{:?}", coloring)
    }
    #[test]
    fn test_equal_regs() {
        let mut cg = ConflictGraph::new();
        cg.add_conflict("x", "y");
        cg.add_conflict("y", "z");
        cg.add_conflict("x", "z");
        cg.add_conflict("z", "w");
        // let coloring = cg.color();
        // println!("{:?}", coloring);
        let coloring = cg.allocate(&[Reg::R8, Reg::R9, Reg::R10], 0);
        println!("{:?}", coloring)
    }
    #[test]
    fn test_more_regs() {
        let mut cg = ConflictGraph::new();
        cg.add_conflict("x", "y");
        cg.add_conflict("y", "z");
        cg.add_conflict("x", "z");
        cg.add_conflict("z", "w");
        // let coloring = cg.color();
        // println!("{:?}", coloring);
        let coloring = cg.allocate(&[Reg::R8, Reg::R9, Reg::R10, Reg::R15], 0);
        println!("{:?}", coloring)
    }

    #[test]
    fn test_no_regs() {
        let mut cg = ConflictGraph::new();
        cg.add_conflict("x", "y");
        cg.add_conflict("y", "z");
        cg.add_conflict("x", "z");
        cg.add_conflict("z", "w");
        // let coloring = cg.color();
        // println!("{:?}", coloring);
        let coloring = cg.allocate(&[], 0);
        println!("{:?}", coloring)
    }
}
