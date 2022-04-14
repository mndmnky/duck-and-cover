//! Implementation of several heuristics and approximations for the Vertex Cover Problem.
//!
//! Ideas/Todos:
//! * Include cliques in both heuristics. For the upper bound this can only get worse? But for a
//! lower bound this could help.
//! * Prove that lowerbound is sound even if we use reduction rules in between.

use fxhash::FxHashSet;
use crate::cust_error::ProcessingError;
use crate::kernelization::Rule;
use crate::vc_instance::VCInstance;

impl VCInstance {

    /// Approximates the solution by repeatedly adding the nodes of the edge with the highest 
    /// degree to the solution and reduces the graph until no more edge (node) remains.
    /// The resulting solution is, in the worst case twice as large as the optimal solution. 
    ///
    /// Returns the approximated solution.
    pub fn two_approx_high_degree_edges(&self, priority_rules: &[Rule]) -> Result<FxHashSet<usize>, ProcessingError> {
        let mut clone = self.clone();
        loop {
            clone.exhaustive_rules(priority_rules);
            if clone.graph.is_empty() {
                break;
            }
            let max_edge = clone.graph
                .max_edge_by_degree()
                .expect("`clone.graph` is not empty and `Rule::simple_rules` remove \
                        isolated vertices");
            clone.add_to_solution(max_edge.0);
            clone.add_to_solution(max_edge.1);
        }
        clone.finallize_solution_in_place()?;
        Ok(clone.solution)
    }

    /// Computes the lower bound by repeatedly: 
    /// 1. Reducing the graph. 
    /// 2. If a clique > 2 exists: 
    /// 2.1 Remove the largest greedy clique and adds its size - 1 to the lower bound.
    /// 2.2 Else, removes a edge that is connected to the node with the lowest degree and adds 1 to
    ///   the lower bound. 
    /// Until the graph is empty. 
    ///
    /// Returns the computed lower bound.
    pub fn lower_bound_heuristic(&self, priority_rules: &[Rule]) -> usize {
        let mut lower_bound = 0;
        let mut clone_instance = self.clone();
        loop {
            clone_instance.exhaustive_rules(priority_rules);
            if clone_instance.graph.is_empty() {
                break;
            }
            let greedy_max_clique = clone_instance.graph.greedy_max_clique();
            if greedy_max_clique.len() > 2 {
                lower_bound += greedy_max_clique.len() - 1;
                // delete clique 
                clone_instance.graph.delete_nodes(&greedy_max_clique);
            } else {
                let min_edge = clone_instance.graph.min_edge_by_degree().expect("`clone_instance.graph` is not empty.");
                lower_bound += 1;
                clone_instance.graph.delete_node(min_edge.0);
                clone_instance.graph.delete_node(min_edge.1);
            }
        }
        // Adds the remaining solution (original or from the reductions) to the lower bound.
        lower_bound += clone_instance.solution.len();
        lower_bound
    }

    /// Computes an upper bound by repeatedly adding the node with the highest degree to the
    /// solution and reducing the graph regarding to some reduction rules, until the graph is
    /// empty.
    pub fn high_degree_heuristic(&self, priority_rules: &[Rule]) -> Result<FxHashSet<usize>, ProcessingError>  {
        let mut clone = self.clone();
        loop {
            clone.exhaustive_rules(priority_rules);
            if clone.graph.is_empty() {
                break;
            }
            let max_node = clone.graph
                .max_degree_node()
                .expect("`clone.graph` is not empty");
            clone.add_to_solution(max_node);
        }
        clone.finallize_solution_in_place()?;
        Ok(clone.solution)
    }

    pub fn high_weight_heuristic() {
        todo!();
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use crate::graph::DyUGraph;
    use crate::vc_instance::VCInstance;
    use crate::kernelization::Rule;

    #[test]
    fn two_approx_test() {
        let gr = Cursor::new("p cep 16 33\n1 2\n1 3\n1 4\n1 5\n1 6\n2 3\n2 4\n2 5\n2 10\n\
                              3 4\n3 5\n3 9\n4 5\n4 8\n5 7\n6 11\n6 12\n7 13\n8 14\n\
                              9 15\n10 16\n11 12\n11 13\n11 15\n11 16\n12 13\n12 14\n\
                              12 16\n13 14\n13 15\n14 15\n14 16\n15 16\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let ins = VCInstance::new(graph.unwrap());
        let some_sol = ins.two_approx_high_degree_edges(&[Rule::SimpleRules]);
        assert!(some_sol.is_ok());
        assert_eq!(some_sol.unwrap().len(), 10); 
        let lb = ins.lower_bound_heuristic(&[Rule::SimpleRules]);
        assert!((lb == 10) || (lb == 9));
        let some_sol = ins.high_degree_heuristic(&[Rule::SimpleRules]);
        assert!(some_sol.is_ok());
        assert_eq!(some_sol.unwrap().len(), 10); 
    }

}
