//! Implementation of a(?) bounded search tree algorithm. 

use crate::vc_instance::VCInstance; 
use crate::kernelization::{Rule};
use crate::cust_error::ProcessingError;
use fxhash::FxHashSet;

impl VCInstance {

    /// A recursive branch and reduce algorithm to find the optimal vertex cover.
    /// To prepare the algorithm computes an initial lower bound and an initial solution.
    /// In every branching step, the algorithm does the following: 
    /// 1. Reduces the instance as far as possible by exhaustively applying all implemented
    ///    reduction rules. 
    /// 2. If the instance is reduced to an empty graph, if the current solution is better
    ///    then the current best (initially the heuristic solution), the current solution is
    ///    returned, else `None` is returned.
    /// 3. Recomputes the lower bound and checks if it is greater or equal to the current best
    ///    solution. Returns `None` in that case.
    /// 4. If the remaining graph is disconnected, starts `branch_and_reduce()` on each component
    ///    of the graph and returnes the collected solution if it is better, than the current best.
    /// (5. Checks if the remaining graph holds a clique of at least size 3 if that is the case
    ///    branches on all possible cases (all nodes but either one-, and all nodes in the solution).) --> Not currently happening
    /// 5. If no clique of size at least 3 was found, branches on the node with the highest degree
    ///    and all of its neighbors.
    /// After each branch the algorithm rebuilds the graph and continues to look for a better
    /// solution.
    ///
    /// A `ProcessingError` should only be thrown if ... TODO
    pub fn branch_and_reduce(&mut self, priority_list: &[Rule]) -> Result<FxHashSet<usize>, ProcessingError> {
        self.compute_and_set_upper_lower(priority_list)?;
        if let Some(solution) = self.branch_and_reduce_inner(priority_list) {
            return Ok(solution)
        }
        Ok(self.current_best.as_ref().expect("was set at the very beginning").clone())
    }

    fn branch_and_reduce_inner(&mut self, priority_list: &[Rule]) -> Option<FxHashSet<usize>> {
        // Reduce instance 
        self.exhaustive_rules(priority_list);
        if self.graph.num_nodes() == 0 {
            if self.solution.len() < self.upper_bound.expect("upper bound was set") {
                // If we use the link node rule, we have to finallize the found solution.
                let sol = self.finallize_solution(&self.solution).expect("Finallizing should not go wrong at empty graph");
                self.update_current_best(&sol);
                return Some(sol);
            } else {
                return None;
            }
        }
        // Compute current lower and compare with current best.
        if self.lower_bound_heuristic(priority_list) >= self.upper_bound.expect("`self.upper_bound` was set") {
            return None
        }
        // Computes CCs indipendently.
        if self.graph.disconnected() {
            let mut solution = self.solution.clone();
            for mut instance in self.graph.split_into_connected().into_iter().map(|graph| VCInstance::new(graph)) {
                solution.extend(instance.branch_and_reduce(priority_list).expect("`branch_and_reduce()` should not fail on a fresh `VCInstance`"));
            }
            if solution.len() < self.upper_bound.expect("upper bound was set") {
                // If we use the link node rule, we have to finallize the found solution.
                let sol = self.finallize_solution(&solution).expect("Finallizing should not go wrong after split");
                self.update_current_best(&sol);
                return Some(sol);
            } else {
                return None;
            }
        }
        // Today we Branch:
        // On cliques 
       // let clique = self.graph.greedy_max_clique();
       // if clique.len() > 2 {
       //     let mut solution_set = clique.clone();
       //     let mut current_best: Option<FxHashSet<usize>> = None;
       //     self.put_register();
       //     self.add_all_to_solution(&solution_set).expect("`solution_set` is in `self.graph`");
       //     if let Some(sol) = self.branch_and_reduce_inner(priority_list) {
       //         current_best = Some(sol);
       //     }
       //     self.rebuild_section();
       //     for node in clique {
       //         self.put_register();
       //         solution_set.remove(&node);
       //         self.add_all_to_solution(&solution_set).expect("`solution_set` is in `self.graph`");
       //         // get neighbors and add them
       //         let nn = self.graph.neighbors(node).as_ref().expect("`node` exists").clone();
       //         self.add_all_to_solution(&nn).expect("`nn` exists");
       //         if let Some(sol) = self.branch_and_reduce_inner(priority_list) {
       //             current_best = Some(sol);
       //         }
       //         self.rebuild_section();
       //         solution_set.insert(node);
       //     }
       //     return current_best
       // } else {
        // On high degree node and neighbors
        // 1. Vertex selection (highest degree, least edges in N(v) 
        let (node, neighbors) = self.graph.max_degree_node_sparse_neighborhood().expect("`self.graph` is not empty");
        // 2. Find mirror 
        let mut mirrors = self.graph.find_mirrors(node, &neighbors);
        mirrors.insert(node);
        // 3. Find Satellite 
        // 4. Packing?
        let mut current_best = None;
        self.put_register();
        self.add_all_to_solution(&mirrors).expect("`mirrors` are in `self.graph`");
        //self.add_to_solution(node);
        if let Some(sol) = self.branch_and_reduce_inner(priority_list) {
            current_best = Some(sol);
        }
        self.rebuild_section();
        self.put_register();
        self.add_all_to_solution(&neighbors).expect("`neighbors` is in `self.graph`");
        self.delete_node(node);
        if let Some(sol) = self.branch_and_reduce_inner(priority_list) {
            current_best = Some(sol);
        }
        self.rebuild_section();
        return current_best
       // }
    }

}

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    use crate::graph::DyUGraph;
    use crate::vc_instance::VCInstance;
    use crate::kernelization::Rule;

    #[test]
    fn branch_and_reduce_test() {
        let gr = Cursor::new("p td 16 33\n1 2\n1 3\n1 4\n1 5\n1 6\n2 3\n2 4\n2 5\n2 10\n\
                              3 4\n3 5\n3 9\n4 5\n4 8\n5 7\n6 11\n6 12\n7 13\n8 14\n\
                              9 15\n10 16\n11 12\n11 13\n11 15\n11 16\n12 13\n12 14\n\
                              12 16\n13 14\n13 15\n14 15\n14 16\n15 16\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        let opt_sol = ins.branch_and_reduce(&[Rule::SimpleRules]);
        assert!(opt_sol.is_ok());
        assert_eq!(opt_sol.unwrap().len(), 10);
    }

    #[test]
    fn branch_and_reduce_intervined_cliques_test() {
        let gr = Cursor::new("p td 12 30\n1 2\n1 3\n1 4\n1 5\n1 9\n2 3\n2 4\n2 6\n2 10\n\
                              3 4\n3 7\n3 11\n4 8\n4 12\n5 6\n5 7\n5 8\n5 9\n6 7\n\
                              6 8\n6 10\n7 8\n7 11\n8 12\n9 10\n9 11\n9 12\n\
                              10 11\n10 12\n11 12\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        let opt_sol = ins.branch_and_reduce(&[Rule::SimpleRules]);
        assert!(opt_sol.is_ok());
        assert_eq!(opt_sol.unwrap().len(), 9);
    }

}
