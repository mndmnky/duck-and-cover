use crate::graph::DyUGraph;
use fxhash::FxHashSet;
use crate::kernelization::Rule;
use crate::cust_error::ProcessingError;
use crate::bipart_flow::BipartFlowNet;
use std::io::Write;
use std::io;

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct VCInstance {
    pub graph: DyUGraph,
    pub solution: FxHashSet<usize>,
    pub lower_bound: Option<usize>,
    pub upper_bound: Option<usize>,
    pub current_best: Option<FxHashSet<usize>>,
    /// Maintains a flow network while processing.
    pub flow_net: Option<BipartFlowNet>,
    /// If any element in `Item.0` is not in the solution, convert the placeholder to `Item.1.0`,
    /// or else to `Item.1.1`.
    conversion: Vec<(FxHashSet<usize>, (usize, usize))>,
    /// Records changes to the adjacency list.
    alterations: Vec<Alteration>,
    /// An id register, that helps to control how much of the graph is rebuild.
    register: Vec<usize>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
enum Alteration {
    DeleteNode(usize, FxHashSet<usize>),
    AddNode(usize, FxHashSet<usize>),
    /// Contracted `link` and merged `from` into `into`. 
    /// `old_from` gives the old neighbors of `from` and `new_into` the new neighbors of `into`.
    ContractLink{ 
        link: usize, 
        from: usize, 
        into: usize, 
        old_from: FxHashSet<usize>, 
        new_into: FxHashSet<usize>
    },
    /// Contract `twins` and merged `trips` into the single node `trips[2]`.
    /// `old_from1` holds the old neighbors of `trips[0]`, `old_from2` resp. for `trips[1]`,
    /// `new_into` the new neighbors of `trips[2]`.
    ContractTwins{
        twins: [usize; 2],
        trips: [usize; 3],
        old_from1: FxHashSet<usize>,
        old_from2: FxHashSet<usize>,
        new_into: FxHashSet<usize>,
    },
    SubstitudeAlternatives(Vec<(usize, usize)>, usize),
}


impl VCInstance {

    pub fn new(graph: DyUGraph) -> Self {
        VCInstance {  
            graph,
            solution: FxHashSet::default(),
            lower_bound: None,
            upper_bound: None,
            current_best: None,
            flow_net: None,
            alterations: Vec::new(),
            register: vec![0],
            conversion: Vec::new(),
        }
    }

    /// Adds `node` to `self.solution` and removes it from `self.graph`. 
    /// Returns `true` and records the alteration if a node was added, returns `false` otherwise.
    pub fn add_to_solution(&mut self, node: usize) -> bool {
        if let Some(old_neighbors) = self.graph.delete_node(node) {
            self.alterations.push(Alteration::AddNode(node, old_neighbors.clone()));
            self.solution.insert(node);
            if let Some(ref mut flow_net) = self.flow_net {
                flow_net.remove(node);
            }
            return true
        }
        false
    }

    /// Adds all nodes in `node_set` to `self.solution` and removes them from `self.graph`. 
    /// Returns `Ok` and records the alteration if all nodes were added, returns a `ProcessingError` otherwise.
    pub fn add_all_to_solution(&mut self, node_set: &FxHashSet<usize>) -> Result<(), ProcessingError> {
        for node in node_set {
            if let Some(old_neighbors) = self.graph.delete_node(*node) {
                self.alterations.push(Alteration::AddNode(*node, old_neighbors.clone()));
                self.solution.insert(*node);
                if let Some(ref mut flow_net) = self.flow_net {
                    flow_net.remove(*node);
                }
            } else {
                return Err(ProcessingError::InvalidParameter("Given node set was not completely contained in the graph.".to_owned()))
            }
        }
        Ok(())
    }

    /// Removes all nodes in `node_set` from `self.graph`. 
    /// Returns `Ok` and records the alteration if all nodes were removed, returns a `ProcessingError` otherwise.
    pub fn delete_all_nodes(&mut self, node_set: &FxHashSet<usize>) -> Result<(), ProcessingError> {
        for node in node_set {
            if let Some(old_neighbors) = self.graph.delete_node(*node) {
                self.alterations.push(Alteration::DeleteNode(*node, old_neighbors.clone()));
                if let Some(ref mut flow_net) = self.flow_net {
                    flow_net.remove(*node);
                }
            } else {
                return Err(ProcessingError::InvalidParameter("Given node set was not completely contained in the graph.".to_owned()))
            }
        }
        Ok(())
    }

    /// Removes `node` from `self.graph`. 
    /// Returns `true` and records the alteration if a node was removed, returns `false` otherwise.
    pub fn delete_node(&mut self, node: usize) -> bool {
        if let Some(old_neighbors) = self.graph.delete_node(node) {
            self.alterations.push(Alteration::DeleteNode(node, old_neighbors.clone()));
            if let Some(ref mut flow_net) = self.flow_net {
                flow_net.remove(node);
            }
            return true
        }
        false
    }

    // -------------------------- TODO maintaining flow_net from here ----------------

    /// Contracts `link` and merges `from` into `into`. 
    /// Returns false if either of the given node does not exist.
    ///
    /// This can lead to erroneous behaviour if there exists an edge between `from` and `into` or
    /// if `link` is not a link node.
    pub (crate) fn contract_link_node(&mut self, link: usize, from: usize, into: usize) -> Result<(), ProcessingError> {
        if self.graph.delete_node(link).is_none() {
            return Err(ProcessingError::InvalidParameter("`link` was not contained in the graph.".to_owned()))
        }
        if let Some((old_from, new_into)) = self.graph.merge_nodes(from, into) {
            // Inserts a placeholder into the solution. Depending on the presense of `into` in the
            // final solution, this will either become `link` or `from`.
            self.solution.insert(self.graph.num_reserved() + self.conversion.len());
            self.conversion.push((vec![into].into_iter().collect(), (from, link)));
            self.alterations.push(Alteration::ContractLink{ link, from, into, old_from, new_into });
            return Ok(())
        } else {
            self.graph.reinsert_node(link, &vec![from, into].iter().copied().collect());
            return Err(ProcessingError::GraphError("`from` could not be merged into `into`".to_owned()))
        }
    }

    /// Contracts twin nodes `twins` and their neighbors `trips` into a single node, only done if
    /// there is no edge between `trips` (not checked).
    pub (crate) fn contract_twins(&mut self, trips: [usize; 3], twins: [usize; 2]) -> Result<(), ProcessingError> {
        if self.graph.delete_node(twins[0]).is_none() || 
            self.graph.delete_node(twins[1]).is_none() {
            return Err(ProcessingError::InvalidParameter("`link` was not contained in the graph.".to_owned()))
        }
        if let Some((old_from1, old_from2, new_into)) = self.graph.merge_triples((trips[0], trips[1]), trips[2]) {
            // Inserts a placeholder into the solution. Depending on the presense of `into` in the
            // final solution, this will either become `link` or `from`.
            self.solution.insert(self.graph.num_reserved() + self.conversion.len());
            self.conversion.push((vec![trips[2]].into_iter().collect(), (trips[0], twins[0])));
            self.solution.insert(self.graph.num_reserved() + self.conversion.len());
            self.conversion.push((vec![trips[2]].into_iter().collect(), (trips[1], twins[1])));
            self.alterations.push(Alteration::ContractTwins{ twins, trips, old_from1, old_from2, new_into });
            return Ok(())
        } else {
            self.graph.reinsert_node(twins[0], &trips.iter().copied().collect());
            self.graph.reinsert_node(twins[1], &trips.iter().copied().collect());
            return Err(ProcessingError::GraphError("`from` could not be merged into `into`".to_owned()))
        }
    }

    /// Removes the two alternative sets `a_set` and `b_set`, adds `a_set.len()` many placeholder
    /// to the solution, and adds missing edges between the two node disjunct sets `a_neighbors`
    /// and `b_neighbors`.
    pub (crate) fn replace_alternatives(&mut self, a_set: FxHashSet<usize>, b_set: FxHashSet<usize>, a_neighbors: &FxHashSet<usize>, b_neighbors: &FxHashSet<usize>) -> Result<(), ProcessingError> {
        self.delete_all_nodes(&a_set)?;
        self.delete_all_nodes(&b_set)?;
        let missing_edges = self.graph.add_all_missing_edges_between(a_neighbors, b_neighbors)?;
        let mut b_iter = b_set.iter();
        for &a in &a_set {
            let b = b_iter.next().expect("`a_set.len()` == `b_set.len()`");
            self.solution.insert(self.graph.num_reserved() + self.conversion.len());
            self.conversion.push((a_neighbors.clone(), (*b, a)));
        }
        self.alterations.push(Alteration::SubstitudeAlternatives(missing_edges, a_set.len()));
        Ok(())
    }

    /// Computes and sets a upper and a lower bound.
    pub fn compute_and_set_upper_lower(&mut self, priority_rules: &[Rule]) -> Result<(), ProcessingError> {
        self.update_lower_bound(self.lower_bound_heuristic(priority_rules));
        self.update_current_best(&self.high_degree_heuristic(priority_rules)?);
        Ok(())
    }

    /// Returns the effective lower bound of the remaining graph. 
    /// TODO: double check if we can use the effective_lower_bound this way.
    pub fn effective_lower_bound(&self) -> Option<usize> {
        self.lower_bound.map(|lb| lb-self.solution.len())
    }

    /// Returns the effective upper bound of the remaining graph.
    pub fn effective_upper_bound(&self) -> Option<usize> {
        self.upper_bound.map(|ub| ub-self.solution.len())
    }

    /// Updates the lower bound. 
    pub fn update_lower_bound(&mut self, lb: usize) {
        if let Some(ref mut lower) = self.lower_bound {
            if &lb > lower {
                *lower = lb
            }
        } else {
            self.lower_bound = Some(lb); 
        }
    }

    /// Updates the current best solution and the upper bound. 
    /// TODO: test
    pub fn update_current_best(&mut self, some_sol: &FxHashSet<usize>) {
        if let Some(ref mut current_best) = self.current_best {
            if some_sol.len() < current_best.len() {
                *current_best = some_sol.clone();
                self.upper_bound = Some(some_sol.len());
            }
        } else {
            self.upper_bound = Some(some_sol.len());
            self.current_best = Some(some_sol.clone());
        }
    }

    /// Replaces the placeholders from the `LinkNode`-rule in a final solution with the respective
    /// correct node. 
    ///
    /// Attention: This can not be redone, and if the solution is not final, this can lead to
    /// erroneous behaviour.
    /// If you still want to redo `self` use `self.finallize_solution()`.
    pub fn finallize_solution_in_place(&mut self) -> Result<(), ProcessingError>{
        while !self.conversion.is_empty() {
            if !self.solution.remove(&(self.conversion.len() + self.graph.num_reserved() - 1)) {
                return Err(ProcessingError::ConversionError)
            }
            let convers = self.conversion.pop().expect("`self.conversion` is not empty");
            if convers.0.iter().all(|node| self.solution.contains(&node)) {
                self.solution.insert(convers.1.0);
            } else {
                self.solution.insert(convers.1.1);
            }
        }
        Ok(())
    }

    /// Replaces the placeholders from the `LinkNode`-rule in a final solution `solution` with the respective
    /// correct node. 
    ///
    /// Attention: If `solution` is not final, this can lead to
    /// erroneous behaviour.
    pub fn finallize_solution(&self, solution: &FxHashSet<usize>) -> Result<FxHashSet<usize>, ProcessingError>{
        let mut conversions = self.conversion.clone();
        let mut new_sol = solution.clone();
        while !conversions.is_empty() {
            if !new_sol.remove(&(conversions.len() + self.graph.num_reserved() - 1)) {
                return Err(ProcessingError::ConversionError)
            }
            let convers = conversions.pop().expect("`self.conversion` is not empty");
            if convers.0.iter().all(|node| new_sol.contains(&node)) {
                new_sol.insert(convers.1.0);
            } else {
                new_sol.insert(convers.1.1);
            }
        }
        Ok(new_sol)
    }

    /// Redoes the alterations up to the next register in `self.register`. Pops that register, if the
    /// instance was rebuild completely, pushes `0` to the register.
    pub fn rebuild_section(&mut self) {
        let up_to = self.register.pop().expect("`self.register` should never be empty");
        while self.alterations.len() > up_to {
            match self.alterations.pop().expect("`self.alteration` > 0") {
                Alteration::AddNode(node, neigh) => {
                    self.solution.remove(&node);
                    self.graph.reinsert_node(node, &neigh);
                },
                Alteration::DeleteNode(node, neigh) => {
                    self.graph.reinsert_node(node, &neigh);
                },
                Alteration::ContractLink { link, from, into, old_from, new_into} => {
                    self.conversion.pop();
                    let placeholder = self.graph.num_reserved() + self.conversion.len();
                    self.solution.remove(&placeholder);
                    self.graph.delete_neighbors(into, &new_into);
                    self.graph.reinsert_node(from, &old_from);
                    self.graph.reinsert_node(link, &vec![into, from].iter().copied().collect());
                },
                Alteration::ContractTwins { twins, trips, old_from1, old_from2, new_into} => {
                    self.conversion.pop();
                    let placeholder = self.graph.num_reserved() + self.conversion.len();
                    self.solution.remove(&placeholder);
                    self.conversion.pop();
                    let placeholder = self.graph.num_reserved() + self.conversion.len();
                    self.solution.remove(&placeholder);
                    self.graph.delete_neighbors(trips[2], &new_into);
                    self.graph.reinsert_node(trips[0], &old_from1);
                    self.graph.reinsert_node(trips[1], &old_from2);
                    self.graph.reinsert_node(twins[0], &trips.iter().copied().collect());
                    self.graph.reinsert_node(twins[1], &trips.iter().copied().collect());
                },
                Alteration::SubstitudeAlternatives(missing_edges, set_len) => {
                    for _ in 0..set_len {
                        self.conversion.pop();
                        let placeholder = self.graph.num_reserved() + self.conversion.len();
                        self.solution.remove(&placeholder);
                    }
                    self.graph.delete_edges(&missing_edges);
                },
            }
        }
        if self.register.is_empty() {
            self.register.push(0);
        }
    }

    /// Puts a register in `self.register` to denote the current state of the graph.
    pub fn put_register(&mut self) {
        self.register.push(self.alterations.len());
    }

    /// Checks if a solution is valid.
    pub fn validate_solution(&self, sol: &FxHashSet<usize>) -> bool {
        let mut clone = self.clone();
        for node in sol {
            if *node >= clone.graph.num_reserved() {
                return false
            }
            clone.graph.delete_node(*node);
        }
        if clone.graph.edges().count() != 0 {
            return false
        }
        true
    }

}

impl VCInstance {
    
    /// Writes a solution to a `Write` type.
    pub fn write_solution<W: Write>(n: usize, solution: &FxHashSet<usize>, mut out: W) -> Result<(), io::Error> { 
        writeln!(out, "s vc {} {}", n, solution.len())?;
        for elem in solution {
            writeln!(out, "{}",elem + 1)?;
        }
        Ok(())
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use crate::graph::DyUGraph;

    #[test]
    fn alter_rebuild_test() {
        let gr = Cursor::new("p td 7 11\n1 2\n2 3\n2 5\n2 6\n3 4\n3 5\n3 6\n4 5\n4 6\n\
                              5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        let check_ins = ins.clone();
        ins.add_to_solution(1);
        ins.delete_node(0);
        assert!(ins.contract_link_node(6, 5, 4).is_ok());
        assert_eq!(ins.graph.num_nodes(), 3);
        assert_eq!(ins.graph.edges().count(), 3);
        ins.rebuild_section(); 
        assert_eq!(ins, check_ins);
    }

    #[test]
    fn bounds_test() {
        let gr = Cursor::new("p td 7 11\n1 2\n2 3\n2 5\n2 6\n3 4\n3 5\n3 6\n4 5\n4 6\n\
                              5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        ins.update_lower_bound(3);
        ins.update_current_best(&vec![6,1,5,4,3].into_iter().collect());
        ins.add_to_solution(1);
        ins.delete_node(0);
        assert!(ins.contract_link_node(6, 5, 4).is_ok());
        assert_eq!(ins.effective_lower_bound(), Some(1));
        assert_eq!(ins.effective_upper_bound(), Some(3));
        ins.update_lower_bound(2);
        ins.update_current_best(&vec![6,1,5,4,3,0].into_iter().collect());
        assert_eq!(ins.effective_lower_bound(), Some(1));
        assert_eq!(ins.effective_upper_bound(), Some(3));
        ins.update_lower_bound(4);
        ins.update_current_best(&vec![1,5,4,3].into_iter().collect());
        assert_eq!(ins.effective_lower_bound(), Some(2));
        assert_eq!(ins.effective_upper_bound(), Some(2));
    }

}

