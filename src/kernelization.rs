use crate::vc_instance::VCInstance;
use fxhash::{FxHashSet, FxHashMap};
use std::collections::{HashSet, HashMap};
use crate::bipart_flow::BipartFlowNet;

pub const FAST_RULES: &[Rule] = &[Rule::SimpleRules, Rule::LinkNode];
pub const ALL_RULES_BUT_LOCAL_FAST_FIRST: &[Rule] = &[Rule::SimpleRules, Rule::LinkNode, Rule::Clique, Rule::Twins, Rule::Dominion, Rule::Crown1, Rule::Flow];

pub enum Rule {
    SimpleRules,
    LinkNode,
    Clique,
    Twins,
    Dominion,
    Flow,
    LocalK1,
    LocalK10,
    LocalK100,
    Crown1,
    Crown10,
    Crown100,
}

impl VCInstance {

    /// Applies some simple reduction rules. The rules are applied for each node and in no specific
    /// order until no more rules can be applied.
    /// Returns true if at least one reduction has been applied.
    ///
    /// The rules are: 
    /// Rule 1: Remove isolated nodes. 
    /// Rule 2: Remove nodes with degree 1 and adds their neighbor to the solution.
    pub fn simple_rules(&mut self) -> bool {
        let mut changed = true;
        let mut rounds = 0;
        while changed {
            rounds +=1;
            changed = false;
            let nodes: Vec<_> = self.graph.nodes().collect();
            for node in nodes {
                // `node` could have been removed by now.
                if let Some(neighbors) = self.graph.neighbors(node).clone() {
                    if neighbors.len() == 0 {
                        self.delete_node(node);
                    } else if neighbors.len() == 1 {
                        self.add_to_solution(*neighbors.iter().next().expect("`node`s degree is 1"));
                        self.delete_node(node);
                        changed = true;
                    }
                }
            }
        }
        rounds > 1 
    }

    /// Contracts node with degree 2.
    ///
    /// Should not reach the panic statement.
    pub fn contract_link_nodes(&mut self) -> bool {
        let mut changed = false;
        'outer: loop {
            let nodes = self.graph.nodes().collect::<Vec<usize>>();
            for node in nodes {
                let neighbors = self.graph.neighbors(node).as_ref().expect("`node` exists");
                if neighbors.len() == 2 {
                    let mut neighs = neighbors.iter().clone();
                    let n1 = *neighs.next().expect("`node` has degree 2");
                    let n2 = *neighs.next().expect("`node` has degree 2");
                    if self.graph.edge_exists((n1, n2)) {
                        self.add_to_solution(n1);
                        self.add_to_solution(n2);
                        self.delete_node(node);
                        changed = true;
                        continue 'outer
                    } else {
                        self.contract_link_node(node, n1, n2).expect("`node` is a link node but could not be contracted");
                        changed = true;
                        continue 'outer
                    }
                }
            }
            break 'outer
        }
        changed
    }

    /// Applies the clique rule (see documentation TODO) exhaustively by checking for each node
    /// `v` in `self.graph` if `v`s neighborhood is a clique. If this is given adds all neighbors
    /// of `v` to the solution and removes the neighborhood as well as `v`.
    /// Returns `true` if anything happened.
    pub fn exhaustive_clique_rule(&mut self) -> bool {
        // Go through all the nodes 
        let nodes = self.graph.nodes().collect::<Vec<_>>();
        for node in nodes {
            let neighborhood = self.graph.neighbors(node).as_ref().expect("`node` exists").clone();
            // Check if strong neighborhood is a cluster 
            if self.graph.is_clique(&neighborhood) {
                self.add_all_to_solution(&neighborhood).expect("`self.graph` hold all of these nodes.");
                self.delete_node(node);
                return true
            }
        }
        false 
    }

    /// Traverses over all nodes with a degree of 3 and stores the neighbors `neighs` of each such 
    /// nodes either in `connects` if any pair in `neighs` is connected by an edge, or in `un_connects` 
    /// otherwise. If for any set of `neighs` there already exists an entry in `connects`, adds all nodes in
    /// `neighs` to the solution and returns. If `neighs` are already in `un_connects`, stores
    /// `neighs` also in `connects`.
    pub fn twin_rule(&mut self) -> bool {
        let mut connects = HashSet::new();
        let mut un_connects = HashSet::new();
        let nodes = self.graph.nodes().collect::<Vec<usize>>();
        for node in nodes {
            if self.graph.degree(node).expect("`node` exists") == 3 {
                let mut neighbors: Vec<usize> = self.graph.neighbors(node).as_ref().expect("`node` exists").iter().copied().collect();
                neighbors.sort_unstable();
                let neighs: [usize; 3] = [neighbors[0], neighbors[1], neighbors[2]];
                if connects.contains(&neighs) {
                    self.add_all_to_solution(&neighs.iter().copied().collect::<FxHashSet<usize>>()).expect("`neighs` are all in `self.graph`");
                    return true
                } else if un_connects.contains(&neighs) {
                    connects.insert(neighs);
                } else {
                    if self.graph.has_edge(&neighs.iter().copied().collect()) {
                        connects.insert(neighs);
                    } else {
                        un_connects.insert(neighs);
                    }
                }
            }
        }
        false 
    }

    /// Checks the `top_x` nodes with the highest degree. If their degree is higher then the
    /// remaining upper bound minus the lower bound of the graph without the respective node and
    /// its neighbors, adds that node to the solution and aborts.
    /// If only x < `top_x` nodes remain in `self.graph`, checks all of them instead.
    ///
    /// Returns `true` if at least one node was removed.
    pub fn local_k_node(&mut self, top_x: usize) -> bool {
        if let Some(upper_bound) = self.effective_upper_bound() {
            let nn = self.graph.max_x_degree_node_neighbors(top_x); 
            for (node, neighbors) in nn {
                let mut gc = self.graph.clone();
                gc.delete_nodes(&neighbors);
                let ins = VCInstance::new(gc);    
                let lower = ins.lower_bound_heuristic(ALL_RULES_BUT_LOCAL_FAST_FIRST);
                if neighbors.len() > upper_bound - lower {
                    self.add_to_solution(node);
                    return true
                }
            }
            return false
        }
        false
    }

    /// Applies the `crown` rule on a random matching. 
    /// Returns `true` if at least one node was added to the solution.
    pub fn crown_rule(&mut self) -> bool {
        let outsiders = self.graph.unmatched_of_random_matching();
        let (mut spikes, matching) = self.graph.random_matching_between_set_and_neighbors(&outsiders);
        let mut crown = FxHashSet::default();
        let mut spike_size = 0;
        while spike_size < spikes.len() {
            crown = self.graph.open_neighborhood_of_set(&spikes);
            spike_size = spikes.len();
            spikes.extend(matching.iter().filter_map(|(a, b)| {
                if crown.contains(a) {
                    Some(b)
                } else if crown.contains(b) {
                    Some(a)
                } else {
                    None
                }
            }));
        }
        if spikes.len() > 0 {
            self.add_all_to_solution(&crown).expect("`crown` exists");
            self.delete_all_nodes(&spikes).expect("`spikes` exist");
            return true
        }
        false
    }

    /// Looks for an unconfined vertex and adds it to the solution if one was find.
    /// Returns `true` if a vertex was added to the solution and `false` otherwise.
    pub fn dominion_rule(&mut self) -> bool {
        let nodes = self.graph.nodes().collect::<Vec<usize>>();
        for node in nodes {
            let mut set: FxHashSet<usize> = vec![node].into_iter().collect();
            // Get closed neighbors of `set`
            let mut set_closed_n = self.graph.neighbors(node).as_ref().expect("`node` exists").clone();
            set_closed_n.insert(node);
            loop {
                let set_closed_n_clone = set_closed_n.clone();
                // Get node `opt` in neighborhood of `set`, such that `opt` has only one neighbor
                // in `set` and the open neighborhood of `opt` minus the closed neighborhood of
                // `set` is minimized.
                let opt = set_closed_n_clone.iter().filter_map(|neigh| {
                    if set.contains(neigh) {
                        return None
                    }
                    let nn = self.graph.neighbors(*neigh).as_ref().expect("`neigh` exists");
                    if nn.intersection(&set).count() != 1 {
                        return None
                    }
                    Some(nn.difference(&set_closed_n).copied().collect::<FxHashSet<usize>>())
                }).min_by_key(|diff| diff.len());

                if let Some(diff) = opt {
                    if diff.is_empty() {
                        self.add_to_solution(node);
                        return true
                    } else if diff.len() == 1 {
                        let s_prime = diff.into_iter().next().expect("`diff.len()` == 1");
                        set.insert(s_prime);
                        set_closed_n.extend(self.graph.neighbors(s_prime).as_ref().expect("`s_prime` exists"));
                        set_closed_n.insert(s_prime);
                        continue
                    }
                }
                // Diamond addition to the `dominion` rule:
                // If `opt` does not exist, or has more than one neighbor outside of the closed
                // neighborhood of `set`, try the diamond rule with `set`:
                // Find all nodes in the neighborhood of `set` that have two neighbors in `set` and
                // no neighbors outside the closed neighborhood of `set`
                let mut evtls: Vec<(usize, [usize;2])> = set_closed_n_clone.iter().filter_map(|neigh| {
                    if set.contains(neigh) {
                        return None
                    }
                    let nn = self.graph.neighbors(*neigh).as_ref().expect("`neigh` exists");
                    if nn.difference(&set_closed_n).count() != 0 {
                        return None
                    }
                    let mut inter: Vec<usize> = nn.intersection(&set).copied().collect();
                    if inter.len() == 2 {
                        inter.sort_unstable();
                        return Some((*neigh, inter.try_into().expect("length is 2")))
                    }
                    None 
                }).collect();
                // Find two elements in `evtls` that are nonadjacent and share the same neighbors.
                while !evtls.is_empty() {
                    let (ncandi, nneighs) = evtls.pop().expect("is not empty");
                    for (ocandi, neighs) in &evtls {
                        if self.graph.edge_exists((*ocandi, ncandi)) {
                            continue
                        }
                        if neighs == &nneighs {
                            self.add_to_solution(node);
                            return true
                        }
                    }
                }
                break
            }
        }
        false
    }

    /// Applies the `flow-rule`, returns true if at least one node was removed.
    pub fn flow_rule(&mut self) -> bool {
        let mut flow_net: BipartFlowNet = self.graph.clone().into();
        if let Some((ins, outs)) = flow_net.compute_full_and_empty_nodes() {
            let real_ins = ins.iter().map(|id| flow_net.names[*id]).collect(); 
            let real_outs = outs.iter().map(|id| flow_net.names[*id]).collect(); 
            self.add_all_to_solution(&real_ins).expect("All nodes in `ins` are in `self.graph`");
            self.delete_all_nodes(&real_outs).expect("All nodes in `outs` are in `self.graph`");
            return true
        }
        false
    }

    /// Exhaustivly applies the rules given in `priority_list` in the given priority order. If at
    /// any point (but after the first rule) a rule altered the graph, the priority list is
    /// traversed from the start.
    ///
    /// The first rule hast to be `Rule::SimpleRules` to be fully functionable. 
    pub fn exhaustive_rules(&mut self, priority_list: &[Rule]) {
        'outer: loop {
            for rule in priority_list {
                match rule {
                    Rule::SimpleRules => {
                        self.simple_rules();
                    },
                    Rule::LinkNode => {
                        if self.contract_link_nodes() {
                            continue 'outer
                        }
                    },
                    Rule::Clique => {
                        if self.exhaustive_clique_rule() {
                            continue 'outer
                        }
                    },
                    Rule::Twins => {
                        if self.twin_rule() {
                            continue 'outer
                        }
                    },
                    Rule::Dominion => {
                        if self.dominion_rule() {
                            continue 'outer
                        }
                    },
                    Rule::Flow => {
                        if self.flow_rule() {
                            continue 'outer
                        }
                    },
                    Rule::LocalK1 => {
                        if self.local_k_node(1) {
                            continue 'outer
                        }
                    },
                    Rule::LocalK10 => {
                        if self.local_k_node(10) {
                            continue 'outer
                        }
                    },
                    Rule::LocalK100 => {
                        if self.local_k_node(100) {
                            continue 'outer
                        }
                    },
                    Rule::Crown1 => {
                        if self.crown_rule() {
                            continue 'outer
                        }
                    },
                    Rule::Crown10 => {
                        let mut i: i8 = 0;
                        while i < 10 {
                            if self.crown_rule() {
                                continue 'outer
                            }
                            i += 1;
                        }
                    },
                    Rule::Crown100 => {
                        let mut i: i8 = 0;
                        while i < 100 {
                            if self.crown_rule() {
                                continue 'outer
                            }
                            i += 1;
                        }
                    },
                }
            }
            break
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use crate::graph::DyUGraph;
    use crate::vc_instance::VCInstance;

    #[test]
    fn simple_rules_test() {
        let gr = Cursor::new("p td 16 12\n5 13\n13 9\n6 14\n14 10\n7 15\n15 11\n8 16\n16 12\n9 10\n10 11\n11 12\n12 9\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.simple_rules());
        assert_eq!(ins.graph.num_nodes(), 4);
        assert_eq!(ins.graph.edges().count(), 4);
        assert!(ins.contract_link_nodes());
        assert_eq!(ins.graph.num_nodes(), 2);
        assert_eq!(ins.graph.edges().count(), 1);
        assert!(ins.simple_rules());
        assert_eq!(ins.graph.num_nodes(), 0);
    }

    #[test]
    fn clique_rule_test() {
        let gr = Cursor::new("p td 7 12\n1 2\n1 3\n1 7\n2 3\n2 4\n3 6\n4 5\n4 6\n4 7\n5 6\n5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.exhaustive_clique_rule());
        assert_eq!(ins.graph.num_nodes(), 3);
        assert_eq!(ins.graph.edges().count(), 3);
        assert!(ins.exhaustive_clique_rule());
        assert_eq!(ins.graph.num_nodes(), 0);
    }

    #[test]
    fn link_rule_test() {
        let gr = Cursor::new("p td 10 14\n1 2\n1 3\n2 4\n2 5\n3 4\n3 5\n\
                             4 6\n4 7\n5 6\n5 7\n6 8\n6 9\n7 9\n7 10\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.contract_link_nodes());
        assert!(ins.simple_rules());
        assert!(ins.finallize_solution_in_place().is_ok());
        assert_eq!(ins.solution.len(), 4);
    }

    #[test]
    fn twin_rule_test() {
        let gr = Cursor::new("p td 16 22\n1 2\n1 3\n1 4\n5 2\n5 3\n5 4\n\
                             6 2\n6 3\n6 4\n7 8\n7 9\n7 10\n8 9\n11 8\n\
                             11 9\n11 10\n12 13\n12 14\n12 15\n16 13\n\
                             16 14\n16 15\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.twin_rule());
        assert!(ins.twin_rule());
        assert!(!ins.twin_rule());
        assert_eq!(ins.solution.len(), 6);
    }

    #[test]
    fn dominion_rule_test() {
        let gr = Cursor::new("p td 14 22\n1 5\n1 6\n1 7\n2 3\n2 4\n2 7\n\
                              3 5\n3 8\n4 5\n4 7\n5 6\n5 14\n6 7\n6 14\n\
                              7 11\n8 11\n8 12\n8 13\n11 12\n11 13\n12 14\n\
                              13 14\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.dominion_rule());
        assert!(ins.dominion_rule());
        assert!(ins.dominion_rule());
        assert!(ins.dominion_rule());
        assert!(ins.dominion_rule());
    }

    #[test]
    fn diamond_test() {
        let gr = Cursor::new("p td 14 32\n1 2\n1 4\n1 8\n1 10\n1 13\n1 14\n\
                              2 3\n2 5\n2 9\n3 4\n3 6\n3 10\n4 5\n4 7\n5 6\n5 8\n\
                              6 7\n6 9\n7 8\n7 10\n\
                              8 9\n6 11\n6 12\n6 14\n9 10\n9 13\n10 11\n10 12\n\
                              11 12\n11 13\n12 14\n13 14\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.dominion_rule());
        assert_eq!(ins.solution, vec![11].into_iter().collect());
    }

    #[test]
    fn local_k_node_test() {
        let gr = Cursor::new("p td 13 27\n1 2\n1 3\n1 4\n1 5\n1 6\n1 7\n\
                              2 3\n2 4\n2 5\n2 6\n2 7\n3 4\n3 5\n3 6\n\
                              3 7\n4 5\n4 6\n4 7\n5 6\n5 7\n6 7\n\
                              8 13\n9 13\n10 13\n11 12\n11 13\n12 13\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        assert!(ins.compute_and_set_upper_lower(&[Rule::SimpleRules]).is_ok());
        assert!(!ins.local_k_node(7));
        assert!(ins.local_k_node(8));
        assert_eq!(ins.solution, vec![12].into_iter().collect());
    }

    #[test]
    fn crown_rule_test() {
        let gr = Cursor::new("p td 11 22\n1 2\n1 3\n1 4\n1 5\n1 6\n2 3\n\
                              2 4\n3 5\n3 6\n4 5\n4 7\n4 8\n4 9\n5 6\n\
                              5 8\n5 9\n5 10\n5 11\n6 7\n6 9\n6 10\n\
                              6 11\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let mut ins = VCInstance::new(graph.unwrap());
        let mut did = false;
        let mut i = 0;
        while !did && i<100 {
            did = ins.crown_rule();
            i += 1;
        }
        let pos_sol_len: FxHashSet<usize> = vec![0,3,5].into_iter().collect();
        assert!(pos_sol_len.contains(&ins.solution.len()));
    }

}
