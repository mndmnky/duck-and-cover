use crate::vc_instance::VCInstance;

pub const FAST_RULES: &[Rule] = &[Rule::SimpleRules, Rule::LinkNode];
pub const ALL_RULES_FAST_FIRST: &[Rule] = &[Rule::SimpleRules, Rule::LinkNode, Rule::Clique];

pub enum Rule {
    SimpleRules,
    LinkNode,
    Clique,
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
                }
            }
            break
        }
    }

}

#[cfg(test)]
mod tests {
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

}
