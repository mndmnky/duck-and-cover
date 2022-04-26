//! Module for the `flow-rule`.
//! Creates a flow network of the bipartite representation `B(V_b, E_b)` of a graph `G(V,E)`. 
//! Where `B(V_b, E_b)` is defined as followes: for each node `v` in `V`, there are two
//! representatives `v'` and `v''` in `V_b`. For each edge `(v,w)` in `E` we have two directed edges
//! `(v',w'')` and `(w',v'')` in `E_b`.
//! 
//! In the flow network we compute an optimal flow with the help of dinic's algorithm. This flow is
//! used to find an optimal matching and an optimal vertex cover for B.
//! 
//! Let nodes `v'` and `v''` in `B` representing a node `v` in `G`. 
//! If both `v'` and `v''` are in the vertex cover of `B`, `v` is in the vertex cover of `G`.
//! If neither `v'` nor `v''` are in the vertex cover of `B`, `v` can be removed from `G`.

use crate::graph::DyUGraph;
use std::convert::From;
use std::collections::{HashMap, HashSet, VecDeque};
use std::cmp::min;
use fxhash::{FxHashMap, FxHashSet};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BipartFlowNet {
    /// Number of nodes in the flow network
    n: usize,
    /// Number of nodes in the origin graph
    n_pr: usize,
    /// Flow matrix, the value in `flow[n*r+c]` gives the amount of flow sent from node `r` to node
    /// `c`
    flow: Vec<i8>,
    /// Adjacency matrix of the origin graph, `capacity[n_pr*r+c] == true` means that there is an
    /// edge between `names[r]` and `names[c]` in the origin graph
    capacity: Vec<bool>,
    /// The ids of nodes in the origin graph. The representatives of a node `names[i]` are `i+1`
    /// and `i+1+n_pr`.
    pub names: Vec<usize>,
    /// Helper for the flow algorithm
    steps: Vec<u8>,
}

impl BipartFlowNet {

    /// Returns the value from the flow matrix in row `row` and column `column`.
    fn get_flow(&self, row: usize, column: usize) -> i8 {
        let id = self.n * row + column;
        self.flow[id]
    }

    /// Adds `value` flow to the flow matrix in row `row` and column `column`.
    fn add_flow(&mut self, row: usize, column: usize, value: i8) {
        let id = self.n * row + column;
        self.flow[id] += value;
    }

    /// Subtracts `value` flow from the flow matrix in row `row` and column `column`.
    fn sub_flow(&mut self, row: usize, column: usize, value: i8) {
        let id = self.n * row + column;
        self.flow[id] -= value;
    }

    /// Returns the capacity from node `row` to node `column` in the flow network.
    fn get_cap(&self, row: usize, column: usize) -> i8 {
        return if row >= column {
            0
        }
        else if row == 0 {
            if column <= self.n_pr{
                1
            } else {
                0
            }
        } else if column == self.n-1 {
            if row > self.n_pr {
                1
            } else {
                0
            }
        } else {
            if row <= self.n_pr {
                if column > self.n_pr {
                    let r = row - 1;
                    let c = column - (self.n_pr + 1); 
                    if self.capacity[r*self.n_pr + c] {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            }
        }
    }

    /// Checks if an augmenting path from source (0) to target (`n`-1) exists. Records the distance
    /// of each reachable node from the source.
    fn bfs(&mut self) -> bool {
        // s is 0
        let mut queue: VecDeque<_> = vec![0].into();
        self.steps = vec![0;self.n];
        self.steps[0] = 1;
        while !queue.is_empty() {
            let k = queue.pop_front().expect("`queue` not empty");
            for i in 0..self.n {
                if i == k {
                    continue
                }
                if (self.get_flow(k,i) < self.get_cap(k,i)) && (self.steps[i] == 0) {
                    self.steps[i] = self.steps[k] + 1;
                    queue.push_back(i);
                }
            }
        }
        return self.steps[self.n-1] > 0
    }

    /// Tries to push as much flow as possible through the network.
    fn dfs(&mut self, k: usize, cp: i8) -> i8 {
        let mut tmp = cp;
        if k == self.n - 1 {
            return cp 
        }
        for i in 0..self.n {
            if (self.steps[i] == self.steps[k] + 1) && (self.get_flow(k, i) < self.get_cap(k, i)) {
                let f = self.dfs(i, min(tmp, self.get_cap(k,i) - self.get_flow(k, i)));
                self.add_flow(k, i, f);
                self.sub_flow(i, k, f);
                tmp -= f;
            }
        }
        cp - tmp
    }

    /// Finds the maximum flow by application of the dinic's algorithm. 
    fn matching_by_max_flow(&mut self) -> HashSet<(usize, usize)> {
        while self.bfs() {
            self.dfs(0, i8::MAX);
        }
        let mut matching = HashSet::new();
        for a in 0..self.n_pr {
            for b in 0..self.n_pr {
                if self.get_flow(a+1,b+self.n_pr+1) > 0 {
                    matching.insert((a+1,b+self.n_pr+1));
                }
            }
        }
        return matching
    }

    /// Given a set `src` and a matching `matching`, returns all nodes from the left side of the
    /// bipartite graph that are reachable from `src` over alternating paths regarding to
    /// `matching`. `src` needs to be an unmatched node set of the left side.
    fn reachable_by_alternating(
        &mut self, src: &FxHashSet<usize>, 
        matching: &HashSet<(usize, usize)>
    ) -> FxHashSet<usize> {
        // Only true alternating paths!
        let mut reachable = src.clone();
        let mut new_len = reachable.len();
        let mut last_len = 0;
        let match_trgs: FxHashSet<usize> = matching.iter().map(|(_, t)| t).copied().collect();
        // While something changed:
        while last_len < new_len {
            last_len = new_len;
            let old_reachable = reachable.clone();
            reachable.extend(match_trgs.iter().filter_map(|t| {
                let org_id = t-(self.n_pr + 1);
                let mut matched_neighbor = None;
                let neighbors = self.capacity[org_id*self.n_pr..(org_id+1)*self.n_pr]
                    .iter()
                    .enumerate()
                    .filter_map(|(id, is_edge)| {
                        if *is_edge {
                            if matching.contains(&(id+1,*t)) {
                                matched_neighbor = Some(id + 1);
                                None
                            } else {
                                Some(id + 1)
                            }
                        } else {
                            None
                        }
                    }).collect::<FxHashSet<_>>();
                if neighbors.intersection(&old_reachable).count() > 0 {
                    return Some(matched_neighbor.expect("all nodes in `match_trgs` are matched"))
                }
                None
            }));
            new_len = reachable.len();
        }
        reachable
    }

    /// Computes a vertex cover of the bipartite graph. 
    /// Returns a set of ids such that for each id in it, both representatives of `self.names[id]`
    /// are in the vertex cover and a set of ids such that for each id in it, no representativ of
    /// `self.names[id]` is in the cover.
    pub fn compute_full_and_empty_nodes(&mut self) 
        -> Option<(FxHashSet<usize>, FxHashSet<usize>)> {
        let matching = self.matching_by_max_flow();
        if matching.len() == self.n_pr {
            return None
        }
        let match_srcs: FxHashSet<usize> = matching.iter().map(|(s, _)| s).copied().collect();
        let s_set: FxHashSet<usize> = (1..(self.n_pr + 1)).filter(|i| !match_srcs.contains(i)).collect();
        // matched trgs are the only nodes that can be inbetween an alternating path.
        let r_set = self.reachable_by_alternating(&s_set, &matching);
        // get `t_set` all neighbors of `r_set` in `matching`
        let cover_in_trg: FxHashSet<usize> = matching.into_iter()
            .filter_map(|(s,t)| {
            if r_set.contains(&s) {
                Some(t - (self.n_pr + 1))
            } else {
                None
            }
        }).collect();
        let cover_in_src: FxHashSet<usize> = (0..self.n_pr)
            .filter(|s| !(s_set.contains(&(s + 1)) || r_set.contains(&(s + 1))))
            .collect();
        let outs: FxHashSet<usize> = (0..(self.n_pr))
            .filter(|node| !(cover_in_src.contains(&node) 
                             || 
                             cover_in_trg.contains(&node)))
            .collect();
        let ins: FxHashSet<usize> = cover_in_src.intersection(&cover_in_trg)
            .copied()
            .collect();
        if ins.is_empty() && outs.is_empty() {
            return None
        }
        Some((ins, outs))
    }

}

impl From<DyUGraph> for BipartFlowNet {

    fn from(graph: DyUGraph) -> Self {
        let names = graph.nodes().collect::<Vec<usize>>();
        let old_new: FxHashMap<usize, usize> = HashMap::from(names.iter().enumerate().map(|(new,old)| (*old,new)).collect());
        let n_pr = graph.num_nodes();
        let n = n_pr*2 + 2;
        let flow = vec![0;n*n];
        // Build capacity matrix. Example for 3 nodes: 
        //  f t f 
        //  t f t 
        //  t t f 
        let mut capacity = vec![];
        for node in names.iter() {
            let mut col = vec![false;n_pr];
            for neigh in graph.neighbors(*node).as_ref().expect("`node` exists") {
                col[*old_new.get(&neigh).expect("If `neigh` is a node it is a key in `old_new`")] = true;
            }
            capacity.extend(col);
        }
        BipartFlowNet {
            n, 
            n_pr,
            flow, 
            capacity, 
            names, 
            steps: vec![0;n],
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use crate::graph::DyUGraph;

    #[test]
    fn converstion_test() {
        let gr = Cursor::new("p td 6 5\n1 4\n1 5\n2 4\n2 6\n3 6\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let bipf: BipartFlowNet = graph.into();
        assert_eq!(bipf.get_cap(1,10), 1);
        assert_eq!(bipf.get_cap(4,7), 1);
        assert_eq!(bipf.get_cap(0,6), 1);
        assert_eq!(bipf.get_cap(0,7), 0);
        assert_eq!(bipf.get_cap(6,13), 0);
        assert_eq!(bipf.get_cap(7,13), 1);
    }

    #[test]
    fn matching_test() {
        let gr = Cursor::new("p td 6 5\n1 4\n1 5\n2 4\n2 6\n3 6\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let mut bipf: BipartFlowNet = graph.into();
        let matching = bipf.matching_by_max_flow();        
        assert_eq!((1..7).collect::<FxHashSet<usize>>(), 
                   matching.iter().map(|(s,_)| s).copied().collect());
        assert_eq!((7..13).collect::<FxHashSet<usize>>(), 
                   matching.iter().map(|(_,t)| t).copied().collect());
    }

    #[test]
    fn some_test() {
        let gr = Cursor::new("p td 6 12\n1 2\n1 3\n1 5\n1 6\n2 3\n2 4\n2 5\n\
                              3 4\n3 6\n4 5\n4 6\n5 6\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let mut bipf: BipartFlowNet = graph.into();
        let in_outs = bipf.compute_full_and_empty_nodes();
        assert_eq!(in_outs, None); 
    }

    //#[test]
    //fn some_other_test() {
    //    let gr = Cursor::new("p td 11 20\n1 2\n1 3\n1 4\n2 3\n2 5\n3 4\n3 5\n\
    //                          4 5\n4 6\n5 6\n6 7\n6 8\n7 8\n7 9\n7 10\n8 9\n\
    //                          8 11\n9 10\n9 11\n10 11\n");
    //    let graph = DyUGraph::read_gr(gr);
    //    assert!(graph.is_ok());
    //    let graph = graph.unwrap();
    //    let mut bipf: BipartFlowNet = graph.into();
    //    let in_outs = bipf.compute_full_and_empty_nodes();
    //    assert_eq!(in_outs, None); // Needs double check.
    //}

    #[test]
    fn star_test() {
        let gr = Cursor::new("p td 5 4\n1 2\n1 3\n1 4\n1 5\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let mut bipf: BipartFlowNet = graph.into();
        let in_outs = bipf.compute_full_and_empty_nodes();
        assert!(in_outs.is_some());
        let (ins, outs) = in_outs.unwrap();
        assert_eq!(ins, vec![0].into_iter().collect());
        assert_eq!(outs, vec![1,2,3,4].into_iter().collect());
    }

    #[test]
    fn path_test() {
        let gr = Cursor::new("p td 5 4\n1 2\n2 3\n3 4\n4 5\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let mut bipf: BipartFlowNet = graph.into();
        let in_outs = bipf.compute_full_and_empty_nodes();
        assert!(in_outs.is_some());
        let (ins, outs) = in_outs.unwrap();
        assert_eq!(ins, vec![1,3].into_iter().collect());
        assert_eq!(outs, vec![0,2,4].into_iter().collect());
    }

    #[test]
    fn star_path_test() {
        let gr = Cursor::new("p td 5 4\n1 2\n1 3\n1 5\n5 4\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        let mut bipf: BipartFlowNet = graph.into();
        let in_outs = bipf.compute_full_and_empty_nodes();
        assert!(in_outs.is_some());
        let (ins, outs) = in_outs.unwrap();
        assert_eq!(ins, vec![0].into_iter().collect());
        assert_eq!(outs, vec![1,2].into_iter().collect());
    }

}

