//! Implementation of a simple, undirected graph data structure with basic static and dynamic
//! functions. 

use fxhash::FxHashSet;
use std::io::BufRead;
use crate::cust_error::ImportError;
use std::cmp::min;
use rand::{thread_rng, Rng};
use std::collections::HashSet;

/// A simple undirected graph datastructure that supports dynamic behaviour.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct DyUGraph {
    adj_list: Vec<Option<FxHashSet<usize>>>,
}

// Static functions
impl DyUGraph {

    /// Returns an `Iterator` over all nodes that have not yet been deleted.
    pub fn nodes(&self) -> impl Iterator<Item=usize> + '_ {
        self.adj_list
            .iter()
            .enumerate()
            .filter_map(|(i,adj)| {
                if adj.is_some() {
                    Some(i)
                } else {
                    None
                }
            })
    }

    /// Returns the number of nodes of `self`.
    pub fn num_nodes(&self) -> usize {
        self.nodes().count()
    }

    /// Returns the amount of reserved nodes of `self`. Deleted or not.
    pub fn num_reserved(&self) -> usize {
        self.adj_list.len()
    }

    /// Returns the neighborhood of `node`, or `None` if `node` was deleted.
    pub fn neighbors(&self, node: usize) -> &Option<FxHashSet<usize>> {
        &self.adj_list[node]
    }

    /// Returns the intersection between `set` and the neighborhood of `node`, or `None` if node
    /// was deleted.
    pub fn neighbors_in(&self, node: usize, set: &FxHashSet<usize>) -> Option<FxHashSet<usize>> {
        let neighbors = self.adj_list[node].clone();
        neighbors.map(|neighs| set.intersection(&neighs).copied().collect())
    }

    /// Returns the open neighborhood of `set`.
    pub fn open_neighborhood_of_set(&self, set: &FxHashSet<usize>) -> FxHashSet<usize> {
        set.iter()
            .filter(|node| self.adj_list[**node].is_some())
            .flat_map(|node| {
                let neighs = self.neighbors(*node).as_ref().expect("`node` exists").clone();
                neighs.difference(set).copied().collect::<Vec<_>>()
        }).collect()
    }

    /// Returns the degree of `node`, or `None` if `node` was deleted.
    pub fn degree(&self, node: usize) -> Option<usize> {
        self.adj_list[node].clone().map(|neighbors| neighbors.len())
    }

    /// Returns the node with the highest degree.
    pub fn max_degree_node(&self) -> Option<usize> {
        self.nodes().max_by_key(|node| self.degree(*node).expect("`node` exists")) }

    /// Returns the `x` nodes and their neighbors with the highest degree. If only `y` < `x` nodes remain in `self`
    /// returns the top `y` nodes (and neighbors) instead.
    pub fn max_x_degree_node_neighbors(&self, x: usize) -> Vec<(usize, FxHashSet<usize>)> {
        let mut nn: Vec<(usize, FxHashSet<usize>)> = self
            .nodes()
            .map(|node| (node, self.neighbors(node).as_ref().expect("`node` exists").clone()))
            .collect();
        nn.sort_unstable_by_key(|(_, neighbors)| -(neighbors.len() as isize));
        if nn.len() < x {
            return nn
        } else {
            return nn[0..x].into()
        }
    }

    /// Returns the node with the highest degree and its neighbors or `None` if no node exists.
    pub fn max_degree_node_neighbors(&self) -> Option<(usize, FxHashSet<usize>)> {
        if let Some((node, neigh)) = self.adj_list.iter()
            .enumerate()
            .filter(|(_,neighs)| neighs.is_some())
            .max_by_key(|(_,evt_neigh)| evt_neigh.as_ref().expect("is some").len()) {
                return Some((node, neigh.as_ref().expect("is some").clone()))
            }
        None
    }

    /// Returns an iterator over all edges.
    pub fn edges(&self) -> impl Iterator<Item=(usize, usize)> + '_ {
        self.adj_list
            .iter()
            .enumerate()
            .filter(|(_,adj)| adj.is_some())
            .flat_map(|(i,adj)| {
                adj.as_ref().expect("`adj` is some")
                    .iter()
                    .filter_map(|neigh| {
                    if i < *neigh {
                        Some((i, *neigh))
                    } else {
                        None
                    }
                }).collect::<Vec<(usize, usize)>>()
            })
    }

    /// Returns the edge with the highest degree sum of both incident nodes.
    pub fn max_edge_by_degree(&self) -> Option<(usize, usize)> {
        self.edges().max_by_key(|(src, trg)| self.degree(*src).expect("`src` exists") + self.degree(*trg).expect("`trg` exists"))
    }

    /// Returns the edge `(src, trg)` where `|self.degree(src) - self.degree(trg)|` is maximal. 
    pub fn max_imba_edge_by_degree(&self) -> Option<(usize, usize)> {
        self.edges().max_by_key(|(src, trg)| (self.degree(*src).expect("`src` exists") as isize - self.degree(*trg).expect("`trg` exists") as isize).abs())
    }

    /// Returns the edge for which either of the connected nodes has a minimal degree. 
    pub fn min_edge_by_degree(&self) -> Option<(usize, usize)> {
        self.edges().min_by_key(|(src, trg)| min(self.degree(*src).expect("`src` exists"), self.degree(*trg).expect("`trg` exists")))
    }

    /// Checks if `edge` exists. 
    pub fn edge_exists(&self, edge: (usize, usize)) -> bool {
        if let Some(neighs) = &self.adj_list[edge.0] {
            return neighs.contains(&edge.1)
        }
        false 
    }

    /// Checks if an edge exists between `set`.
    pub fn has_edge(&self, set: &FxHashSet<usize>) -> bool {
        let mut mut_set = set.clone();
        while mut_set.len() > 1 {
            let next = *mut_set.iter().next().expect("`mut_set` is not empty");
            mut_set.remove(&next);
            if let Some(neighbors) = self.neighbors(next) {
                if mut_set.intersection(&neighbors).count() > 0 {
                    return true
                }
            }
        }
        false
    }

    /// Checks if `self` is empty (holds no undeleted nodes).
    pub fn is_empty(&self) -> bool {
        self.num_nodes() == 0
    }
    
    /// Greedily looks for a maximal clique: 
    /// Starting with the node with the highest strong degree and then adding node with the biggest
    /// neighborhood intersection.
    pub fn greedy_max_clique(&self) -> FxHashSet<usize> {
        let mut greedy_max_clique = FxHashSet::default();
        if let Some((node, mut neighbors)) = self.max_degree_node_neighbors() {
            greedy_max_clique.insert(node);
            while !neighbors.is_empty() {
                let mut max_intersect = FxHashSet::default();
                let mut max_neighbor = None;
                for neigh in &neighbors {
                    if let Some(shared_neighbors) = self.neighbors_in(*neigh, &neighbors) {
                        if shared_neighbors.len() > max_intersect.len() || max_neighbor.is_none() {
                            max_intersect = shared_neighbors.clone();
                            max_neighbor = Some(*neigh);
                        }
                    }
                }
                if let Some(neigh) = max_neighbor {
                    greedy_max_clique.insert(neigh);
                    neighbors = max_intersect;
                } else {
                    break
                }
            }
        }
        greedy_max_clique
    }

    /// Checks if `node_set` is a clique in `self`.
    pub fn is_clique(&self, node_set: &FxHashSet<usize>) -> bool {
        let mut remaining = node_set.clone();
        while !remaining.is_empty() {
            let node = remaining.iter().next().cloned().expect("`remaining` is not empty");
            remaining.remove(&node);
            if let Some(neighbors) = self.neighbors(node) {
                if !(remaining.difference(&neighbors).count() == 0) {
                    return false
                }
            } else {
                return false
            }
        }
        true
    }

    /// Returns a set of all nodes reachable by `node`, including `node`.
    pub fn reachable(&self, node: usize) -> FxHashSet<usize> {
        let mut reached = FxHashSet::default();
        let mut queue = vec![node];
        while !queue.is_empty() {
            let next = queue.pop().expect("`queue` is not empty");
            if reached.contains(&next) {
                continue
            }
            reached.insert(next);
            queue.extend(self.neighbors(next).as_ref().expect("`next` exists"));
        }
        reached
    }

    /// Checks if `self` is disconnected.
    pub fn disconnected(&self) -> bool {
        if self.num_nodes() == 0 {
            return false
        }
        if self.reachable(self.nodes().next().expect("`self` has nodes")).len() 
            != self.num_nodes() {
            return true
        }
        false
    }

    /// Returns a random neighbor of `node`.
    pub fn random_neighbor(&self, node: usize) -> Option<usize> {
        if let Some(neighs) = self.neighbors(node) {
            let neighs_vec: Vec<&usize> = neighs.iter().collect();
            if neighs_vec.len() != 0 {
                let id = thread_rng().gen_range(0..neighs.len());
                return Some(*neighs_vec[id])
            }
        }
        None
    }

    /// Returns a random neighbor of `node` that is not in `set`.
    pub fn random_neighbor_not_in(&self, node: usize, set: &FxHashSet<usize>) -> Option<usize> {
        if let Some(neighs) = self.neighbors(node) {
            let neighs_vec: Vec<&usize> = neighs.difference(set).collect();
            if neighs_vec.len() != 0 {
                let id = thread_rng().gen_range(0..neighs_vec.len());
                return Some(*neighs_vec[id])
            }
        }
        None
    }

    /// Returns the unmatched nodes of a random maximal matching of `self`.
    pub fn unmatched_of_random_matching(&self) -> FxHashSet<usize> {
        let mut nodes: Vec<usize> = self.nodes().collect();
        let mut matched: FxHashSet<usize> = FxHashSet::default();
        let mut outsiders: FxHashSet<usize> = FxHashSet::default();
        while !nodes.is_empty() {
            let id = thread_rng().gen_range(0..nodes.len());
            let node = nodes.swap_remove(id);
            if matched.contains(&node) {
                continue
            }
            if let Some(neighbor) = self.random_neighbor_not_in(node, &matched) {
                matched.insert(neighbor);
                matched.insert(node);
                // to get the actual matching:
                //matching.insert((node, neighbor));
            } else {
                outsiders.insert(node);
            }
        }
        outsiders
    }

    /// Returns the matching and the unmatched nodes of a random maximal matching of the edges
    /// between `set` and its neighbors.
    pub fn random_matching_between_set_and_neighbors(&self, set: &FxHashSet<usize>) -> (FxHashSet<usize>, HashSet<(usize, usize)>) {
        let mut no_match = set.clone();
        let mut set_vec: Vec<&usize> = set.iter().collect();
        let mut outsiders: FxHashSet<usize> = FxHashSet::default();
        let mut matching: HashSet<(usize, usize)> = HashSet::new();
        while !set_vec.is_empty() {
            let id = thread_rng().gen_range(0..set_vec.len());
            let node = set_vec.swap_remove(id);
            if let Some(neighbor) = self.random_neighbor_not_in(*node, &no_match) {
                no_match.insert(neighbor);
                matching.insert((*node, neighbor));
            } else {
                outsiders.insert(*node);
            }
        }
        (outsiders, matching)
    }

}

// Dynamic functions
impl DyUGraph {

    /// Tries to delete `node`. 
    /// Returns the old neighborhood of `node` or `None` if nothing was deleted.
    pub fn delete_node(&mut self, node: usize) -> Option<FxHashSet<usize>> {
        let opt_neighbors = self.adj_list[node].take();
        if let Some(neighborhood) = opt_neighbors.as_ref() {
            for neighbor in neighborhood.iter() {
                if let Some(ref mut nn) = self.adj_list[*neighbor] {
                    nn.remove(&node);
                }
            }
        }
        opt_neighbors
    }

    /// Removes all nodes in `node_set` from the graph. 
    pub fn delete_nodes(&mut self, node_set: &FxHashSet<usize>) {
        for node in node_set {
            let opt_neighbors = self.adj_list[*node].take();
            if let Some(neighborhood) = opt_neighbors.as_ref() {
                for neighbor in neighborhood.difference(&node_set) {
                    if let Some(ref mut nn) = self.adj_list[*neighbor] {
                        nn.remove(&node);
                    }
                }
            }
        }
    }

    /// Reinserts `node` and a edge to each former neighbor given as `neighbors`.
    pub fn reinsert_node(&mut self, node: usize, neighbors: &FxHashSet<usize>) {
        self.adj_list[node] = Some(neighbors.clone());
        for neigh in neighbors {
            if let Some(ref mut nn) = self.adj_list[*neigh] {
                nn.insert(node);
            }
        }
    }

    /// Merge `from` into `into`. 
    /// Returns the old neighbors of `from` and the new neighbors of `into`, or `None` if either
    /// `from` or `into` was already deleted.
    pub fn merge_nodes(&mut self, from: usize, into: usize) 
        -> Option<(FxHashSet<usize>, FxHashSet<usize>)> {
        if let Some(neighbors) = self.delete_node(from) {
            if let Some(add_neighs) = self.adj_list[into].as_mut() {
                // Find doubles
                let new_neighbors: FxHashSet<usize> = neighbors
                    .difference(&add_neighs)
                    .copied()
                    .collect();
                // add neighbors (both sides)
                add_neighs.extend(&new_neighbors);
                for neigh in &new_neighbors {
                    if let Some(ref mut nn) = self.adj_list[*neigh] {
                        nn.insert(into);
                    }
                }
                return Some((neighbors, new_neighbors));
            } else {
                self.reinsert_node(from, &neighbors);
                return None
            }
        }
        return None
    }

    /// Removes all the edges between `node` and the nodes in `neighbors`.
    pub fn delete_neighbors(&mut self, node: usize, neighbors: &FxHashSet<usize>) {
        for neigh in neighbors {
            if let Some(ref mut nn) = self.adj_list[*neigh] {
                nn.remove(&node);
            }
        }
        if let Some(ref mut nn) = self.adj_list[node] {
            for neigh in neighbors {
                nn.remove(&neigh);
            }
        }
    }

}

impl DyUGraph {

    /// Reads a `.gr` input and creates a `DyUGraph`.
    pub fn read_gr<R: BufRead>(gr: R) -> Result<Self, ImportError> {
        let (lines, _): (Vec<_>, Vec<_>) = gr.lines()
            .partition(|l| {
                if let Ok(line) = l {
                    // ignore empty lines and comment lines
                    !line.starts_with("c ") && !line.is_empty()
                } else {
                    true
                }
            });
        let mut lines = lines.into_iter();
        // p td <n> <m>
        let (n, m) = {
            let line = lines.next().ok_or(ImportError::InputMalformedError)??;
            let mut s = line.split(' ');
            if let Some("p") = s.next() {} else { return Err(ImportError::InputMalformedError); }
            if let Some("td") = s.next() {} else { return Err(ImportError::InputMalformedError); }
            let n: usize = s.next().ok_or(ImportError::InputMalformedError)?.parse()?;
            let m: usize = s.next().ok_or(ImportError::InputMalformedError)?.parse()?;
            if s.next().is_some() { return Err(ImportError::InputMalformedError); }
            (n, m)
        };
        let mut adj_list = vec![Some(FxHashSet::default()); n];
        let mut num_edges = 0;
        for line in lines {
            // <src> <trg>
            let line = line?;
            let mut s = line.split(' ');
            let src = s.next().ok_or(ImportError::InputMalformedError)?.parse::<usize>()? - 1;
            let trg = s.next().ok_or(ImportError::InputMalformedError)?.parse::<usize>()? - 1;
            if s.next().is_some() { return Err(ImportError::InputMalformedError); }
            adj_list[src].as_mut().unwrap().insert(trg);
            adj_list[trg].as_mut().unwrap().insert(src);
            num_edges += 1;
        }
        if num_edges != m { return Err(ImportError::InputMalformedError); }
        Ok(DyUGraph {
            adj_list,
        })
    }

    /// Splits `self` into its connected components.
    /// Returns the components.
    pub fn split_into_connected(&self) -> Vec<Self> {
        let big_n = self.num_reserved(); 
        let mut components = Vec::new();
        let mut marked = FxHashSet::default();
        for node in self.nodes() {
            if marked.contains(&node) {
                continue
            }
            let mut adj_list = vec![None; big_n];
            for reach in self.reachable(node) {
                marked.insert(reach);
                adj_list[reach] = self.adj_list[reach].clone();
            }
            components.push(DyUGraph {
                adj_list
            });
        }
        components
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn read_gr_test() {
        let gr = Cursor::new("p td 7 9\n1 2\n1 3\n2 3\n4 5\n4 6\n4 7\n5 6\n5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
    }

    #[test]
    fn greedy_max_clque_test() {
        let gr = Cursor::new("p td 7 9\n1 2\n1 3\n2 3\n4 5\n4 6\n4 7\n5 6\n5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        assert_eq!(graph.greedy_max_clique().len(), 4);
    }

    #[test]
    fn connected_test() {
        let gr = Cursor::new("p td 7 9\n1 2\n1 3\n2 3\n4 5\n4 6\n4 7\n5 6\n5 7\n6 7\n");
        let graph = DyUGraph::read_gr(gr);
        assert!(graph.is_ok());
        let graph = graph.unwrap();
        assert!(graph.disconnected());
        let mut graphs = graph.split_into_connected();
        assert_eq!(graphs.len(), 2);
        let g1 = graphs.pop().unwrap();
        let g2 = graphs.pop().unwrap();
        if g1.num_nodes() == 3 {
            assert_eq!(g1.greedy_max_clique().len(), 3);
        } else {
            assert_eq!(g2.greedy_max_clique().len(), 3);
        }
    }

}
