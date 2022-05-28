use crate::vc_instance::VCInstance;
use fxhash::FxHashSet;
use std::collections::{HashMap, HashSet};

pub struct MaxCliqueInstance {
    pub ordering: Vec<usize>,
    pub adj_matrix: Vec<bool>,
    pub n: usize,
}


impl MaxCliqueInstance {

    fn get_branches_d0(&self, sub_start: usize, sub_end: usize, colors: usize) -> (Vec<usize>, Vec<FxHashSet<usize>>) {
        let mut indiess: Vec<FxHashSet<usize>> = Vec::new();
        let mut b: Vec<usize> = Vec::new();
        'outer: for node in sub_end..(sub_start - 1) {
            // Try to add `node` in the first indipendent set.
            for indies in indiess.iter_mut() {
                if !indies.iter().any(|other| self.adj_matrix[node*self.n+other]) {
                    indies.insert(node);
                    continue 'outer
                }
            }
            // If `node` does not fit in any previous indipendent set and there is still place for
            // indipendent sets, add a new indipendent containing  `node`.
            if indiess.len() < colors {
                indiess.push(vec![node].into_iter().collect());
            } else {
                for i in 0..indiess.len() {
                    // find first indipendent set that contains only one node connected to `node`.
                    let mut count = 0;
                    let mut indies = &mut indiess[i];
                    if !indies.iter().any(|other| {
                        if self.adj_matrix[node*self.n+other] {
                            count += 1;
                            return count == 2
                        }
                        false
                    }){
                        // get match 
                        let other = *indies.iter().find(|other| self.adj_matrix[node*self.n+**other]).expect("exactly one such node exists");
                        // check other fits
                        for j in (i+1)..indiess.len() {
                            let mut indies2 = &mut indiess[j];
                            if !indies2.iter().any(|otterother| self.adj_matrix[other*self.n+otterother]) {
                                indies2.insert(other);
                                indies.remove(&other);
                                indies.insert(node);
                                continue 'outer
                            }
                        }
                    }
                }
                b.push(node);
            }
        }
        (b, indiess)
    }

    /// `b_set` needs to be ordered in respective to the ordering (decreasing)
    fn inc_max_sat(&self, start: usize, end: usize, a_set: &Vec<Vec<usize>>, b_set: &mut Vec<usize>) 
        -> Vec<usize> {
        todo!();
        let mut hard: Vec<HashSet<(bool,usize, bool)>> = Vec::new();
        let mut soft: Vec<HashSet<(bool,usize, bool)>> = Vec::new();
        for i in start..(end+1) {
            for j in (i+1)..(end+1) {
                if !self.adj_matrix[i*self.n+j] {
                    hard.push(vec![(false, i, true), (false, j, true)].into_iter().collect());
                }
            }
        }
        for indie in a_set {
            soft.push(indie.iter().map(|node| (true, *node, true)).collect());
        }
        while !b_set.is_empty() {
            // Where and how do we define reasons?
            let mut reasons: HashMap<Vec<usize>, usize> = HashMap::new();
            // Pop?
            let b = b_set[b_set.len() - 1];
            soft.push(vec![(true,b,true)].into_iter().collect());
            let mut stack = Vec::new();
            stack.push(b);
            'mid: while !stack.is_empty() {
                let unit = stack.pop().expect("`stack` is not empty");
                reasons.insert(vec![unit], unit);

            }
        }
        b_set.clone()
    }


}


impl From<VCInstance> for MaxCliqueInstance {

    /// TODO other ordering for other densities
    fn from(vc_instance: VCInstance) -> Self {
        let mut g_clone = vc_instance.graph.clone();

        // Ordering 
        let mut ordering = Vec::new();
        let n = g_clone.num_nodes();
        let mut place_in_ordering = vec![n;g_clone.num_reserved()];
        while let Some(max_node) = g_clone.max_degree_node() {
            g_clone.delete_node(max_node);
            place_in_ordering[max_node] = ordering.len();
            ordering.push(max_node);
        }
        let mut adj_matrix = vec![true;n*n]; 
        for i in 0..n {
            adj_matrix[i*n+i] = false;
        }
        for (a, b) in vc_instance.graph.edges() {
            adj_matrix[ordering[a]*n+ordering[b]] = false;
            adj_matrix[ordering[b]*n+ordering[a]] = false;
        }
        MaxCliqueInstance { 
            ordering, 
            adj_matrix,
            n 
        }
    }
}
