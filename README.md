# Duck and Cover 

## A Vertex Cover Solver

A solver for the vertex cover problem. This library provides algorithms and data structure to solve the vertex cover problem (efficiently). Functionalities include:

### Dynamic simple graph 
* A undirected, simple graph data structure that allows for dynamic behavior.

### Kernelization 
* Simple and advanced reduction rules to create a smaller problem instance. These rules include the following:
	* Removal of isolated nodes and nodes of degree 1. 
	* Contraction of link nodes [^fn1].
	* Reduction of Cliques [^fn2].
	* Twin node rule [^fn3]. (with contraction TODO: cite)
	* Unconfined node rule as described in [^fn4], here dubbed `dominion` rule.
	* Network flow rule as described in [^fn5].
		* And its improvements as described in [^fn8].
	* Alternatives (funnel & desk) as described in [^fn6].

### Heuristics and Approximations
* Algorithms to compute initial solutions, upper- and lower bounds. These include:
	* A simple two-approximation.
	* A lower bound heuristic that first removes cliques and then unbalanced edges.
	* An upper bound heuristic that, step-by-step removes the node with the highest degree.

### Exact Computation 
* A branch-and-reduce algorithm to compute the optimal solution.
	* Includes mirror branching as described by [^fn7].

## Changelog

### 1.0.0 
* Initial version. Includes the basic algorithms and data structure.

### 1.0.1
* Fix input format to fit the PACE19 challenge format.
* Fix improper merging.

### 1.0.2
* Fixed bug in `finallize_solution()`.
* Improved `branch_and_reduce()`.
* Fix output format to fit the PACE19 challenge format.

### 1.1.0
* Twin rule
* Dominion rule

### 1.2.0
* Network flow rule

### 1.3.0 
* Added diamond case to dominion rule.
* Local `k` node rule
* Crown rule

### 1.3.1 
* `DyUGraph.from_edge_iter()`

### 1.4.0
* (Core rule)
* Alternatives (Funnel rule)

### 1.4.1
* Extended alternatives with the desk rule
* Improved twin rule

### 1.5.0
* Improved vertex selection for branching 
* Mirror branching

### 1.6.0
* Improved LP rule (finding balanced independent sets)

## Todo 

### 1.6.1
* Carry LP network along

### 1.7.0
* MoMR branching

### 1.?.?
* Packing
	* Branching
	* Rules
* Initial local search 


[^fn1]: Chen, Jianer, Iyad A. Kanj, and Weijia Jia. "Vertex cover: further observations and further improvements." Journal of Algorithms 41.2 (2001): 280-301.

[^fn2]: Butenko, Sergiy, et al. "Finding maximum independent sets in graphs arising from coding theory." Proceedings of the 2002 ACM symposium on Applied computing. 2002.

[^fn3]: Xiao, Mingyu, and Hiroshi Nagamochi. "Confining sets and avoiding bottleneck cases: A simple maximum independent set algorithm in degree-3 graphs." Theoretical Computer Science 469 (2013): 92-104.

[^fn4]: Akiba, Takuya, and Yoichi Iwata. "Branch-and-reduce exponential/FPT algorithms in practice: A case study of vertex cover." Theoretical Computer Science 609 (2016): 211-225.

[^fn5]: Abu-Khzam, Faisal N., et al. "Kernelization algorithms for the vertex cover problem." (2017).

[^fn6]: Xiao, Mingyu, and Hiroshi Nagamochi. "Confining sets and avoiding bottleneck cases: A simple maximum independent set algorithm in degree-3 graphs." Theoretical Computer Science 469 (2013): 92-104.

[^fn7]: Fomin, Fedor V., Fabrizio Grandoni, and Dieter Kratsch. "A measure & conquer approach for the analysis of exact algorithms." Journal of the ACM (JACM) 56.5 (2009): 1-32.

[^fn8]: Iwata, Yoichi, Keigo Oka, and Yuichi Yoshida. "Linear-time FPT algorithms via network flow." Proceedings of the twenty-fifth annual ACM-SIAM symposium on Discrete algorithms. Society for Industrial and Applied Mathematics, 2014.
