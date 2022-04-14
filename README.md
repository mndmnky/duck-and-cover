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

### Heuristics and Approximations
* Algorithms to compute initial solutions, upper- and lower bounds. These include:
	* A simple two-approximation.
	* A lower bound heuristic that first removes cliques and then unbalanced edges.
	* An upper bound heuristic that, step-by-step removes the node with the highest degree.

### Exact Computation 
* A branch-and-reduce algorithm to compute the optimal solution.

## Changelog

### 1.0.0 
* Initial version. Includes the basic algorithms and data structure.

## Todo 

### 1.?.?
* Reductions:
	* Twin rule 
	* Crown rule 
	* LP or Flow rule 
	* Unconfined vertices/Diamond rule 
* Heuristics:
	* Special weight heuristics 
* Branch-and-reduce:
	* Mirror branching 
	* Satellite branching 
	* Packing branching



[^fn1]: Chen, Jianer, Iyad A. Kanj, and Weijia Jia. "Vertex cover: further observations and further improvements." Journal of Algorithms 41.2 (2001): 280-301.

[^fn2]: Butenko, Sergiy, et al. "Finding maximum independent sets in graphs arising from coding theory." Proceedings of the 2002 ACM symposium on Applied computing. 2002.

