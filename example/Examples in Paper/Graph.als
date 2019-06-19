module Graph

/*
 * ➀ Multigraph
 * ➁ Undirected
 * ➂ DAG
 * ➃ Tree
 * ➄ Vertex labeled
 * ➅ Binary search tree
*/

fact FeatureModel {
	// DAG incompatible with Undirected
	➁➂some none➂➁
	// Tree requires DAG
	➃➌some none➌➃
	// Binary search tree requires Tree
	➅➍some none➍➅
	// Binary search tree requires Vertex labeled
	➅➎some none➎➅
}

sig Node {
	adj : set Node,
	➄label : one Label➄
}

➄sig Label {}➄

➃lone sig Root extends Node {}➃

sig Edge {
	src, dst : one Node
}

➅sig Left, Right extends Edge {}➅


fact {
	// Auxiliary relation two help with visualization and specification
	adj = ~src.dst
	// No multiple edges
	➊all disj e,e' : Edge | e.src != e'.src or e.dst != e'.dst➊
	// The adjency relation is symetric
	➁adj = ~adj➁
	// No cycles
	➂all n : Node | n not in n.^adj➂
	// All nodes except the root have one parent
	➃all n : Node-Root | one adj.n➃
	// Labels are unique
	➄label in Node lone -> Label➄
	// In binary search tree all edges are either left or right
	// This is an example where it would be nice to mark the abstract keyword
	➅Edge = Left+Right➅
	// Each node has at most one left and one right adjacent
	➅all n : Node | lone (src.n & Left).dst and lone (src.n & Right).dst➅
	// The left and right adjacents must be distinct
	➅all n : Node | no (src.n & Left).dst & (src.n & Right).dst➅
}

run {} with exactly ➊,➋,➌,➍,➎,➏ for 5 -- not working correctly, some features are selected
run {} with ➊,➋,➌,➍,➎,➏ for 5 -- not working correctly without the above fact
run {} with exactly ➀ for 5
run {} with exactly ➁ for 5
run {} with exactly ➂ for 5
run {} with exactly ➃ for 5 expect 0
run {} with exactly ➄ for 5
run {} with exactly ➅ for 5 expect 0
run {} with exactly ➀,➁ for 5
run {} with exactly ➀,➂ for 5
run {} with exactly ➀,➃ for 5 expect 0
run {} with exactly ➀,➄ for 5
run {} with exactly ➀,➅ for 5 expect 0
run {} with exactly ➁,➂ for 5 expect 0
run {} with exactly ➁,➃ for 5 expect 0
run {} with exactly ➁,➄ for 5
run {} with exactly ➁,➅ for 5 expect 0
run {} with exactly ➂,➃ for 5
run {} with exactly ➂,➄ for 5
run {} with exactly ➂,➅ for 5 expect 0
run {} with exactly ➃,➄ for 5 expect 0
run {} with exactly ➃,➅ for 5 expect 0
run {} with exactly ➄,➅ for 5 expect 0

run {} with exactly ➂,➃,➄,➅ for 2
run {} with exactly ➀,➂,➃,➄,➅ for 5

assert Connected {
	// All nodes descend from root
	➃Node in Root.*adj➃
}

check Connected with ➃ for 8 -- Not working correctly without the above fact
check Connected with exactly ➂,➃ for 8
check Connected with exactly ➀,➂,➃ for 8
check Connected with exactly ➂,➃,➄ for 8
check Connected with exactly ➀,➂,➃,➄ for 8
check Connected with exactly ➂,➃,➄,➅ for 8
check Connected with exactly ➀,➂,➃,➄,➅ for 8

assert SourcesAndSinks {
	// If the graph is not empty there is at least one source and one sink node
	some Node implies (some n : Node | no adj.n and some n : Node | no n.adj)
}

check SourcesAndSinks with ➂ for 7

