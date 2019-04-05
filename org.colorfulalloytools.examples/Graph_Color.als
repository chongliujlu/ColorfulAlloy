-- Basic Graph
-- tree ➀ UniqueValues ➁ BinaryTree➂ SearchTree➃
--  BinarySearch➄ 
module Graph
-- a singleton graph contains multiple nodes
one sig Graph {
	nodes: set Node,
	➄searchRel: Node -> Int -> Node➄
} {
	Node in nodes
}

-- each node has multiple incoming and outgoing edges
sig Node {
	inEdges: set Edge, 
	outEdges: set Edge,
	edges: set Edge,
	➁val: one Int➁
} {
	edges = inEdges + outEdges
}
// each edge has a source and destination node
sig Edge {
	src: one Node, 
	dest: one Node
}
➃sig LeftEdge, RightEdge extends Edge { }{
	LeftEdge + RightEdge = Edge
}➃


// defines proper connections between nodes and edges
fact prevNext {
	all n: Node, e: Edge | 
		(n in e.src <=> e in n.outEdges) && 
		(n in e.dest <=> e in n.inEdges)
}
// determines the number of reachable nodes (incl. the given node)

fun reachableNodes [n: Node] : Int {
	#((n.^(edges.(src + dest)) - n))
}
// property that a graph has no double edges
pred noDoubleEdges {
	all e, e': Edge | e != e' => e.(src + dest) != e'.(src + dest)
}


// creates an instance without double edges
run noDoubleEdges with exactly ➀ for 5 --exactly method:  ➀ selected Tree with no Double Edge
run noDoubleEdges with exactly ➊,➁ for 5 --exactly method: 
run noDoubleEdges with exactly ➊ for 5 --has error 
run noDoubleEdges with ➊ for 5
run noDoubleEdges with exactly ➅ for 5 //  exactly method: no feature selected, Graph with no Double Edge(just try exactly no feature selected )
run noDoubleEdges for 5 -- Amalagmated method: 
run noDoubleEdges with  ➀ for 5 -- Amalgamated method:

// holds if the graph has no double edges
assert hasNoDoubleEdges {
	!noDoubleEdges
}
// checks whether the graph has no double edges
check hasNoDoubleEdges with exactly ➀ for 5
check hasNoDoubleEdges with exactly ➊,➁ for 5
check hasNoDoubleEdges with exactly ➅ for 5
check hasNoDoubleEdges  for 5

pred show { }

--run show for exactly 5 Node, 2 LeftEdge, 2 RightEdge, 4 Edge
pred isConnected {
➀	some n: Node | (Graph.nodes = n) || 
		(Graph.nodes = n.^(edges.(src + dest)))➀
}

pred noCycles {
➀	all n: Node | n not in (n.^(outEdges.dest) + n.^(inEdges.src))➀
}

pred loneParent {
➀	all n: Node | lone n.inEdges➀
}

fact {
	-- isTree
	➀noDoubleEdges➀ && ➀isConnected➀ && ➀noCycles➀ && ➀loneParent➀
	--uniqueValues
	➁all disj n, n': Node | n.val != n'.val➁
	--binaryTree
	➂all n: Node | #n.outEdges =< 2➂
	--searchTree
	➃all n: Node | (#n.outEdges = 2) => 
		(some n.outEdges & LeftEdge && some n.outEdges & RightEdge)➃
	➃all n: Node | all l: LeftEdge | all r: RightEdge | 
		(l in n.outEdges => 
			(validLeftSubTree [l.dest.*(outEdges.dest), n])) && 
		(r in n.outEdges  => 
			(validRightSubTree [r.dest.*(outEdges.dest), n]))➃
	-- Binary search , defineSearchRel
	➄all current: Node, key: Int, found: Node |
		 current -> key -> found in Graph.searchRel <=> 
		((➁current.val = key➁ && found = current) || 
			(➁current.val < key➁ && ((current.(outEdges) & ➃RightEdge➃).dest) -> key -> found in Graph.searchRel) ||
			 (➁current.val > key➁ && ((current.(outEdges) & ➃LeftEdge➃).dest) -> key -> found in Graph.searchRel))➄
}

assert isTree {
	--isTree
	➀all e, e': Edge | e != e' => e.(src + dest) != e'.(src + dest)➀
	➀some n: Node | (Graph.nodes = n) || 
		(Graph.nodes = n.^(edges.(src + dest)))➀
	➀all n: Node | n not in (n.^(outEdges.dest) + n.^(inEdges.src))➀
	➀all n: Node | lone n.inEdges &&
	➂(#n.outEdges =< 2)➂➀ --isBinaryTree
}
check isTree with exactly ➀ for 5 --exactly method: Tree 
check isTree with  ➀ for 5 -- amalgamate method 
check isTree with exactly ➀,➁ for 5 --exactly method:   UniqueValues graph
check isTree with exactly ➀,➂ for 5 --exactly method:  BinaryTree
check isTree with exactly ➀,➁,➂ for 5 --exactly method:  UniqueValues Binary  Tree


check isTree with exactly ➀,➂ for 5--isBinaryTree


pred validLeftSubTree[children: Node, parent: one Node] {
	-- has error, because of the empty body of ExprQt
	➃all child : Node | ➁child in children => child.val < parent.val➁➃
}

pred validRightSubTree[children: Node, parent: one Node] {
	-- has error, because of the empty body of ExprQt  if ➁ not selected
	➃all child : Node | ➁child in children => child.val > parent.val➁➃
}

fun search [n: Node, i: Int] : lone Node {
	➄let res = (i.(n.(Graph.searchRel)))| (one res) => res else none➄
} 

