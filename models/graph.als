module util/graph[Node1]

/*
 * Utilities for some common operations and contraints
 * on graphs.
 *
 * author: Greg Dennis
 */

open util/relation as rel

/** graph in undirected */
pred undirected [r: Node1->Node1] {
  symmetric[r]
}

/** graph has no self-loops */
pred noSelfLoops[r: Node1->Node1] {
  irreflexive[r]
}

/** graph is weakly connected */
pred weaklyConnected[r: Node1->Node1] {
  all n1, n2: Node1 | n1 in n2.*(r + ~r)  // Changed from ^ to * to permit singleton
}

/** graph is strongly connected */
pred stronglyConnected[r: Node1->Node1] {
  all n1, n2: Node1 | n1 in n2.*r         // Changed from ^ to * to permit singleton
}

/** graph is rooted at root */
pred rootedAt[r: Node1->Node1, root: Node1] {
  Node1 in root.*r
}

/** graph is a ring */
pred ring [r: Node1->Node1] {
  all n: Node1 | one n.r && rootedAt[r, n]
}

/** graph is a dag */
pred dag [r: Node1->Node1] {
  acyclic[r, Node1]
}

/** graph is a forest */
pred forest [r: Node1->Node1] {
  dag[r]
  all n: Node1 | lone r.n
}

/** graph is a tree */
pred tree [r: Node1->Node1] {
  forest[r]
  lone root: Node1 | no r.root
}

/** graph is a tree rooted at root */
pred treeRootedAt[r: Node1->Node1, root: Node1] {
  forest[r]
  rootedAt[r, root]
}

/** returns the roots of the graph */
fun roots [r: Node1->Node1] : set Node1 {
  Node1 - Node1.^r
}

/** returns the leaves of the grpah */
fun leaves [r: Node1->Node1] : set Node1 {
  Node1 - Node1.^~r
}

/** returns the inner Node1s (non-leaves) of the graph */
fun  innerNode1s [r: Node1->Node1] : set Node1 {
  Node1 - leaves[r]
}
