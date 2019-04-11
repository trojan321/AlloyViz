module appendixA/undirected

sig Node1 { adjs: set Node1 }

pred acyclic {
	adjs = ~adjs
	// You have to fill in additional formula here
}

run acyclic for 4

