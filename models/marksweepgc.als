module examples/systems/marksweepgc

/*
 * Model of mark and sweep garbage collection.
 */

// a Node1 in the heap
sig Node1 {}

sig HeapState {
  left, right : Node1 -> lone Node1,
  marked : set Node1,
  freeList : lone Node1
}

pred clearMarks[hs, hs' : HeapState] {
  // clear marked set
  no hs'.marked
  // left and right fields are unchanged
  hs'.left = hs.left
  hs'.right = hs.right
}

/**
 * simulate the recursion of the mark() function using transitive closure
 */
fun reachable[hs: HeapState, n: Node1] : set Node1 {
  n + n.^(hs.left + hs.right)
}

pred mark[hs: HeapState, from : Node1, hs': HeapState] {
  hs'.marked = hs.reachable[from]
  hs'.left = hs.left
  hs'.right = hs.right
}

/**
 * complete hack to simulate behavior of code to set freeList
 */
pred setFreeList[hs, hs': HeapState] {
  // especially hackish
  hs'.freeList.*(hs'.left) in (Node1 - hs.marked)
  all n: Node1 |
    (n !in hs.marked) => {
      no hs'.right[n]
      hs'.left[n] in (hs'.freeList.*(hs'.left))
      n in hs'.freeList.*(hs'.left)
    } else {
      hs'.left[n] = hs.left[n]
      hs'.right[n] = hs.right[n]
    }
  hs'.marked = hs.marked
}

pred GC[hs: HeapState, root : Node1, hs': HeapState] {
  some hs1, hs2: HeapState |
    hs.clearMarks[hs1] && hs1.mark[root, hs2] && hs2.setFreeList[hs']
}

assert Soundness1 {
  all h, h' : HeapState, root : Node1 |
    h.GC[root, h'] =>
      (all live : h.reachable[root] | {
        h'.left[live] = h.left[live]
        h'.right[live] = h.right[live]
      })
}

assert Soundness2 {
  all h, h' : HeapState, root : Node1 |
    h.GC[root, h'] =>
      no h'.reachable[root] & h'.reachable[h'.freeList]
}

assert Completeness {
  all h, h' : HeapState, root : Node1 |
    h.GC[root, h'] =>
      (Node1 - h'.reachable[root]) in h'.reachable[h'.freeList]
}

check Soundness1 for 3 expect 0
check Soundness2 for 3 expect 0
check Completeness for 3 expect 0
