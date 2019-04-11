module models/countryman

/*
 * Adapted from farmer.als model
 * The classic river crossing puzzle. A countryman is carrying a wolf, a
 * goat, and a sack of cabbage. He must cross a river using a boat
 * that can only hold the countryman and at most one other thing. If the
 * countryman leaves the wolf alone with the goat, the wolf will eat the
 * goat; and if he leaves the goat alone with the cabbage, the
 * goat will eat the cabbage. How can the countryman bring everything
 * to the far side of the river intact?
 *
 * authors: Greg Dennis, Rob Seater
 *
 * Acknowledgements to Derek Rayside and his students for finding and
 * fixing a bug in the "crossRiver" predicate.
 */

open util/ordering[State] as ord

/**
 * The countryman and all his possessions will be represented as Objects.
 * Some objects eat other objects when the Countryman's not around.
 */
abstract sig Object { eats: set Object }
one sig Countryman, Wolf, Goat, Cabbage extends Object {}

/**
 * Define what eats what when the Countryman' not around.
 * Wolf eats the Goat and the Goat eats the cabbage.
 */
fact eating { eats = Wolf->Goat + Goat->Cabbage }

/**
 * The near and far relations contain the objects held on each
 * side of the river in a given state, respectively.
 */
sig State {
   near: set Object,
   far: set Object
}

/**
 * In the initial state, all objects are on the near side.
 */
fact initialState {
   let s0 = ord/first |
     s0.near = Object && no s0.far
}

/**
 * Constrains at most one item to move from 'from' to 'to'.
 * Also constrains which objects get eaten.
 */
pred crossRiver [from, from', to, to': set Object] {
   // either the Countryman takes no items
   (from' = from - Countryman - from'.eats and
    to' = to + Countryman) or
    // or the Countryman takes one item
    (one x : from - Countryman | {
       from' = from - Countryman - x - from'.eats
       to' = to + Countryman + x })
}

/**
 * crossRiver transitions between states
 */
fact stateTransition {
  all s: State, s': ord/next[s] {
    Countryman in s.near =>
      crossRiver[s.near, s'.near, s.far, s'.far] else
      crossRiver[s.far, s'.far, s.near, s'.near]
  }
}

/**
 * the countryman moves everything to the far side of the river.
 */
pred solvePuzzle {
     ord/last.far = Object
}

run solvePuzzle for 8 State expect 1

/**
 * no Object can be in two places at once
 * this is implied by both definitions of crossRiver 
 */
assert NoQuantumObjects {
   no s : State | some x : Object | x in s.near and x in s.far
}

check NoQuantumObjects for 8 State expect 0








