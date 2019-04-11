/*
 * a simple List1 module
 * which demonstrates how to create predicates and fields that mirror each other
 *   thus allowing recursive constraints (even though recursive predicates are not
 *   currently supported by Alloy)
 * author: Robert Seater
 */

module List1

sig Thing {}
fact NoStrayThings {Thing in List1.car}

abstract sig List1 {
    equivTo: set List1,
    prefixes: set List1
    }
sig NonEmptyList1 extends List1 {
    car: one Thing,
    cdr: one List1
    }
sig EmptyList1 extends List1 {}

pred isFinite [L:List1] {some e: EmptyList1 | e in L.*cdr}
fact finite {all L: List1 | isFinite[L]}

fact Equivalence {
    all a,b: List1 | (a in b.equivTo) <=> ((a.car = b.car and b.cdr in a.cdr.equivTo) and (#a.*cdr = #b.*cdr))
    }
assert reflexive {all L: List1 | L in L.equivTo}
check reflexive for 6 expect 0
assert symmetric {all a,b: List1 | a in b.equivTo <=> b in a.equivTo}
check symmetric for 6 expect 0
assert empties {all a,b: EmptyList1 | a in b.equivTo}
check empties for 6 expect 0

fact prefix { //a is a prefix of b
    all e: EmptyList1, L:List1 | e in L.prefixes
    all a,b: NonEmptyList1 | (a in b.prefixes) <=> (a.car = b.car
                                                and a.cdr in b.cdr.prefixes
                                                and #a.*cdr < #b.*cdr)
}

pred show {
    some a, b: NonEmptyList1 | a!=b && b in a.prefixes
    }
run show for 4 expect 1

