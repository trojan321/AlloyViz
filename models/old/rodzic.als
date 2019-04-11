module models/person

abstract sig Person {
	pets: set Animal,
	father: lone Man,
	mother: lone Woman
}
sig Woman extends Person {
	husband: lone Man
}
sig Man extends Person {
	wife: lone Woman
}
sig Animal {}
{
	#(pets.this)<=1
}
sig Cat, Bird, Rabbit in Animal { }
sig Canary in Bird { }

fact DifferentSpecies {
	disj[Cat, Bird, Rabbit]
}

fact {
	no p: Person | p in p.^(mother+father)
}
fun parents (p: Person): set Person{
	p.mother + p.father
}
pred orphans {
	some p: Person | lone parents[p]
}
run orphans for 5 but 2 Woman

fact {
	no p: Person | p in p.^(mother+father)
	wife = ~husband
}

assert NoSelfFather {
	no m: Man | m = m.father
}

// This should not find any counterexample.
check NoSelfFather

fun grandpas [p: Person] : set Person {
	p.(mother+father).father
	}

pred ownGrandpa [p: Person] {
	p in p.grandpas
	}

// This should not find any instance.
run ownGrandpa for 4 Person

assert NoSelfGrandpa {
	no p: Person | p in p.grandpas
	}

// This should not find any counterexample
check NoSelfGrandpa for 4 Person

