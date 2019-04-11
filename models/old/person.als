module models/person
abstract sig Person {
	pets: set Animal,
	father: lone Man,
	mother: lone Woman
}
sig Woman, Man extends Person { }
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
	no p : Person | p in p.^(father + mother)
}
fun parents (p: Person): set Person{
	p.mother + p.father
}
pred orphans {
	some p: Person | lone parents[p]
}
run orphans for 5 but 2 Woman

assert noSelfParent {
	irreflexive[father+mother]
}
check noSelfParent for 3

