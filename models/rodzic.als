module przyklad/schemat1
open util/relation
abstract sig Osoba {
	posiadane_zwierzeta: set Zwierze,
	ojciec: lone Mezczyzna,
	matka: lone Kobieta
}
sig Kobieta, Mezczyzna extends Osoba { }
sig Zwierze {}
{
	#(posiadane_zwierzeta.this)<=1
}
sig Kot, Ptak, Krolik in Zwierze { }
sig Kanarek in Ptak { }

fact rozneGatunki {
	disj[Kot, Ptak, Krolik]
}

fact {
	all x : Osoba | x not in x.^(ojciec + matka)
}
fun rodzice (o: Osoba): set Osoba{
	o.matka + o.ojciec
}
pred maksymalnieJedenRodzic{
	some x: Osoba | lone rodzice[x]
}
run maksymalnieJedenRodzic for 5 but 2 Kobieta

assert nieMoznaBycSwoimRodzicem {
	irreflexive[ojciec+matka]
}
check nieMoznaBycSwoimRodzicem for 3

