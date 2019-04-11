module examples/toys/genealogy

abstract sig Person {spouse: lone Person, parents: set Person}
{
    -- nobody is his or her own ancestor
    this not in this.^@parents
}
sig Man, Woman extends Person {}
one sig Eve extends Woman {}
one sig Adam extends Man {}

fact Bible {
    -- every person except Adam and Eve has a mother and father
    all p: Person - (Adam + Eve) | one mother: Woman, father: Man |
        p.parents = mother + father
    -- Adam and Eve have no parents
    no (Adam + Eve).parents
    -- Adam's spouse is Eve
    Adam.spouse = Eve
    }

fact SocialNorms {
    -- nobody is his or her own spouse
    no p: Person | p.spouse = p
    -- spouse is symmetric
    spouse = ~spouse
    -- a man's spouse is a woman and vice versa
    Man.spouse in Woman && Woman.spouse in Man
    }

fact NoIncest {
    -- can't marry a sibling
    no p: Person | some p.spouse.parents & p.parents
    -- can't marry a parent
    no p: Person | some p.spouse & p.parents
    }

fun getSiblings(p:Person): set Person{
	p.(parents).~(parents) - p
}

pred Show {
    some p: Person - (Adam + Eve) | some p.spouse
    }
run Show for 6 expect 1

assert noOneIsOwnParent {
no p: Person |  p in p.^parents
}
check noOneIsOwnParent expect 0
