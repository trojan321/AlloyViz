open util/ordering[House]
sig House {
    color: Color,
    nationality: Nationality,
    drink: Drink,
    cigarette: Cigarette,
    pet: Pet
}
abstract sig Color {}
one sig red extends Color {}
one sig green extends Color {}
one sig yellow extends Color {}
one sig blue extends Color {}
one sig white extends Color {}
abstract sig Nationality {}
one sig Englishman extends Nationality {}
one sig Swede extends Nationality {}
one sig Dane extends Nationality {}
one sig German extends Nationality {}
one sig Norwegian extends Nationality {}
abstract sig Drink {}
one sig tea extends Drink {}
one sig coffee extends Drink {}
one sig milk extends Drink {}
one sig beer extends Drink {}
one sig water extends Drink {}
abstract sig Cigarette {}
one sig Pall_Mall extends Cigarette {}
one sig Dunhills extends Cigarette {}
one sig Blend extends Cigarette {}
one sig Blue_Masters extends Cigarette {}
one sig Prince extends Cigarette {}
abstract sig Pet {}
one sig dog extends Pet {}
one sig bird extends Pet {}
one sig horse extends Pet {}
one sig cat extends Pet {}
one sig fish extends Pet {}
fact constraints {
    // There are five houses, each of a different color.
    some disj h1, h2, h3, h4, h5: House | 	h1.color = red and h2.color = green and h3.color = yellow and 
 					h4.color = blue and h5.color = white
    // In each house lives a man of a different nationality.
    no disj h,h': House | h.nationality = h'.nationality
    // 1. The Englishman lives in the red house.
    some h: House | (h.nationality = Englishman) and (h.color = red)
    // 2. The Swede keeps dogs.
    some h: House | (h.nationality = Swede) and (h.pet = dog)
    // 3. The Dane drinks tea.
    some h: House | (h.nationality = Dane) and (h.drink = tea)
    // 4. The green house is just to the left of the white one.
    some disj h, h': House | (h.color = green) and (h'.color = white) and (h'.prev = h)
    // 5. The owner of the green house drinks coffee.
    some h: House | (h.color = green) and (h.drink = coffee)
    // 6. The Pall Mall smoker keeps birds.
    some h: House | (h.cigarette = Pall_Mall) and (h.pet = bird)
    // 7. The owner of the yellow house smokes Dunhills.
    some h: House | (h.color = yellow) and (h.cigarette = Dunhills)
    // 8.  The man in the center house drinks milk.
    some h: House | (some h.prev.prev) and (some h.next.next) and (h.drink = milk)
    // 9. The Norwegian lives in the first house.
    some h: House | (h = first) and (h.nationality = Norwegian)
    // 10. The Blend smoker has a neighbor who keeps cats.
    some disj h,h': House | (h.cigarette = Blend) and (h'.pet = cat) and  ((h.prev = h') or (h.next = h')) 
    // 11. The man who smokes Blue Masters drinks beer.
    some h: House | (h.cigarette = Blue_Masters) and (h.drink = beer)
    // 12. The man who keeps horses lives next to the Dunhill smoker.
    some disj h,h': House | (h.pet = horse) and (h'.cigarette = Dunhills) and ((h.next = h') or (h.prev = h'))
    // 13. The German smokes Prince.
    some h: House | (h.nationality = German) and (h.cigarette = Prince)
    // 14. The Norwegian lives next to the blue house.
    some disj h,h': House | (h.nationality = Norwegian) and (h'.color= blue) and (h.next = h')
    // 15. The Blend smoker has a neighbor who drinks water.
    some disj h,h': House | (h.cigarette = Blend) and (h'.drink = water) and ((h.next = h') or (h.prev = h'))
}
run {} for 5

