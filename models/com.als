module examples/case_studies/com

/*
 * Model of Microsoft Component1 Object Model (COM) query
 * interface and aggregation mechanism.
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/~dnj/publications/com-fse00.pdf
 *
 * author: Daniel Jackson
 */

open util/relation as rel

sig IID {}

sig Interface {
  qi : IID -> lone Interface,
  iids : set IID,
  // next two lines should use domain() or range() functions
  iidsKnown : IID,
  reaches : Interface
}{
  iidsKnown = dom[qi]
  reaches = ran[qi]
}

sig Component1 {
  interfaces : set Interface,
  iids : set IID,   // can't do iids = interfaces.Interface$iids
  first, identity : interfaces,
  eqs: set Component1,
  aggregates : set Component1
}

fact defineEqs {
  all c1, c2: Component1 |
    c1->c2 in eqs <=> c1.identity = c2.identity
}

fact IdentityAxiom {
  some unknown : IID | all c : Component1 |
    all i : c.interfaces | unknown.(i.qi) = c.identity
}

fact Component1Props {
  all c : Component1 {
    c.iids = c.interfaces.iids
    all i : c.interfaces | all x : IID | x.(i.qi) in c.interfaces
  }
}

sig LegalInterface extends Interface { }
fact { all i : LegalInterface | all x : i.iidsKnown | x in x.(i.qi).iids}

sig LegalComponent1 extends Component1 { }
fact { LegalComponent1.interfaces in LegalInterface }

fact Reflexivity { all i : LegalInterface | i.iids in i.iidsKnown }
fact Symmetry { all i, j : LegalInterface | j in i.reaches => i.iids in j.iidsKnown }
fact Transitivity { all i, j : LegalInterface | j in i.reaches => j.iidsKnown in i.iidsKnown }

fact Aggregation {
    no c : Component1 | c in c.^aggregates
    all outer : Component1 | all inner : outer.aggregates |
      (some inner.interfaces & outer.interfaces)
      && (some o: outer.interfaces | all i: inner.interfaces - inner.first | all x: Component1  | (x.iids).(i.qi) = (x.iids).(o.qi))
    }

assert Theorem1 {
     all c: LegalComponent1 | all i: c.interfaces | i.iidsKnown = c.iids
     }

assert Theorem2 {
    all outer: Component1 | all inner : outer.aggregates |
        inner in LegalComponent1 => inner.iids in outer.iids
    }

assert Theorem3 {
    all outer: Component1 | all inner : outer.aggregates | inner in outer.eqs
    }

assert Theorem4a {
      all c1: Component1, c2: LegalComponent1 |
         some (c1.interfaces & c2.interfaces) => c2.iids in c1.iids
    }

assert Theorem4b {
      all c1, c2: Component1 | some (c1.interfaces & c2.interfaces) => c1 in c2.eqs
      }

check Theorem1 for 3 expect 0
check Theorem2 for 3 expect 0
check Theorem3 for 3 expect 0
check Theorem4a for 3 expect 0
check Theorem4b for 3 expect 0
