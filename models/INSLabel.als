module examples/case_studies/INSLabel

/*
 * Models an Intentional Naming System (INS), a scheme for
 * dynamic resource discovery in a dynamic environment.
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/pubs/2000/INS_ASE00.pdf
 *
 * author: Sarfraz Khurshid
 */

sig Record {}

sig Label {}

sig Node1 {
  label: Label
}

sig LabelTree {
  root: Node1,
  Node1s: set Node1,
  children: Node1s one -> (Node1s - root)
}
{ // connected
  Node1s = root.*children
  some root.children
}

pred Get[db: DB, r: Record, a:Advertisement] {
  root[a] = root[db]
  Node1s[a] =
    Node1s[db]  & r.~(db.recs).*(~(db.children))
  aNode1s[a] =
    aNode1s[db] & r.~(db.recs).*(~(db.children))
  vNode1s[a] =
    vNode1s[db] & r.~(db.recs).*(~(db.children))
  all n: a.Node1s |
      n.~(a.children) = n.~(db.children)
}

sig Attribute extends Label {}

sig Value extends Label {}

one sig Wildcard, Null extends Value {}

sig AVTree extends LabelTree {
  vNode1s, aNode1s: set Node1s
}
{
  root in vNode1s
  root.label = Null
  Null !in (vNode1s - root).label + aNode1s.label
  aNode1s.label in Attribute
  vNode1s.label in Value
  all n: Node1s | all /* disj */ c,c': n.children |
    c.label != c'.label
  all a: aNode1s | a.children in vNode1s && some a.children
  all v: vNode1s | v.children in aNode1s
  no Wildcard.~label.children
}

one sig Query extends AVTree {}
{
  all a: aNode1s | one a.children
}

one sig Advertisement extends AVTree {}
{
  Wildcard !in vNode1s.label
}

one sig DB extends AVTree {
  records: set Record,
  recs: (vNode1s - root) some -> records
}
{
  Wildcard !in vNode1s.label
  all a: aNode1s | no a.recs
  all v: vNode1s {
    no v.children => some v.recs
    no v.recs & v.^(~children).recs }
  all a: aNode1s | all disj v,v': a.children |
    (no v.*children.recs & v'.*children.recs)
}

one sig State {
  conforms: Query -> Advertisement -> Node1 -> Node1,
  lookup: DB -> Query -> Node1 -> Node1 -> Record
}

fact ConformsFixPoint {
  all q: Query | all a: Advertisement |
    all nq: Node1 | all na: Node1 |
      q.ConformsAux[a,nq,na] <=>
      {
       nq.label in Wildcard + na.label
       all nq': q.children[nq] | some na': a.children[na] |
         q.ConformsAux[a,nq',na']
      }
}

pred Query.ConformsAux[a: Advertisement, nq: Node1, na: Node1] {
  na in State.conforms[this][a][nq]
}

pred Conforms[q: Query, a:Advertisement] {
  q.ConformsAux[a, q.root, a.root]
}

fact LookupFixPoint {
  all db: DB, q: Query, T: Node1, n: Node1, r: Record |
    r in db.LookupAux[q,T,n] <=>                                  // record r is in the result if and only if
    {
     all na: n.(q.children) | all nv: na.(q.children) |            // for all child av-pairs (na,nv) of av-pair n in q
      some Ta: T.(db.children) {
         Ta.label = na.label                                       //  Ta is a child Node1 with attribute na
         nv.label = Wildcard =>                                    //  wildcard matching
           r in Ta.^(db.children).(db.recs) else                     //   r is a record of any child of Ta
           (some Tv: Ta.(db.children) {                             //  normal matching
             Tv.label = nv.label                                   //   Tv is a child of Ta with value nv
             no nv.(q.children) =>                                 //   if Tv is a leaf-Node1
               r in Tv.*(db.children).(db.recs) else                   //        r is a record of Tv or of v
               r in db.LookupAux[q,Tv,nv] }) }                     //   else r is a record of the recursive call at Tv
    }
}

fun DB.LookupAux[q: Query, vd: Node1, vq: Node1]: set Record {      // helper function for Lookup
  State.lookup[this][q][vd][vq]
}

fun Lookup[db: DB, q: Query]: set Record {                             // models Lookup-Name algorithm invocation
  db.LookupAux[q, db.root, q.root]
}

assert LookupConforms2 { //soundness and completeness
  all q: Query | all db: DB | all r: Record | all a: Advertisement |
    Get[db,r,a] => // all n: a.Node1s | n.~(db.children)
    {r in db.Lookup[q] <=> q.Conforms[a]}
}

// < 10 sec
check LookupConforms2 for 4 but 1 State, 3 LabelTree, 2 Record expect 0
// ~ 25 min
//check LookupConforms2 for 6 but 1 State, 3 LabelTree, 2 Record
//check LookupConforms2 for 6 but 1 State, 3 LabelTree, 3 Record
run Lookup for 3 expect 0
