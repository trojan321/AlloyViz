module models/ringlead

/*
 * Model of leader election on a ring
 *
 * Each process has a unique ID, IDs are ordered.
 * The algorithm elects the process with the highest
 * ID the leader, as follows.  First, each process
 * sends its own ID to its right neighbor.
 * Then, whenever a process receives an ID, if the
 * ID is greater than the process' own ID it forwards
 * the ID to its right neighbor, otherwise does nothing.
 * When a process receives its own ID that process
 * is the leader.
 */

open models/boolean as bool
open models/messaging as msg
open models/ordering[msg/Node1] as Node1Ord
open models/ordering[msg/Tick] as tickOrd

sig RingLeadNode1 extends msg/Node1 {
   rightNeighbor: msg/Node1
}

fact DefineRing {
  (one msg/Node1 || (no n: msg/Node1 | n = n.rightNeighbor))
  all n: msg/Node1 | msg/Node1 in n.^rightNeighbor
}

sig RingLeadMsgState extends msg/MsgState {
  id: msg/Node1
}

sig MsgViz extends msg/Msg {
  vFrom: msg/Node1,
  vTo: set msg/Node1,
  vId: msg/Node1
}

fact {
  MsgViz = msg/Msg
  vFrom = state.from
  vTo = state.to
  vId = state.id
}


sig RingLeadNode1State extends msg/Node1State {
  leader: Bool
}


pred RingLeadFirstTrans [self: msg/Node1, pre, post: msg/Node1State,
                        sees, reads, sends, needsToSend: set msg/Msg] {
   one sends
   # needsToSend = 1
   sends.state.to = self.rightNeighbor
   sends.state.id = self
   post.leader = False
}

fact InitRingLeadState {
  all n: msg/Node1 |
    tickOrd/first.state[n].leader = False
}

pred RingLeadRestTrans [self: msg/Node1, pre, post: msg/Node1State,
                       sees, reads, sends, needsToSend: set msg/Msg] {
   RingLeadTransHelper[self, sees, reads, sends, needsToSend]
   post.leader = True iff (pre.leader = True ||
                           self in reads.state.id)
}

/**
 * we take any messages whose Node1 ids are higher than ours,
 * and we forward them to the right neighbor.  we drop
 * all other messages.  if we get a message with our own
 * id, we're the leader.
 */
pred RingLeadTransHelper[self: msg/Node1, sees, reads, sends, needsToSend: set msg/Msg] {
   reads = sees

   all received: reads |
     (received.state.id in Node1Ord/nexts[self]) =>
       (one weSend: sends | (weSend.state.id = received.state.id && weSend.state.to = self.rightNeighbor))

   all weSend: sends | {
     let mID = weSend.state.id | {
       mID in Node1Ord/nexts[self]
       mID in reads.state.id
       weSend.state.to = self.rightNeighbor
     }
     //weSend.sentBecauseOf = { received : reads | received.id = weSend.id }
     //all otherWeSend: sends - weSend | otherWeSend.id != weSend.id
   }

   # needsToSend = # { m: reads | m.state.id in Node1Ord/nexts[self] }
}
fact RingLeadTransitions {
   all n: msg/Node1 {
      all t: msg/Tick - tickOrd/last | {
         t = tickOrd/first =>
           RingLeadFirstTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
         else
           RingLeadRestTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
      }
      // also constrain last tick
      RingLeadTransHelper[n, tickOrd/last.visible[n], tickOrd/last.read[n], tickOrd/last.sent[n], tickOrd/last.needsToSend[n]]
   }
}

assert OneLeader {
   all t: msg/Tick |
      lone n: msg/Node1 |
         t.state[n].leader = True
}

fact CleanupViz {
  RingLeadNode1 = msg/Node1
  RingLeadMsgState = msg/MsgState
  RingLeadNode1State = msg/Node1State
}

pred SomeLeaderAtTick[t: msg/Tick] {
  some n: msg/Node1 | t.state[n].leader = True
}

pred NeverFindLeader {
  msg/Loop
  all t: msg/Tick | ! SomeLeaderAtTick[t]
}

assert Liveness {
  (msg/NoLostMessages && msg/NoMessageShortage) => ! NeverFindLeader
}

pred SomeLeader { some t: msg/Tick | SomeLeaderAtTick[t] }

assert LeaderHighest {
  all t: msg/Tick, n: msg/Node1 |
    t.state[n].leader = True => n = Node1Ord/last
}

run NeverFindLeader for 1 but 3 msg/Tick, 2 Bool, 2 msg/Node1State expect 1
check Liveness for 3 but 6 msg/Msg, 2 Bool, 2 msg/Node1State expect 0
check OneLeader for 5 but 2 Bool, 2 msg/Node1State expect 0
run SomeLeader for 2 but 3 msg/Node1, 5 msg/Msg, 5 msg/Tick, 5 msg/MsgState expect 1
check LeaderHighest for 3 but 2 msg/Node1State, 5 msg/Msg, 5 msg/MsgState, 5 msg/Tick expect 0

