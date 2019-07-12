module ROSArchitectureV1
open util/ordering [Time]

/**
This model was divided in 2 fundamental parts.
      The first section depicts the strutural part of a simple ROS architecture, that can be seen as 
		a group of nodes organized in a linear structure.
      The second parts depicts the behavioural part of the system. Since the flow of the messages within the system, up to
		the behaviour of each individual node.
*/
sig Time{}

abstract sig Node {	
	subscribes: set Topic,
	advertises: set Topic,
	inbox : Message->Time, 
	outbox : Message->Time
	}
//Node that mimics the logical negation Behaviour.
sig Node_Not extends Node{}
//Sensor Behaviour. 	
one sig Producer extends Node{}{						
	subscribes = none
	}
-- Actuator Behaviour.
one sig Consumer extends Node{}{						
	advertises = none
	}
-- In this model, the distinct Topics and distinct message types are not considered
sig Topic {} 
-- Each Message is associated to a given topic, and has some given value
sig Message {	
	topic : one Topic,
	//either "One" or "Zero"	
	value : one  Value
}

abstract sig Value {}
one sig One, Zero extends Value{}

/*
These describe the architecture structure, which in this particular case, will represent 
            a set of nodes organized in a linear form.
            i.e : Producer -> Node -> Node -> Node -> Node -> ... -> Consumer 
*/
fact Linear_Structure {
	Node = Node_Not + Producer + Consumer
	 -- The only Node that doesn't publishes, is the last one.
	all n: Node | 
		(n.advertises = none) implies (n in Consumer)
	-- The only Node that doesn't subscribes any topic, is the first one.
	all n:Node| 						
		(n.subscribes = none) implies (n in Producer)
	-- Each Node only subscribes and advertises, at most, one topic.
	all n:Node | 						
		(lone n.subscribes) and (lone n.advertises) and (n.advertises != n.subscribes) 
	subscribes.~subscribes in id[Node]		-- 'subscribes' is injective.
	advertises.~advertises in id[Node] 		-- 'advertises' is injective.
	Topic in (Node.subscribes & Node.advertises)	-- Each topic will be used.
	no id[Node] & ^(subscribes.~advertises)	-- There are no cycles 
	}
--- Aux Function, id definition.
fun id[S: univ] : univ -> univ {		
	(S -> S) & iden
	}

fact Messages {
	all n : Node, t : Time |		
		(n.inbox.t.topic in n.subscribes and n.outbox.t.topic in n.advertises)

	all m : Message, t: Time-last | some t': Time| {
 		t' in t.nexts 

		m in Node.outbox.t implies 
				(all n : subscribes.(m.topic) |   m in n.inbox.t') 	
		}

	all t: Time-last| some t': Time | let m = Node.outbox.t{
			 t' in t.nexts and 
			 (m not in Node.outbox.t')
			}

	all m : Message, t: Time-first| some t': Time |{
		t' in t.prevs 
	
		m in Node.inbox.t implies 
			(some n : advertises.(m.topic)| m in n.outbox.t') 
		}
	}

/*On the initial states, there are no messages, both in inbox as outbox.*/
fact init {
	no (outbox.first + inbox.first)
	}

fact Producer_As_Sensor{									-- The Sensor only produces Zero values	
	all t: Time-last| some t': Time | {
			t' in t.nexts and 
			some Producer.outbox.t'}
	}

fact Producer_Constraints {		
	-- In this particular case, the Sensor will only produce values equals to Zero							-- In this particular case, the Sensor will only produce values equals to Zero
	all t: Time| let  m= Producer.outbox.t | m.value = Zero	
	}

fact Node_Not_Behaviour{									-- The Node_Not will always have the same 'Safety' behaviour (logical NOT function).
	
		all n: Node_Not, t: Time-first | some t': Time{
			t' in t.prevs 
			(some m1: n.outbox.t | m1.value in Zero)
				implies  (some m0: n.inbox.t' | m0.value in One)
		}
		
		all n: Node_Not,t : Time-first| some t': Time {
			t' in t.prevs
			(some m1: n.outbox.t | m1.value in One)
				implies  (some m0: n.inbox.t' | m0.value in Zero)
		}	
}

-- check properties:
check property {
	all t: Time|
		some Consumer.inbox.t 
			implies (all m: Consumer.inbox.t | m.value in One)

} for 3 but exactly 1 Zero, exactly 1 One, exactly 1 Producer, exactly 1 Consumer, exactly 3 Node_Not, exactly 4 Topic,  exactly 4 Message, exactly 10 Time	

