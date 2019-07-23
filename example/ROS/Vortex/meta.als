module meta
open util/ordering[Time]
sig Time{}

abstract sig Node {
	subscribes: set Topic,
	advertises: set Topic,
	inbox: Message ->Time,
	outbox: Message->Time
}

abstract sig Topic {}

fact Node_Liveness{ 
--	all n: Node | (some n.advertises) implies always (some n.inbox implies eventually some n.outbox)
}

sig Message {
	topic : one Topic,	
	value : one  Value
}

abstract sig Value {}

fact Messages {
	all n : Node, t : Time | 	{	
		n.inbox.t.topic in n.subscribes
		n.outbox.t.topic in n.advertises}
	

	all m : Message, t: Time-last | some t': t.nexts|{ 
		m in Node.outbox.t implies (all n : subscribes.(m.topic) |  m in n.inbox.t')
	}
					
	all t: Time-last| all m : Node.outbox.t | some t':  t.nexts |
				 {m not in Node.outbox.t'}
	all m : Message, t: Time-first |some t': t.prevs|{ 	
		m in Node.inbox.t implies (some n : advertises.(m.topic) | m in n.outbox.t') 
	}	
}


fact init {
	no (outbox + inbox).first
}


abstract sig Sensor extends Node {}{
	subscribes = none
}

abstract sig Actuator extends Node{}{
	advertises = none
}

fact Sensor_Behaviour {
		all s:Sensor,t: Time-last| some t': t.nexts | { some s.outbox.t'
	}
}
fun channel : Node -> Topic -> Node {
	{a : Node, t : Topic, b : Node | a->t in advertises and b->t in subscribes}
}
