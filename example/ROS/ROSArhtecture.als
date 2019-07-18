module ROSArchitectureV3
open util/ordering [Time]

sig Time{}

abstract sig Topic {}	
one sig negation_topic, sensor_data extends Topic{} 

abstract sig Node {	
	subscribes: set Topic,
	advertises: set Topic,
	inbox :  Message -> Time,
	outbox : Message ->Time
	}
//The Node_Not, is a simple node, whose behaviour will mimic the logical negation operation
one sig Node_Not extends Node{}{
	advertises = negation_topic
	subscribes = sensor_data
	}	
// The Sensor Node will not subscribe any topic, and will behave like a robotic sensor.								
one sig Sensor extends Node{}{						
	advertises = sensor_data
	subscribes = none
	}
//The Actuator  will act as a robotic actuator. Its behaviour is limited to the message consumption.
one sig Actuator extends Node{}{					
	advertises = none
	subscribes = negation_topic
	}

//Each Message is associated to a static given topic, and has some static given value
sig Message {									
	topic : one Topic,
	// either "1" or "0"	
	value : one  Value
	}
abstract sig Value {}								
one sig One, Zero extends Value{}

fact Messages {

	all n : Node, t : Time |		
		(n.inbox.t.topic in n.subscribes and n.outbox.t.topic in n.advertises)

	all m : Message, t: Time-last |some t':t.nexts| {
		m in Node.outbox.t implies 
			(all n : subscribes.(m.topic) | m in n.inbox.t') 
		}

	all t: Time-last| some t': t.nexts| let m = Node.outbox.t{ 
			 (m not in Node.outbox.t')
			}
	//message in inbox => message with this topic in some node's outbox 
	all m : Message, t: Time-first| some t': t.prevs | 	
		m in Node.inbox.t implies 
			(some n : advertises.(m.topic) | m in n.outbox.t') 
	}


//On the initial states, there are no messages, both in inbox as outbox.
fact init {
	no inbox. first
	no Node_Not.outbox.first
	no Actuator. outbox.first
	//no Sensor.outbox.first
	//no (outbox + inbox).first
	}

fact Sensor_Behaviour{									
	all t: Time-last| some t': t.nexts| 
			some Sensor.outbox.t'
	}
// The Node_Not will always have the same 'Safety' behaviour (logical NOT function).
fact Node_Not_Behaviour{
	all t: Time-first | some t':t.prevs{ 
		(some m1: Node_Not.outbox.t & topic.negation_topic | m1.value in Zero)
				implies (some m0: Node_Not.inbox.t' & topic.sensor_data | m0.value in One)

		(some m1: Node_Not.outbox.t & topic.negation_topic | m1.value in One)
				implies(some m0: Node_Not.inbox.t' & topic.sensor_data | m0.value in Zero)
	}		
}

//run {some Sensor. outbox} for 4 
//run { some t:Time-first| some Actuator.inbox.t} for 3 but exactly 4 Time
run { some t:Time-first| some Actuator.inbox.t} for 3 but exactly 20 Time

check safety_property{
	all t: Time-first|  some t' : t.prevs| { 
		(some m1: Actuator.inbox.t & topic.negation_topic | m1.value in Zero)
			implies (some m0: Sensor.outbox.t' & topic.sensor_data | m0.value in One)
		}
	} for 4 but 10 Time


