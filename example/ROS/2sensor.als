/**
  ➀: add a sensor node to the map
*/
module ROSArchitecturev3
open util/ordering [Time]
sig Time{}

abstract sig Topic {}	
one sig negation_l, sensor_data_l extends Topic{} 
➀one sig sensor_data_v extends Topic{}➀
➀one sig negation_v extends Topic{}➀

abstract sig Node {	
	subscribes: set Topic,
	advertises: set Topic,
	inbox :  Message -> Time,
	outbox : Message ->Time
	}
//The Node_Not, is a simple node, whose behaviour will mimic the logical negation operation
one sig Node_Not extends Node{}{
	advertises = negation_l+➀negation_v➀
	subscribes = sensor_data_l+➀sensor_data_v➀
	}	
// The Sensor Node will not subscribe any topic, and will behave like a robotic sensor.								
abstract sig Sensor extends Node{}{						
	subscribes = none
	}
one sig Sensor_L extends Sensor{}{
	advertises = sensor_data_l
	}
➀one sig Sensor_V extends Sensor{}{
	➀advertises = sensor_data_v➀
	}➀
//The Actuator  will act as a robotic actuator. Its behaviour is limited to the message consumption.
one sig Actuator extends Node{}{					
	advertises = none
	subscribes = negation_l+➀negation_v➀
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

	all t: Time-last| some t': t.nexts| all m : Node.outbox.t{ 
			 (m not in Node.outbox.t')
			}

	all m : Message, t: Time-first| some t': t.prevs | 	
		m in Node.inbox.t implies 
			(some n : advertises.(m.topic) | m in n.outbox.t') 
	}


//On the initial states, there are no messages, both in inbox as outbox.
fact init {
	no (inbox+outbox). first
	}

fact Sensor_Behaviour{									
	all t: Time-last| some t': t.nexts| 
			some Sensor.outbox.t'
	}
// The Node_Not will always have the same 'Safety' behaviour (logical NOT function).
fact Node_Not_Behaviour{
	all t: Time-first | some t':t.prevs{ 
		(some m1: Node_Not.outbox.t & topic.negation_l | m1.value in Zero)
				implies (some m0: Node_Not.inbox.t' & topic.(sensor_data_l) | m0.value in One)
		➀(some m1: Node_Not.outbox.t & topic.negation_v | m1.value in Zero)
				implies (some m0: Node_Not.inbox.t' & topic.(sensor_data_v) | m0.value in One)➀

		(some m1: Node_Not.outbox.t & topic.negation_l | m1.value in One)
				implies(some m0: Node_Not.inbox.t' & topic.sensor_data_l | m0.value in Zero)
	➀(some m1: Node_Not.outbox.t & topic.negation_v | m1.value in One)
				implies(some m0: Node_Not.inbox.t' & topic.sensor_data_v | m0.value in Zero)➀
	}		
}


run { some t:Time-first| some Actuator.inbox.t} for 3 but exactly 5 Time
run { some t:Time-first| some Actuator.inbox.t} with exactly ➀ for 3 but exactly 5 Time




