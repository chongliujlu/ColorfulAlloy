module ROSArchitecturev2
open util/ordering[Time]
sig Time{}

abstract sig Topic {}	
one sig negation_topic, sensor_data extends Topic{} 

/* Each node subscribes and advertises some set of Topics */
/* Each node has an inbox and outbox,  respectively representing the messages that will be processed,
    and the ones that already had been. */
abstract sig Node {	
	subscribes: set Topic,
	advertises: set Topic,
	inbox :  Message -> Time,
	outbox : Message->Time
	}
/*
	In this model, there are 3 distinct type of Nodes.
	The Node_Not, is a simple node, whose behaviour will mimic the logical negation operation
	The Sensor Node will not subscribe any topic, and will behave like a robotic sensor.
	The Actuator  will act as a robotic actuator. Its behaviour is limited to the message consumption.
*/
one sig Node_Not extends Node{}{
	advertises = negation_topic
	subscribes = sensor_data
	}									
one sig Sensor extends Node{}{						
	advertises = sensor_data
	subscribes = none
	}
one sig Actuator extends Node{}{					
	advertises = none
	subscribes = negation_topic
	}

/*On the initial states, there are no messages, both in inbox as outbox.*/
fact init {
	no (outbox.first + inbox.first)
	}
fact Messages {
	all n : Node, t : Time |		
		(n.inbox.t.topic in n.subscribes and n.outbox.t.topic in n.advertises)

	all m : Message, t: Time | 
		m in Node.outbox.t implies 
			(all n : subscribes.(m.topic) , t' :Time|  t' in t.nexts and  m in n.inbox.t') 
		

	all t: Time-last| some t': Time | let m = Node.outbox.t{
			 t' in t.nexts and 
			 (m not in Node.outbox.t')
			}

	all m : Message, t: Time | 	
		m in Node.inbox.t implies 
			(some n : advertises.(m.topic), t': Time | t' in t.prevs and m in n.outbox.t') 
			
}

fact Sensor_Behaviour{									
	all t: Time-last| some t': Time | (t' in t.nexts and 
			some Sensor.outbox.t')
}

sig Message {								
	topic : one Topic,
	//either "1" or "0"	
	value : one  Value
	}
abstract sig Value {}								
one sig One, Zero extends Value{}

/*The Node_Not will always have the same 'Safety' behaviour (logical NOT function).*/
fact Node_Not_Behaviour{						
	all t: Time-first, n: Node_Not| some t': Time|{
			t' in t.prevs and

		((some m1: n.outbox.t | m1.value in Zero)
				implies (some m0: n.inbox.t' | m0.value in One))
			
			(some m1: n.outbox.t | m1.value in One)
				implies (some m0: n.inbox.t' | m0.value in Zero)
		}	
	}
//gives counterexample, not right
check safety_property{
	all t:Time| some t':Time{
		t' in t.prevs and
		((some m1: Actuator.inbox.t | m1.value in Zero)
			implies  (some m0: Sensor.outbox.t' | m0.value in One))
	}
} for 4 but 10 Time

/* 
Middle node can not transmit message between sensor and Actuator because of the field "topic"
	( message flow: Sensor.outbox-> Node_Not inbox)
     Field "advertises" and "advertises" are not var, so
     	Sensor node only generates message with "sensor_data" topic( and put in its outbox).
     	Middle node will  public messages with "negation_topic" and subscribes messages with "sensor_data" 
   So no meaage for Middle to publish since the topic of a message can not change
	mabe change  to var type?
*/
