module phone
/**
* fom FeatureAlloy (from paper "Detecting Dependences and Interactions in Feature-Oriented Design")
* ➀CallForwarding
* ➁Callwaiting
*/
sig Phone {
	currentState: one State,
	currentCall: lone Call,
	➀forward: lone Phone➀,
	➁waitingCall: set Call➁
	} 

sig Call {} 

abstract sig State {}
one sig Idle extends State {} 
one sig Busy extends State {} 
// exist in feature "Callwaiting"
➁one sig Suspended extends State{} ➁

fact noEmptyCalls {
	no call: Call | call not in Phone.(currentCall+➁waitingCall➁)
	}
➀fact noSelfForward{
	no phone: Phone | phone in phone.forward
}➀
fact states {
	all phone: Phone | phone.currentState = Idle => no phone.currentCall && 
							 ➀no phone.forward➀ &&
							 ➁no phone.waitingCall➁
	all phone: Phone | phone.currentState = Busy => one phone.currentCall 
	
	➁all phone: Phone | phone.currentState = Suspended => 
						one phone.currentCall && some phone.waitingCall ➁

	➁no(Phone.currentCall & Phone.waitingCall)➁
	}

pred incomingCall [inCall: Call, disj phone, phone': Phone] {
	phone.currentState=Busy

	phone.currentState=Idle implies phone'.currentState=Busy &&
		 		    	   phone'.currentCall =inCall &&
					   ➀no phone'.forward ➀ &&
					   ➁no phone.waitingCall && no phone'.waitingCall➁ &&
					    no phone'' : Phone | phone'' not in (phone +phone')

	phone.currentState=Busy implies phone.currentCall != inCall && 
					    phone'.currentCall =phone.currentCall &&
					    ➀no phone. forward➀  &&
					    (➀ one phone'': Phone| phone'' not in (phone+phone') && 
								    phone''.currentCall=inCall && 
								    phone''.currentState=Busy && 
							               no phone''.forward &&  
								     phone'.currentState=Busy &&
							               phone'.forward=phone'' && ➁phone'.waitingCall=phone.waitingCall + inCall➁ &&
							               (no phone''': Phone| phone'''! in (phone+phone'+phone''))➀
						 or ➁(inCall not in phone.waitingCall && phone'.waitingCall=(phone.waitingCall+inCall) &&  phone'.currentState=Suspended &&
							 ➀no phone'.forward➀&& (no phone'' : Phone | phone'' not in (phone +phone')) )➁
					     )
					  
	➁phone.currentState = Suspended => phone'.currentState = Suspended && 
						phone'.currentCall = phone.currentCall  && 
						phone'.currentCall != inCall &&
						inCall not in phone.waitingCall &&
						phone'.waitingCall = phone.waitingCall + inCall &&
						➀no phone.forward && no phone'.forward➀&&
						no phone'' : Phone | phone'' not in (phone +phone')➁
	}

➀assert isForwarded{
	all disj phone, phone':Phone | all inCall:Call |
		 incomingCall [inCall,phone,phone'] implies( (phone.currentState=Idle iff no phone'.forward)&& 
							         (phone.currentState=Busy iff one phone'.forward))
	}➀



➁assert isSuspended{
	all disj phone,phone':Phone|  all inCall: Call | 
		(incomingCall [inCall,phone,phone']) implies ((phone.currentState=Idle iff no phone'.waitingCall) && 
								(phone.currentState=Busy iff some phone'.waitingCall) &&
								(phone.currentState= Suspended implies (some phone.waitingCall && 
													some phone'.waitingCall)))
	}➁



run incomingCall for 5 
run incomingCall with exactly ➊,➋ for 3
run incomingCall with ➊,➋ for 3 
run incomingCall with exactly ➀ for 3
run incomingCall with ➀,➋ for 3 
run incomingCall with exactly ➁ for 3
run incomingCall with ➊,➁ for 3  
run incomingCall with exactly ➀,➁ for 3 
run incomingCall with ➀,➁ for 3 

check isSuspended with exactly ➁ for 3
check isSuspended with exactly ➀,➁ for 3
check isForwarded with exactly➀ for 3 
//This should give an counterexample(state Suspended)
check isForwarded with exactly➀,➁ for 3  
