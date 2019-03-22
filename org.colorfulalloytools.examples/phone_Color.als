--CallForwarding➀   Callwaiting➁
sig Phone {
	currentState: one State,
	currentCall: lone Call,
	➀forward: lone Phone➀,
	➁waitingCall: set Call➁
} 

fact noEmptyCalls {
	➁no call: Call | call not in Phone.(currentCall+waitingCall)➁
}

sig Call {} 

abstract sig State {}
one sig Idle extends State {} 
one sig Busy extends State {} 
-- Callwaiting➁
➁one sig Suspended extends State{} ➁

fact states {
	all phone: Phone | phone.currentState = Idle => no phone.currentCall && 
							 ➀no phone.forward➀ &&
							 ➁no phone.waitingCall➁
	all phone: Phone | phone.currentState = Busy => one phone.currentCall 
	
	➁all phone: Phone | phone.currentState = Suspended => one phone.currentCall && some phone.waitingCall ➁

	➁no(Phone.currentCall & Phone.waitingCall)➁
}



pred incomingCall [inCall: Call, disj phone, phone': Phone] {
	phone.currentState=Idle implies phone'.currentState=Busy &&
		 		    	   phone'.currentCall =inCall &&
					   ➀no phone'.forward ➀ &&
					     
					   ➁no phone.waitingCall➁	&&
 					   (no phone'' : Phone | phone''!=phone &&phone''!=phone') 		
		

	phone.currentState=Busy implies phone.currentCall != inCall && 
					phone'.currentState in (➀Busy➀ +➁Suspended➁) &&
					    phone'.currentCall =phone.currentCall &&
					    ➀no phone. forward➀ &&
					    ➀ (one phone'': Phone| phone''! =phone &&  --Callforward
							               phone''!=phone'&& --Callforward
							               phone''.currentState=Busy && --Callforward
							               phone''.currentCall=inCall && --Callforward
							               no phone''.forward &&  --Callforward
							               phone'.forward=phone'' && --Callforward
							               (no phone''': Phone| phone'''! =phone&& --Callforward
									                      phone'''!=phone'&& --Callforward
									                      phone'''!=phone''))➀ && --callforward
					   ➊(no phone'' : Phone | phone''!=phone &&phone''!=phone')➊ &&
					   ➁phone'.waitingCall=inCall➁ &&
					   ➁no phone.waitingCall➁

	➁	phone.currentState = Suspended => 	phone'.currentState = Suspended && 
						phone'.currentCall = phone.currentCall  && 
						phone'.currentCall != inCall &&
						inCall not in phone.waitingCall &&
						phone'.waitingCall = phone.waitingCall + inCall &&
						(no phone'' : Phone | phone''!=phone &&phone''!=phone')➁

}

assert isForwarded{
	➀all disj phone, phone':Phone | all inCall:Call |
		 incomingCall [inCall,phone,phone'] implies( (phone.currentState=Idle iff no phone'.forward)&& 
							         (phone.currentState=Busy iff one phone'.forward))➀
}



assert isSuspended{
	➁all disj phone,phone':Phone|  all inCall: Call | 
		(incomingCall [inCall,phone,phone']) implies ((phone.currentState=Idle iff no phone'.waitingCall) && 
								(phone.currentState=Busy iff one phone'.waitingCall) &&
								(phone.currentState= Suspended iff (some phone.waitingCall && 
													some phone'.waitingCall)))➁
}



run incomingCall for 5 -- amalgamate method:  all 
run incomingCall with exactly ➀ for 3 -- exatly method : only with CallForward 
run incomingCall with exactly ➁ for 3 -- exatly method : only with Callwaiting
run incomingCall with exactly ➀,➁ for 3 -- exatly method : CallForwarding and Callwaiting  
run incomingCall with ➁ for 5 -- exatly method : only with Callwaiting 
check isSuspended for 3
check isForwarded with exactly➀ for 3 --exactly method: only with CallForward 
