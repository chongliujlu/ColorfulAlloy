module WashingMachine
/**
* From paper "Software Product Lines with Design Choices: Reasoning about Variability and Design Uncertainty"

* ➀ Heat: supports heating water in case there access only to the cold water supply(heated to 30 degree ).
* ➁ Delay: allows setting a future time to start wash.
* ➂ Dry: adds the function of a dryer.
*
*
*                                                 ➀ heat()➀ or ➁wait()➁
*                                                             _____
*                                                            |      |
*                                 lockdoor()            /    \|/                
*                  Free————————————> Ready  
*                 /|\ /|\                                        |
*                   |    \         unlock()                    |  wash()
                    |      \_______________________     \|/
*  lockdoor()  |                                        Washing
**                 |    unlock()                              |
*                  |———————Drying<—————-
*                                                     ➂dry()➂
*/
open util/ordering [Time]
fact FM {
	//Heat and Delay are not competible
	➀➁some none➁➀
}
sig Time{}

one sig WashingMachine{
	currentState: State one -> Time,
	//locking or unlocking
	doorState:  Door one ->Time,
	// temperature of water
	➀temp:  Int one->Time➀,
	//The Timer is On or Off
	➁timer: Int one-> Time➁,
	➂drier:  Switch one->Time➂
	}

abstract sig Door {}
one sig Unlocking, Locking extends Door{}

abstract sig  Switch{}
one sig On, Off extends Switch{} 

abstract sig State {}
one sig Free, Ready, Washing extends State{}
➂one sig Drying extends State{}➂


pred lockdoor [w:WashingMachine,t,t':Time]{
	w.currentState.t=Free
	w.currentState.t'=Ready
// lock door
	w.doorState.t=Unlocking
	w.doorState.t'=Locking

	➀w.temp.t'=w.temp.t➀
	➁w.timer.t=w.timer.t'➁
	➂w.drier.t'=w.drier.t➂
	}

➀pred heat [w:WashingMachine,t,t':Time]{
	w.currentState.t=Ready 
	w.currentState.t'=Ready

	w.doorState.t=w.doorState.t'
	//heated to 30 degree
	lt[w.temp.t,30] 
	 w.temp.t'=30

	➁w.timer.t'=w.timer.t➁
	➂w.drier.t'=w.drier.t➂
	}➀

➁pred wait [w:WashingMachine,t,t':Time]{
	w.currentState.t=Ready 
	w.currentState.t'=Ready

	w.doorState.t'=w.doorState.t
	➀w.temp.t'=w.temp.t➀
	//timer-1
	gt[w.timer.t, 0]
	w.timer.t'=minus[w.timer.t, 1]	

	➂w.drier.t'=w.drier.t➂
	}➁

pred wash [w:WashingMachine,t,t':Time]{
	//move to state "Washing"
	w.currentState.t = Ready
	w.currentState.t'=Washing

	w.doorState.t'=w.doorState.t
	➀w.temp.t'=w.temp.t➀
	➁w.timer.t=0➁
	➁w.timer.t'=w.timer.t➁
	➂w.drier.t'=w.drier.t➂
	}

➂pred dry [w:WashingMachine,t,t':Time]{
	w.currentState.t=Washing
	w.currentState.t'=Drying

	w.doorState.t'=w.doorState.t
	➀w.temp.t'=w.temp.t➀	
	➁w.timer.t'=w.timer.t➁
	//drier start working
	w.drier.t=Off
	w.drier.t'=On
	}➂

pred unlock [w:WashingMachine,t,t':Time]{
	w.currentState.t in Washing+➂Drying➂
	w.currentState.t'=Free
	//unlock door
	w.doorState.t=Locking
	w.doorState.t'=Unlocking
	➀w.temp.t'=w.temp.t➀
	➁w.timer.t'=w.timer.t➁
	
	//driver stop working
	➂w.drier.t=On➂
	➂w.drier.t'=Off➂	
	}

pred init{
	WashingMachine.currentState.first=Free
	WashingMachine.doorState.first=Unlocking
	➂WashingMachine.drier.first=Off➂
	}



//temperature of water is between 1 to 40 
fact {
   all t: Time|{
	➀gte[WashingMachine.temp.t,0]➀
	➀lte[WashingMachine.temp.t,40]➀
	➁gte[WashingMachine.timer.t, 0]➁
		}
	}

fact Trace {
	all t: Time-last| let t'=t.next| one w: WashingMachine{ 
	init  
	lockdoor[w,t,t'] or wash[w,t,t'] or
	 ➁ wait[w,t,t']➁ or➀ heat[w,t,t']➀ or
	➂ dry[w,t,t']➂ or unlock[w,t,t'] 
		}	
	}

run {} with exactly ➊,➋,➌ for 4  but 1 WashingMachine
run {} with  ➊,➋,➌ for 4  but 1 WashingMachine,3 Time
run {} with exactly ➀,➋,➌ for 3 but 1 WashingMachine, 5 Time, 7 Int
run {} with  ➀,➋,➌ for 3 but 1 WashingMachine, 5 Time, 7 Int

run {} with exactly ➊,➁,➌ for 4  but 1 WashingMachine , 5 Time,2 Int
run {} with  ➊,➁,➌ for 4  but 1 WashingMachine

run {} with exactly ➊,➋,➂ for 4  but 1 WashingMachine, 5 Time
run {} with exactly ➀,➋,➂ for 4  but 1 WashingMachine, 6 Time, 7 Int
run {} with exactly ➊,➁,➂ for 4  but 1 WashingMachine, 6 Time

 assert washingState{
	all t: Time, w: WashingMachine| let t'=t.next| 
	wash[w, t,t'] implies 
	w.doorState.t'=Locking and ➂w.drier.t'=Off➂ and ➁w.timer.t'=0➁
}

check washingState  for 10 but 6 Int, 20 Time,1 WashingMachine
check washingState  with exactly  ➀ for 10 but  7 Int, 20 Time,1 WashingMachine
check washingState  with exactly  ➁ for 10 but  7 Int, 20 Time,1 WashingMachine
check washingState  with exactly  ➂ for 10 but 7 Int, 20 Time,1 WashingMachine
check washingState  with exactly  ➀,➂ for 10 but  7 Int, 20 Time,1 WashingMachine
check washingState  with exactly  ➁,➂ for 10 but 7 Int, 20 Time,2 WashingMachine

➁assert timer{
	all t:Time,w: WashingMachine| gt[w.timer.t,0] implies w.currentState.t in Free+Ready
}➁

check timer with ➁ for 3 
