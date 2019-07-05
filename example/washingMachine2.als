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
sig Time{
	currentState: State ,
	//locking or unlocking
	doorState: one Door ,
	// temperature of water
	➀temp:  one Int ➀,
	//The Timer is On or Off
	➁timer: one Int➁,
	➂drier:  one Switch ➂
}

abstract sig Door {}
one sig Unlocking, Locking extends Door{}

abstract sig  Switch{}
one sig On, Off extends Switch{} 

abstract sig State {}
one sig Free, Ready, Washing extends State{}
➂one sig Drying extends State{}➂


pred lockdoor [t,t':Time]{
	t.currentState=Free
	t'.currentState=Ready

	t.doorState=Unlocking
	t'.doorState=Locking

	➀t'.temp=t.temp➀
	➁t'.timer=t.timer➁
	➂t'.drier=t.drier➂
	}

➀pred heat [t,t':Time]{
	t.currentState=Ready 
	t'.currentState=Ready

	t'.doorState=t.doorState

	lt[t.temp,30] 
	 t'.temp=30
	➁t'.timer=t.timer➁
	➂t'.drier=t.drier➂
	}➀

➁pred wait [t,t':Time]{
	t.currentState =Ready 
	t'.currentState=Ready

	t'.doorState=t.doorState

	➀t'.temp=t.temp➀

	gt[t.timer, 0]

	t'.timer=minus[t.timer, 1]	

	➂t'.drier=t.drier➂
	}➁

pred wash [t,t':Time]{
	t.currentState = Ready
	t'.currentState=Washing

	t'.doorState=t.doorState

	➀t'.temp=t.temp➀

	➁t.timer=0➁
	➁t'.timer=t.timer➁

	➂t'.drier=t.drier➂
	}

➂pred dry [t,t':Time]{
	t.currentState=Washing
	t'.currentState=Drying
	t'.doorState=t.doorState
	➀t'.temp=t.temp➀	
	➁t'.timer=t.timer➁
	t.drier=Off
	t'.drier=On
	}➂

pred unlock [t,t':Time]{
	t.currentState in Washing+➂Drying➂
	t'.currentState=Free

	t.doorState=Locking
	t'.doorState=Unlocking
	➀t'.temp=t.temp➀

	➁t'.timer=t.timer➁
	
	➂t.drier=On➂
	➂t'.drier=Off➂	
	}

pred init{
	first.currentState=Free
	first.doorState=Unlocking

	➂first. drier=Off➂
	}

//temperature of water is between 1 to 40 
fact {
   all t: Time|{
	➀gte[t.temp,0]➀
	➀lte[t.temp,40]➀
	➁gte[t.timer, 0]➁
		}
	}

fact Trace {
	all t: Time-last| let t'=t.next|{
	init  
	lockdoor[t,t'] or wash[t,t'] or
	 ➁ wait[t,t']➁ or➀ heat[t,t']➀ or
	➂ dry[t,t']➂ or unlock[t,t'] 
		}	
	}

run {} with exactly ➊,➋,➌ for 4  but 5 Time
run {} with  ➊,➋,➌ for 4  but 2 Time
run {} with exactly ➀,➋,➌ for 4  but 3 Time, 7 Int
run {} with  ➀,➋,➌ for 3 but  5 Time, 7 Int

run {} with exactly ➊,➁,➌ for 4  but  5 Time,2 Int
run {} with  ➊,➁,➌ for 4  but 5 Time

run {} with exactly ➊,➋,➂ for 4  but 5 Time
run {} with exactly ➀,➋,➂ for 4  but  6 Time, 6 Int
run {} with exactly ➊,➁,➂ for 4  but  6 Time

 assert washingState{
	all t: Time| let t'=t.next| 
	wash[t,t'] implies 
	t'.doorState=Locking and ➂t'.drier=Off➂ and ➁t'.timer=0➁
}

check washingState  for 10 but 6 Int, 20 Time
check washingState  with exactly  ➀ for 10 but  7 Int, 20 Time
check washingState  with exactly  ➁ for 10 but  7 Int, 20 Time
check washingState  with exactly  ➂ for 10 but 7 Int, 20 Time
check washingState  with exactly  ➀,➂ for 10 but  7 Int, 20 Time
check washingState  with exactly  ➁,➂ for 10 but 7 Int, 20 Time

➁assert timer{
	all t:Time| gt[t.timer,0] implies t.currentState in Free+Ready
}➁

check timer with ➁ for 3 
