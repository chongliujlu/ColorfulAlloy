//with no feature
module lift
open util/ordering[Time]

abstract sig Direction{}
one sig Down,Up extends Direction{}
abstract sig DoorState{}
one sig Open,Close extends DoorState{}

sig Time{
	currentDirection : one Direction,
	currentFloor: one Int,
	door: one DoorState,
	landingCall: set Int,
	pressedButton: set Int
	}
abstract sig Event{
	pre,post: Time
	}
abstract sig  liftTravelEvent extends Event{}

sig openDoor extends liftTravelEvent{}{
	pre.currentFloor in pre.(landingCall+pressedButton)
	pre.door=Close
	post.currentFloor =pre.currentFloor
	post.door=Open
	post.landingCall=pre.landingCall-pre.currentFloor
	post.pressedButton=pre.pressedButton-pre.currentFloor
	//0层或5层换向
	(pre.currentDirection=Up && lt[pre.currentFloor,max[pre.(landingCall+pressedButton)]])implies 
				post.currentDirection=Down 
		else( (pre.currentDirection=Down && gt[pre.currentFloor,min[pre.(landingCall+pressedButton)]]) implies
				post.currentDirection=Up 
			 else post.currentDirection=pre.currentDirection )

	
	}
sig closedDoor extends liftTravelEvent{}{
	pre.door=Open
	post.door=Close
	post.currentFloor=pre.currentFloor
	post.landingCall=pre.landingCall
	post.pressedButton=pre.pressedButton
	}

sig travelup extends liftTravelEvent{}{
	pre.door=Close
	gte[pre.currentFloor,max[pre.landingCall+pre.pressedButton]]
	pre.currentFloor in pre.(landingCall+pressedButton)
	post.currentFloor =pre.currentFloor
	post.door=Open
	post.landingCall=pre.landingCall-pre.currentFloor
	post.pressedButton=pre.pressedButton-pre.currentFloor
	}
sig travelDown extends liftTravelEvent{}{
	pre.door=Close
	lte[pre.currentFloor,max[pre.landingCall+pre.pressedButton]]
	pre.currentFloor in pre.(landingCall+pressedButton)
	post.currentFloor =pre.currentFloor
	post.door=Open
	post.landingCall=pre.landingCall-pre.currentFloor
	post.pressedButton=pre.pressedButton-pre.currentFloor
	}
abstract sig ButtonEvent extends Event{}
sig landingCall extends Event{}{
	post.door=pre.door
	post.currentFloor=pre.currentFloor
	post.landingCall=pre.landingCall+ Int
	}
fact{
	gte[0,Time.currentFloor]
	gte[0,min[Time.landingCall]]
	gte[0,min[Time.pressedButton]]
	}
pred init{
	first.currentDirection=Up
	first.currentFloor=0
	first.door=Open
	some first.landingCall
	no first.pressedButton
}
fact trace{
	init
	all t:Time-last| let t'=t.next|
	some e:Event{
		e.pre=t
		e.post=t'
		e in (ButtonEvent+liftTravelEvent)
}
}
run {} for 4 but exactly 5 Time , 4 Int
