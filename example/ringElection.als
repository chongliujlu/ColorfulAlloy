module chapter6/ringElection
/**
*from chapter 6
* ➀ static topology
* ➁ dynamic topoplogy
*/
open util/ordering[Time] 
open util/ordering[Process] 

sig Time {}

fact FM{
	//The topology is either static(➀) or dynamic(➁)
	➀➁some none➁➀
	➊➋some none➋➊
}
sig Process {
	// each process has exactly one successor
	➀succ: Process➀,
	//Ring topology is dynamic
	➁succDyn: Process one->Time➁,
	
	toSend: Process -> Time,
	elected: set Time
	}

//The processes are form a ring
fact ring {
	➀all p: Process | Process in p.^succ➀
	➁all t: Time, p: Process | Process in p.^(succDyn.t)➁
	}

//Each process is ready to send only its own identifier
pred init [t: Time] {
	all p: Process | p.toSend.t = p
	}

pred step [t, t': Time, p: Process] {
	➀let from = p.toSend, to = p.succ.toSend| 
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
		}➀
	
	➁ let from = p.toSend | let to = (p.succDyn.t).toSend|
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - (p.succDyn.t).prevs)
		}➁


	}

fact defineElected {
	no elected.first
	all t: Time-first | elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.prev)}
	}

fact traces {
	init [first]
	all t: Time-last |
		let t' = t.next |
			all p: Process |
				step [t, t', p] or
				 ➀step [t, t', succ.p]➀ or 
					skip [t, t', p] or 
				➁step[t,t',(succDyn.t).p]➁
	}

pred skip [t, t': Time, p: Process] {
	p.toSend.t = p.toSend.t'
	}

//whenever some process has a nonempty identifier pool, some process  must make a move.
pred progress {
	all t: Time - last |
		some Process.toSend.t =>
		some p: Process | not skip [t, t.next, p]
	}




assert AtMostOneElected { 
	lone elected.Time 
	}
check AtMostOneElected with exactly ➀for 3 Process, 7 Time
check AtMostOneElected with ➀,➋for 3 Process, 7 Time 

check AtMostOneElected with exactly ➁for 3 Process, 7 Time--?
check AtMostOneElected with ➊,➁for 3 Process, 7 Time--?


assert AtLeastOneElected { 
	progress => some elected.Time 
	}
check AtLeastOneElected with exactly ➀  for  3 Process, 7 Time
check AtLeastOneElected with ➀,➋for 3 Process, 7 Time

check AtLeastOneElected with exactly ➁  for  3 Process, 7 Time--?
check AtLeastOneElected with  ➊,➁  for  3 Process, 7 Time--?


check AtLeastOneElected for 3 but  7 Time

pred show { some elected }
run show with exactly ➀ for 3 Process, 4 Time
