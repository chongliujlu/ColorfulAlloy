module chapter6/ringElection2 --- the final version (as depicted in Fig 6.1)
open util/ordering[Time] as TO
open util/ordering[Process] as PO
sig Time {}
sig Process {
	succ: Process,
	toSend: Process -> Time,
	elected: set Time
	}


pred step [t, t': Time, p: Process] {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
		}
	}




assert AtMostOneElected { lone elected.Time }


check AtMostOneElected for 3 Process, 7 Time--
--check AtLeastOneElected with ➀ for 3 Process, 7 Time--


