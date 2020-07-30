module chapter6/ringElection2 --- the final version (as depicted in Fig 6.1)
➀open util/ordering[Time] as TO➀
➀open util/ordering[Process] as PO➀
➀sig Time {}➀
➀sig Process {
	succ: Process,
	toSend: Process -> Time,
	elected: set Time
	}➀
➀fact ring {
	all p: Process | Process in p.^succ
	}➀
➀pred init [t: Time] {
	all p: Process | p.toSend.t = p
	}➀
➀pred step [t, t': Time, p: Process] {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
		}
	}➀
➀fact defineElected {
	no elected.first
	all t: Time-first | elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.prev)}
	}➀
➀fact traces {
	init [first]
	all t: Time-last |
		let t' = t.next |
			all p: Process |
				step [t, t', p] or step [t, t', succ.p] or skip [t, t', p]
	}➀
➀pred skip [t, t': Time, p: Process] {
	p.toSend.t = p.toSend.t'
	}➀
➀pred show { some elected }➀

➀assert AtMostOneElected { lone elected.Time }➀

➀pred progress  {
	all t: Time - TO/last |
		let t' = TO/next [t] |
			some Process.toSend.t => some p: Process | not skip [t, t', p]
	}➀
➀assert AtLeastOneElected { progress => some elected.Time }➀

➀pred looplessPath { no disj t, t': Time | toSend.t = toSend.t' }➀
run show with ➀for 3 Process, 4 Time--
check AtMostOneElected with ➀ for 3 Process, 7 Time--
check AtLeastOneElected with ➀ for 3 Process, 7 Time--
run looplessPath with ➀ for 3 Process, 12 Time
run looplessPath with ➀ for 3 Process, 13 Time
