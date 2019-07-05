module owngrandpa 
open util/ordering [Time]
/*
 * Based on the toy model of genealogical relationships by Daniel Jackson
 *
 * ➀ Bible
 * ➁ Marriage
 * ➂ Forbid incest
 */

abstract sig Person {
	➁spouse: Person lone -> Time➁,
	parents:  Person->Time,
	alive: set Time
}
sig Man, Woman extends Person {}

➀one sig Eve extends Woman {}➀
➀one sig Adam extends Man {}➀

sig Time {}

fact FeatureModel {
   	 -- ➂ requires ➁
   	 ➂➋some none➋➂
	}

➁pred marry [a,b: Person, t,t': Time]{
	one a & Woman
	one b & Man
	(a+b) in alive.t

	--no effect on "parents" and "alive" relation
	parents.t'=parents.t
	alive.t' = alive.t

	--can not marry ancessor or sibling
	➂no a.*(parents.t) & b.*(parents.t)➂
	--must be single
    	no (a+b).spouse.t
	a.spouse.t'=b
	b.spouse.t'=a
	--no effect on other person
	all p: Person-(a+b) | p.spouse.t'=p.spouse.t
	}➁

➀pred reproduce[mother,father,child: Person,t,t':Time] {
	one mother & Woman
	one father & Man
	(mother+father) in alive.t
	child not in alive.t

	--no effect on "spouse" relation
	➁spouse.t'=spouse.t➁
	--no effect on people except children
	all p: Person-child| p.parents.t'=p.parents.t
	child.parents.t'=mother+father
	alive.t' = alive.t+child
}➀

pred hatch[child:Person,t,t': Time] {
	child not in alive.t

	--no effect on "spouse" relation
	➁spouse.t'=spouse.t➁
	--no effect on people except children
	all p: Person-child| p.parents.t'=p.parents.t
	
	lone child.parents.t' & Woman
	lone child.parents.t' & Man
	child.parents.t' in alive.t
	
	alive.t' = alive.t+child	
}

pred nop[t,t' : Time] {
	➁spouse.t' = spouse.t➁
	parents.t' = parents.t
	alive.t' = alive.t
}
 
pred init{
	-- no alive people in the begining except Adam and Eve
	➀alive.first = Adam+Eve➀
	➊no alive.first➊

	-- nobody is married in the initial time
	➁no spouse.first➁
	-- nobody has parent in initial time
	  no parents.first
	}
fact {
	init
	all t: Time-last | let t'=t.next {
		➁some a,b:Person |  marry[a,b, t,t']➁ or
		➀some a,b,c:Person | reproduce[a,b,c,t,t']➀ or
		➊some a:Person | hatch[a,t,t']➊ or
		nop[t,t']
	}
}
run{} with exactly ➊,➋,➌ for 10 but 6 Time
run {} with exactly ➁ for 10 but 6 Time
run {} with  ➊,➁,➌ for 10 but 6 Time
run {} with exactly ➁,➂ for 10 but 6 Time
run {} with exactly➀, ➁,➂ for 5 but 10 Time

assert OnlyAliveMarryAndHaveChildren {
	➁all t : Time | spouse.t in alive.t -> alive.t➁
	all t : Time | parents.t in alive.t -> alive.t
}
//These should show no counterexample
check OnlyAliveMarryAndHaveChildren  for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➊,➋,➌ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➊,➋,➌ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➀ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➀,➋,➌ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➁ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➊,➁,➌ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➀,➁ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➀,➁,➌ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➁,➂ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➊,➁,➂ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with exactly ➀,➁,➂ for 5 but 10 Time
check OnlyAliveMarryAndHaveChildren with  ➀,➁,➂ for 5 but 10 Time

➁assert SocualNorms {
	-- spouse is symmetric
	all t:Time| spouse.t = ~(spouse.t)
	--nobody is his or her own spouse
	all t:Time | no p: Person | p.spouse.t = p
	 --a man's spouse is a woman and vice versa
	all t: Time|
	 Man.spouse.t in Woman && Woman.spouse.t in Man
	}➁

//These should show no counterexample
check SocualNorms with ➁ for 5 but 20 Time
check SocualNorms with exactly➁ for 5 but 20 Time
check SocualNorms with ➊,➁,➌ for 5 but 20 Time
check SocualNorms with exactly➀,➁ for 5 but 20 Time
check SocualNorms with ➀,➁,➌ for 5 but 20 Time
check SocualNorms with exactly➁,➂ for 5 but 20 Time
check SocualNorms with ➊,➁,➂ for 5 but 20 Time
check SocualNorms with exactly➀,➁,➂ for 5 but 20 Time
check SocualNorms with ➀,➁,➂ for 5 but 20 Time


// can't marry a sibling or a parent
➁ assert NoIncest {
		all t: Time, p: alive.t|
				 no p.spouse.t.parents.t & p.parents.t  and 
				 no p.spouse.t & p.^(parents.t) 	 
}➁

check NoIncest with  ➁ for 6 but 10 Time --counterexample
check NoIncest with exactly ➁ for 6 but 10 Time --counterexample
check NoIncest with  ➊,➁,➌ for 6 but 10 Time --counterexample
check NoIncest with exactly ➀,➁ for 6 but 10 Time -- counterexample
check NoIncest with  ➀,➁,➌ for 6 but 10 Time --counterexample
check NoIncest with exactly ➁,➂ for 6 but 10 Time
check NoIncest with  ➊,➁,➂ for 6 but 10 Time
check NoIncest with exactly ➀,➁,➂ for 6 but 10 Time
check NoIncest with  ➀,➁,➂ for 6 but 10 Time



➀assert  Bible {
	-- Adam and Eve have no parents
   	 all t: Time | no (Adam + Eve).parents.t
	 -- every person(who is alive) except Adam and Eve has a mother and father
           all t:Time, p: alive.t - (Adam + Eve) | 
		one mother: Woman, father: Man | p.parents.t = mother + father
	}➀
//these should give no counterexample
check Bible with  ➀for 5 but 10 Time
check Bible with exactly ➀for 5 but 10 Time
check Bible with ➀,➋,➌for 5 but 10 Time
check Bible with exactly ➀,➁for 5 but 10 Time
check Bible with  ➀,➁,➌for 5 but 10 Time
check Bible with exactly ➀,➁,➂for 5 but 10 Time
check Bible with  ➀,➁,➂for 5 but 10 Time


assert Biology {
   	 -- nobody is his or her own ancestor
   	all t: Time|  no p: Person | p in p.^(parents.t)
   	 -- every person has at most one female and one male parent
	all p : Person,t: Time | lone p.parents.t & Woman and lone p.parents.t & Man
	}
//these should show no counterexample

check Biology with exactly ➊,➋,➌ for 5 but 10 Time
check Biology with  ➊,➋,➌ for 5 but 10 Time
check Biology with exactly ➀ for 5 but 10 Time
check Biology with  ➀,➋,➌ for 5 but 10 Time
check Biology with exactly ➁ for 5 but 10 Time
check Biology with  ➊,➁,➌ for 5 but 10 Time
check Biology with exactly ➀,➁ for 5 but 10 Time
check Biology with  ➀,➁,➌ for 5 but 10 Time
check Biology with exactly ➁,➂ for 5 but 10 Time
check Biology with  ➊,➁,➂ for 5 but 10 Time
check Biology with exactly ➀,➁,➂ for 5 but 10 Time
check Biology with  ➀,➁,➂ for 5 but 10 Time


➀assert AllDescendFromAdamAndEve {
	all t: Time,  p : alive.t - (Adam + Eve) | p in ^(parents.t).Adam and p in ^(parents.t).Eve
}➀
//These should give no counterexample
check AllDescendFromAdamAndEve with  ➀ for 7 expect 0
check AllDescendFromAdamAndEve with exactly ➀ for 7 expect 0
check AllDescendFromAdamAndEve with exactly ➀,➁ for 7 expect 0
check AllDescendFromAdamAndEve with exactly ➀,➁,➂ for 7 expect 0

assert OwnGrandPa {
	all t: Time |no p : alive.t |
		p in p.(parents+➁parents.t.spouse➁).t .((parents+➁parents.t.spouse➁).t)
} 

check OwnGrandPa with exactly ➊,➋,➌ for 6 but 10 Time
check OwnGrandPa with  ➊,➋,➌ for 6 but 10 Time
check OwnGrandPa with exactly ➀for 5 but 10 Time 
check OwnGrandPa with  ➀,➋,➌for 5 but 10 Time
check OwnGrandPa with exactly ➁ for 6 but 10 Time-- counterexample
check OwnGrandPa with  ➊,➁,➌ for 6 but 10 Time-- counterexample
check OwnGrandPa with exactly ➀,➁ for 6 but 10 Time--counterexample
check OwnGrandPa with  ➀,➁,➌ for 6 but 10 Time--counterexample
check OwnGrandPa with exactly ➁,➂ for 6 but 10 Time --counterexample
check OwnGrandPa with  ➊,➁,➂ for 6 but 10 Time--counterexample
check OwnGrandPa with exactly ➀,➁,➂ for 6 but 10 Time
check OwnGrandPa with  ➀,➁,➂ for 6 but 10 Time
