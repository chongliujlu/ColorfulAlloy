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
	parents:  Person->Time ,
	}
sig Man, Woman extends Person {}

➀one sig Eve extends Woman {}➀
➀one sig Adam extends Man {}➀

sig Time{}

fact FeatureModel {
   	 -- ➂ requires ➁
   	 ➂➋some none➋➂
	//feature Marriage must be include
	➋some none➋
	}


➁pred marry [a,b: Person, t,t': Time]{
	//one Woman marry to one Man(" pred marry[a:Woman,b:Man]{...}" gives counterexample (for example,assert "ManMarryWoman")with Man marry Man)
	//book P167 "analyzer uses multiplicities to generate warnings when the scope setting and signature declarations are mutually inconsistent" also apply to here?
	one a & Woman      one b & Man

	--no effect on "parents" relation
	all p: Person| p.parents.t'=p.parents.t

	--can not marry ancessor or sibling
	➂no a. *(parents.t) & b.*(parents.t)➂
	--must be single
    	no (a+b).spouse.t
	a.spouse.t'=b
	b.spouse.t'=a
	--no effect on other person
	all p: Person-(a+b) | p.spouse.t'=p.spouse.t
	}➁

/*
➁pred marry [a: one Woman, b: one Man, t,t': Time]{
	--no effect on "parents" relation
	all p: Person| p.parents.t'=p.parents.t

	--can not marry ancessor or sibling
	➂no a. *(parents.t) & b.*(parents.t)➂
	--must be single
    	no (a+b).spouse.t
	a.spouse.t'=b
	b.spouse.t'=a
	--no effect on other person
	all p: Person-(a+b) | p.spouse.t'=p.spouse.t
	}➁
*/

➁pred reProduce[disj mother,father: Person, t,t':Time, children: set Person]{
	➀Adam not in children➀
	➀Eve not in children➀
	
	--must be couple 
	mother.spouse.t=father
	father.spouse.t=mother
	--no effect on "spouse" relation
	all p:Person| p.spouse.t'=p.spouse.t
	--no effect on people except children
	all p: Person-children| p.parents.t'=p.parents.t

	no children.parents.t
	no children.spouse.t
	children.parents.t'=mother+father
}➁
pred init{
	--Adam's spouse is Eve,
	➁➀Adam.spouse.first= Eve➀➁
	--Eve's spouse is Adam,
	➁➀Eve.spouse.first= Adam➀➁
	--only Adam and Eve has spouse in the initial time 
	➁➀all p: Person-(Adam+Eve)| no p.spouse.first➀➁
	➊➁no spouse.first➁➊
	--nobody has parent in initial time
	  no parents.first
	}
fact {
	init
	all t: Time-last | let t'=t.next |
		➁some a,b,children:Person | marry[a,b, t,t']
			 or reProduce[a,b,t,t',children] ➁	
	}
run {} with exactly ➁ for 10 but 6 Time
run {} with  ➊,➁,➌ for 10 but 6 Time
run {} with exactly ➁,➂ for 10 but 6 Time
run {} with exactly➀, ➁,➂ for 10 but 4 Time


-- spouse is symmetric
➁assert SpouseSymmetric{
	all t:Time| spouse.t = ~(spouse.t)
	}➁
//These should show no counterexample
check SpouseSymmetric with exactly➁ for 7
check SpouseSymmetric with ➊,➁,➌ for 7
check SpouseSymmetric with exactly➀,➁ for 7
check SpouseSymmetric with ➀,➁,➌ for 7
check SpouseSymmetric with exactly➁,➂ for 7
check SpouseSymmetric with ➊,➁,➂ for 7
check SpouseSymmetric with exactly➀,➁,➂ for 7
check SpouseSymmetric with ➀,➁,➂ for 7


 --a man's spouse is a woman and vice versa
➁assert ManMarryWoman{
	Man.spouse.Time in Woman && Woman.spouse.Time in Man
	}➁
//these should show no counterexample
check ManMarryWoman with exactly ➁ for 7 
check ManMarryWoman with ➊,➁,➌ for 7
check ManMarryWoman with exactly ➀,➁ for 7
check ManMarryWoman with  ➀,➁,➌ for 7
check ManMarryWoman with exactly ➁,➂ for 7
check ManMarryWoman with  ➊,➁,➂ for 7
check ManMarryWoman with exactly➀, ➁,➂ for 7
check ManMarryWoman with  ➀,➁,➂ for 7

--nobody is his or her own spouse
➁assert NoOwnSpouse{
	no p: Person | p.spouse.Time = p
	}➁
//these should show no counterexample
check NoOwnSpouse with exactly ➁ for 7
check NoOwnSpouse with  ➊,➁,➌ for 7
check NoOwnSpouse with exactly ➀,➁ for 7
check NoOwnSpouse with  ➀,➁,➌ for 7
check NoOwnSpouse with exactly ➁,➂ for 7
check NoOwnSpouse with  ➊,➁,➂ for 7
check NoOwnSpouse with exactly ➀,➁,➂ for 7
check NoOwnSpouse with  ➀,➁,➂ for 7


➁ assert NoIncest {
		all t: Time, p:Person|
				 no p.spouse.t.parents.t & p.parents.t  and 
				 no p.spouse.t & p.^(parents.t) 	 
}➁
check NoIncest with exactly ➁ for 10 --counterexample
check NoIncest with  ➊,➁,➌ for 10 
check NoIncest with exactly ➀,➁ for 10 -- counterexample
check NoIncest with  ➀,➁,➌ for 10 
check NoIncest with exactly ➁,➂ for 10 
check NoIncest with  ➊,➁,➂ for 6 
check NoIncest with exactly ➀,➁,➂ for 7
check NoIncest with  ➀,➁,➂ for 6


-- Adam and Eve have no parents
➀assert  NoAdamEveParent {
   	 no (Adam + Eve).parents.Time
	}➀
//these should give no counterexample
check NoAdamEveParent with exactly ➀,➁for 10
check NoAdamEveParent with  ➀,➁,➌for 10
check NoAdamEveParent with exactly ➀,➁,➂for 10
check NoAdamEveParent with  ➀,➁,➂for 10


assert Biology {
   	 -- nobody is his or her own ancestor
   	 no p: Person | p in p.^(parents.Time)
   	 -- every person as at most one female and one male parent
	all p : Person | lone p.parents.Time & Woman and lone p.parents.Time & Man
	}
//these should show no counterexample
check Biology with exactly ➁ for 6
check Biology with  ➊,➁,➌ for 6
check Biology with exactly ➀,➁ for 6
check Biology with  ➀,➁,➌ for 6
check Biology with exactly ➁,➂ for 6
check Biology with  ➊,➁,➂ for 6
check Biology with exactly ➀,➁,➂ for 6
check Biology with  ➀,➁,➂ for 6


