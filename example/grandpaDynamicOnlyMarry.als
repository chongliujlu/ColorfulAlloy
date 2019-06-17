module owngrandpa --only  marry
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
	}
//need to be changed for born operator
fact Biology {
   	 -- nobody is his or her own ancestor
   	 no p: Person | p in p.^(parents.Time)
   	 -- every person as at most one female and one male parent
	all p : Person | lone p.parents.Time & Woman and lone p.parents.Time & Man
	}
//need to be changed for born operator
➀fact  Bible {
   	 -- Adam and Eve have no parents
   	 no (Adam + Eve).parents.Time
	}➀

➁pred marry [a,b: Person, t,t': Time]{
	//one Woman marry to one Man(" pred marry[a:Woman,b:Man]{...}" gives counterexample (for example,assert "ManMarryWoman")with man marry man)
	//book P167 "analyzer uses multiplicities to generate warnings when the scope setting and signature declarations are mutually inconsistent" also apply to arguments?
	one a & Woman      one b & Man
	➀no a & Eve➀
	➀no b & Adam➀
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
➁pred marry [a:Woman,b: Man, t,t': Time]{
	➀no a & Eve➀
	➀no b & Adam➀
	--no effect on parents relation
	all p: Person| p.parents.t'=p.parents.t
	--can not marry ancessor
	➂no a. *(parents.t) & b.*(parents.t)➂
	--must be single
    	no (a+b).spouse.t
	a.spouse.t'=b
	b.spouse.t'=a
	--no effect on other person
	all p: Person-(a+b) | p.spouse.t'=p.spouse.t
	}➁
*/
fact {
	--Adam's spouse is Eve,
	➁➀Adam.spouse.first= Eve➀➁
	➁➀Eve.spouse.first= Adam➀➁
	➊➁no spouse.first➁➊
	all t: Time-last | let t'=t.next |
		➁some a,b:Person| marry[a,b, t,t']➁ 
	}

-- spouse is symmetric
➁assert SpouseSymmetric{
	all t:Time| spouse.t = ~(spouse.t)
	}➁
check SpouseSymmetric with exactly➁ for 10
check SpouseSymmetric with ➊,➁,➌ for 10
check SpouseSymmetric with exactly➀,➁ for 10
check SpouseSymmetric with ➀,➁,➌ for 10
check SpouseSymmetric with exactly➀,➁,➂ for 10
check SpouseSymmetric with ➀,➁,➂ for 10
check SpouseSymmetric with exactly➁,➂ for 10
check SpouseSymmetric with ➊,➁,➂ for 10

 --a man's spouse is a woman and vice versa
➁assert ManMarryWoman{
	Man.spouse.Time in Woman && Woman.spouse.Time in Man
	}➁
check ManMarryWoman with exactly ➁ for 10 
check ManMarryWoman with ➊,➁,➌ for 10
check ManMarryWoman with exactly ➀,➁ for 10
check ManMarryWoman with  ➀,➁,➌ for 10
check ManMarryWoman with exactly ➁,➂ for 10
check ManMarryWoman with  ➊,➁,➂ for 10
check ManMarryWoman with exactly➀, ➁,➂ for 10
check ManMarryWoman with  ➀,➁,➂ for 10

--nobody is his or her own spouse
➁assert NoOwnSpouse{
	no p: Person | p.spouse.Time = p
	}➁
check NoOwnSpouse with exactly ➁ for 10
check NoOwnSpouse with  ➊,➁,➌ for 10
check NoOwnSpouse with exactly ➀,➁ for 10
check NoOwnSpouse with  ➀,➁,➌ for 10
check NoOwnSpouse with exactly ➁,➂ for 10
check NoOwnSpouse with  ➊,➁,➂ for 10
check NoOwnSpouse with exactly ➀,➁,➂ for 10
check NoOwnSpouse with  ➀,➁,➂ for 10


➁ assert NoIncest {
		all t: Time, p:Person|
				 no p.spouse.t.parents.t & p.parents.t  and 
				 no p.spouse.t & p.^(parents.t) 	 
}➁
check NoIncest with exactly ➁ for 10 but 2 Time -- counterexample
check NoIncest with exactly ➁ for 10 --? 
check NoIncest with  ➊,➁,➌ for 10 but 2 Time
check NoIncest with exactly ➀,➁ for 10 but 2 Time -- counterexample
check NoIncest with  ➀,➁,➌ for 10 but 2 Time
check NoIncest with exactly ➁,➂ for 10 but 2 Time
check NoIncest with  ➊,➁,➂ for 10 
check NoIncest with exactly ➀,➁,➂ for 10 
check NoIncest with  ➀,➁,➂ for 10 

run {} with exactly ➁,➂ for 10 but 6 Time
run {} with exactly➀, ➁,➂ for 10 but 4 Time




