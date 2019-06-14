module owngrandpa

/*
 * Based on the toy model of genealogical relationships by Daniel Jackson
 *
 * ➀ Bible
 * ➁ Marriage
 * ➂ Forbid incest
 */

abstract sig Person {
	➁spouse: lone Person➁, 
	parents: set Person,
	children: set Person
	}
sig Man, Woman extends Person {}

➀one sig Eve extends Woman {}➀
➀one sig Adam extends Man {}➀

fact FeatureModel {
   	 -- ➂ requires ➁
   	 ➂➋some none➋➂
	}

fact Biology {
   	 -- nobody is his or her own ancestor
   	 no p: Person | p in p.^parents
   	 -- every person as at most one female and one male parent
	all p : Person | lone p.parents & Woman and lone p.parents & Man
	no p:Person| p in p.^children
	}

➀fact Bible {
   	 -- every person except Adam and Eve has a mother and father
  	 -- all p: Person - (Adam + Eve) | one mother: Woman, father: Man | p.parents = mother + father
   	 -- Adam and Eve have no parents
   	 no (Adam + Eve).parents
   	 -- Adam's spouse is Eve
   	 ➁Adam.spouse = Eve➁
	}➀

➁fact SocialNorms {
    	-- nobody is his or her own spouse
    	no p: Person | p.spouse = p
    	-- spouse is symmetric
    	spouse = ~spouse
   	 -- a man's spouse is a woman and vice versa
    	Man.spouse in Woman && Woman.spouse in Man
	}➁

--➁➂fact NoIncest {
    -- can't marry a sibling
 --   no p: Person | some p.spouse.parents & p.parents
    -- can't marry a parent
 --   no p: Person | some p.spouse & p.^parents
--}➂➁

--assert OwnGrandPa {
--  no p : Person | p in p.(parents+➁parents.spouse➁).(parents+➁parents.spouse➁)
--} 

--check OwnGrandPa with exactly ➁ for 2
--check OwnGrandPa with exactly ➀,➁ for 4
--check OwnGrandPa with exactly ➁,➂ for 4
--check OwnGrandPa with exactly ➀,➁,➂ for 7
--check OwnGrandPa with ➋ for 10 expect 0

➁pred marry [a,a': one Woman,b,b': one Man]{
    	a.parents=a'.parents
    	b.parents=b'.parents
	a.children=a'.children
	b.children=b'.children

   	 --no same parent
    	➂no (a.*parents+a') &( b.*parents+b') ➂
    	--single
    	no (a+b).spouse
    	a'.spouse=b'
	}➁

//one can not marry his ancestor and his sibling
➂➁assert NoIncest {
    all a,a':Woman, b,b':Man| -- a,a': Woman-➀Eve➀,b,b':Man-➀Adam➀ 

    marry[a,a',b,b' ] implies (no a'.*parents & b'.*parents) 
}➁➂

check NoIncest with exactly ➁,➂ for 10
check NoIncest with exactly ➀,➁,➂ for 10


➁pred ReProduce[a: Woman, b: Man, p,p': set Person]{
	➀ (p+p') in (Person-(Adam+Eve))➀
	no (p+p').children
    	a.spouse=b 

    	no p.parents                    
    	p'.parents=a+b
	}➁

➁➀assert DescendFromAdamAndEve{
    all a : Woman - Eve , b : Man-Adam|
        let p=Person-(Adam+Eve+a+b)|
        let p'=Person-(Adam+Eve+a+b+p)|
    ReProduce[a,b,p,p']    implies p' in ^parents.Adam and p' in ^parents.Eve
}➀➁

check DescendFromAdamAndEve with exactly ➀,➁ for 4
check DescendFromAdamAndEve with exactly ➀,➁ for 4



