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
	parents: set Person
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
}

➀fact Bible {
    -- every person except Adam and Eve has a mother and father
    all p: Person - (Adam + Eve) | one mother: Woman, father: Man | p.parents = mother + father
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

➁➂fact NoIncest {
    -- can't marry a sibling
    no p: Person | some p.spouse.parents & p.parents
    -- can't marry a parent
    no p: Person | some p.spouse & p.^parents
}➂➁

assert OwnGrandPa {
	no p : Person | p in p.(parents+➁parents.spouse➁).(parents+➁parents.spouse➁)
} 

check OwnGrandPa with exactly ➁ for 2
check OwnGrandPa with exactly ➀,➁ for 4
check OwnGrandPa with exactly ➁,➂ for 4
check OwnGrandPa with exactly ➀,➁,➂ for 7
check OwnGrandPa with ➋ for 10 expect 0

➀assert AllDescendFromAdamAndEve {
	all p : Person - (Adam + Eve) | p in ^parents.Adam and p in ^parents.Eve
}➀

check AllDescendFromAdamAndEve with ➀ for 10 expect 0
check AllDescendFromAdamAndEve with exactly ➀ for 10 expect 0
check AllDescendFromAdamAndEve with ➀,➋,➌ for 10 expect 0
check AllDescendFromAdamAndEve with exactly ➀,➁ for 10 expect 0
check AllDescendFromAdamAndEve with ➀,➁,➌ for 10 expect 0
check AllDescendFromAdamAndEve with exactly ➀,➂ for 10 expect 0
check AllDescendFromAdamAndEve with ➀,➋,➂ for 10 expect 0
check AllDescendFromAdamAndEve with exactly ➀,➁,➂ for 10 expect 0
check AllDescendFromAdamAndEve with ➀,➁,➂ for 10 expect 0
