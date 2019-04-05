--Feature ➀: biological grandpas  
module language/grandpa1 ---- Page 84, 85

abstract sig Person {
	father: lone Man,
	mother: lone Woman
	}

sig Man extends Person {
	wife: lone Woman
	}

sig Woman extends Person {
	husband: lone Man
	}

fact {
	no p: Person | p in p.^(mother+father)
	wife = ~husband
	}

assert NoSelfFather {
	no m: Man | m = m.father
	}

// This should not find any counterexample.
//no paint Expr used
check NoSelfFather -- Amalgamate method:  those products that at least with no feature selected(no constrain)?  , no Conterexample

--no Conterexample
--check NoSelfFather with exactly ? or check NoSelfFather with 0? not support


fun grandpas [p: Person] : set Person {
	
	let parent = mother + father + ➀father.wife + mother.husband➀ |
	p.parent.parent & Man

	}

pred ownGrandpa [p: Person] {
	p in p.grandpas
	}

// This should not find any instance.
run ownGrandpa with exactly ➀ for 4 Person --exactly method: ➀ selected, instance fond
run ownGrandpa with exactly ➊ for 4 Person --exactly method: ➊ selected, instance fond

run ownGrandpa for 4 Person-- Amalgamate method:  all product selected ?
run ownGrandpa with ➀ for 4 Person   --Amalgamate method:  those products that with ➀  selected ?
run ownGrandpa with ➊ for 4 Person   --Amalgamate method:  those products that with ➊ selected ? : no instance found


assert NoSelfGrandpa {
	no p: Person | p in p.grandpas
	}

// This should not find any counterexample
check NoSelfGrandpa for 4 Person --Amalgamate method: hose products  that with  selected?  
--check NoSelfGrandpa with exactly  for 4 Person ? exactly with no feature selected, not support 
check NoSelfGrandpa  with exactly ➀ for 4 Person --exactly method:only ➀ selected
check NoSelfGrandpa  with exactly ➊ for 4 Person -- exactly method: only ➊ selected
check NoSelfGrandpa  with  ➀ for 4 Person -- those products that with ➀ selected
check NoSelfGrandpa  with  ➊ for 4 Person -- those products  that with ➊ selected
