sig A {
	r : set B
}

sig B {}

fact Bestiary {
	➀r in A lone -> B➀
	➁r in A -> lone B➁
	➂r in A -> some B➂
	➃r in A some -> B➃
}

assert Injective {
	r.~r in iden
}

check Injective with ➀ for 25
check Injective with ➀ for 30

assert Simple {
	~r.r in iden
}

check Simple with ➁ for 25
check Simple with ➁ for 30

assert Associative {
	r.(~r.r) = (r.~r).r
}

check Associative for 6
check Associative for 7
check Associative for 8
