/**
* Based on the examples of Chapter 2  
* ➀: Hierarchy
* ➁: No Meaningless Add (Alias refer to no Addr)
* ➂: No Single Mapping Deletion
*     (name mapped to some target besides the one about to delete)
*/

module tour/addressBook
open util/ordering [Book]
fact FM{
	//No Meaningless Add requires  Hierarchy
	➁➊some none➊➁
	//feature ➁ require Hierarchy
	➂➊some none➊➂
	
}
abstract sig Target { }
sig Addr extends Target { }
sig Name extends Target { }

➀sig Alias, Group extends Name { }➀
//signature "Name" is abstract if feature  ➀ is selected
➀fact abstractName{
	all n:Name| n in Alias+Group
	}➀

sig Book {
	names: set Name,
	addr: names->some Target	
	} {
	--addr is a mapping from Name to Addr if feature ➀ is not selected 
	➊addr in names->Addr➊
	  no n: Name | n in n.^addr -- or : no n: Name | n in ➀n.^addr➀+➊n.addr➊ ???

	➀all a: Alias | lone a.addr➀

	}

pred add [b, b': Book, n: Name, t: Target] { 
	➁(t in Addr or  some lookup[b,t])➁
	b'.addr = b.addr + n->t  
	}
pred del [b, b': Book, n: Name, t: Target] { 
	➂(no b.addr.n or some n.(b.addr) - t)➂
	b'.addr = b.addr - n->(➀t➀ +➊Addr➊) 
	}
fun lookup [b: Book, n: Name] : set Addr { 
	n.^(b.addr) & ➀Addr➀ --or : ➊n.(b.addr)➊ +➀n.^(b.addr) & Addr ??? 
	}

pred init (b: Book) {
	no b.addr
	}
fact traces {
	init [first]
	all b: Book - last | let b' = next [b] |
	some n: Name, t: Target |
		 add [b, b', n, t] or del [b, b', n, t] 
	}


assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		--t can only be Addr is feature ➀ is not selected
		➊ t in Addr➊ and
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr
	}
// These should not find any counterexample.
check delUndoesAdd for 3
check delUndoesAdd with exactly ➊,➋,➌ for 3
check delUndoesAdd with  ➊,➋,➌ for 3
check delUndoesAdd with exactly ➀ for 3
check delUndoesAdd with  ➀,➋,➌ for 3
check delUndoesAdd with exactly ➀,➁ for 3 
check delUndoesAdd with  ➀,➁,➌ for 3
check delUndoesAdd with exactly ➀,➂ for 3
check delUndoesAdd with  ➀,➋,➂ for 3
check delUndoesAdd with exactly ➀,➁,➂ for 3
check delUndoesAdd with  ➀,➁,➂ for 3





assert addIdempotent {
	all b, b', b'': Book, n: Name, t: Target |
		➊ t in Addr➊ and
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr
	}

// These should not find any counterexample.
check addIdempotent  for 3
check addIdempotent with exactly ➊,➋ for 3
check addIdempotent with  ➊,➋ for 3
check addIdempotent with exactly ➀ for 3
check addIdempotent with ➀,➋ for 3
check addIdempotent with exactly ➀,➁ for 3
check addIdempotent with ➀,➁ for 3


assert addLocal {
	all b, b': Book, n, n': Name, t: Target |
		➊some t & Addr➊ and
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
	}

// This shows a counterexample
check addLocal for 3 but 2 Book 
check addLocal with exactly ➊,➋ for 3 but 2 Book
check addLocal with  ➊,➋ for 3 but 2 Book
// This shows a counterexample
check addLocal with exactly ➀ for 3 but 2 Book
// This shows a counterexample
check addLocal with ➀,➋ for 3 but 2 Book
// This shows a counterexample
check addLocal with exactly ➀,➁ for 3 but 2 Book
// This shows a counterexample
check addLocal with ➀,➁ for 3 but 2 Book


assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
	}

// This shows a counterexample
check lookupYields for 3 but 4 Book
check lookupYields with exactly ➊,➋,➌ for 3 but 4 Book
check lookupYields with ➊,➋,➌ for 3 but 4 Book
// This shows a counterexample  "group can map to empty"
check lookupYields with exactly ➀ for 3 but 4 Book
// This shows a counterexample  "group can map to empty"
check lookupYields with ➀,➋,➌ for 3 but 4 Book
check lookupYields with exactly ➀,➁ for 3 but 4 Book
check lookupYields with ➀,➁,➌ for 3 but 4 Book
// This shows a counterexample 
check lookupYields with exactly ➀,➂ for 3 but 4 Book
// This shows a counterexample 
check lookupYields with ➀,➋,➂ for 3 but 4 Book
check lookupYields with exactly ➀,➁,➂ for 3 but 4 Book
check lookupYields with ➀,➁,➂ for 3 but 4 Book
