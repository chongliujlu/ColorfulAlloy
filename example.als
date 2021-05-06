module tour/addressBook
➀➁open util/ordering [Book] ➁➀
fact FeatureModel{
➁➊some none➊➁
}
➊➋sig Name{ }➋➊
➊➋sig Addr { }➋➊
➀abstract sig Target { }➀
➀sig Addr extends Target { }➀
➀abstract sig Name extends Target { }➀
➀sig Alias extends Name { }➀
➀sig Group extends Name { }➀
sig Book {
	➊➋addr: Name -> lone Addr➋➊,
	➀names: set Name➀,
	➀addr: names->some Target➀
}{
	➀no n: Name | n in n.^addr➀
	➀all a: Alias | lone a.addr➀
}

➊➋pred add [b, b': Book, n: Name, a: Addr] {
	b'.addr = b.addr + n->a
}➋➊
➊➋pred del [b, b': Book, n: Name] {
	b'.addr = b.addr - n->Addr
}➋➊
➊➋fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}➋➊
➀pred add [b, b': Book, n: Name, t: Target] { b'.addr = b.addr + n->t }➀
➀pred del [b, b': Book, n: Name, t: Target] { b'.addr = b.addr - n->t }➀
➀fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }➀
➊➋pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}➋➊

➀➁pred init [b: Book]  { no b.addr }➁➀
➀➁fact traces {
	init [first]
	all b: Book-last |
	  let b' = b.next |
	    some n: Name, t: Target |
	      add [b, b', n, t] or del [b, b', n, t]
}➁➀
➊➋pred showAdd [b, b': Book, n: Name, a: Addr] {
	add [b, b', n, a]
	#Name.(b'.addr) > 1
}➋➊
--run showAdd with ➊,➋ for 3 but 2 Book
assert delUndoesAdd {
	➊➋all b, b', b'': Book, n: Name, a: Addr |
		no n.(b.addr) and add [b, b', n, a] and del [b', b'', n]
		implies
		b.addr = b''.addr➋➊
	➀all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr➀
}
assert addIdempotent {
	➊➋all b, b', b'': Book, n: Name, a: Addr |
		add [b, b', n, a] and add [b', b'', n, a]
		implies
		b'.addr = b''.addr➋➊
	➀all b, b', b'': Book, n: Name, t: Target |
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr➀
}

assert addLocal {
	➊➋all b, b': Book, n, n': Name, a: Addr |
		add [b, b', n, a] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']➋➊
	➀all b, b': Book, n, n': Name, t: Target |
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']➀
}

➀assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}➀


check delUndoesAdd with exactly ➊,➋ for 15
check delUndoesAdd  with exactly ➀for 15
check delUndoesAdd  with exactly ➀,➁for 15
check delUndoesAdd with exactly ➊,➋ for 18
check delUndoesAdd  with exactly ➀for 18
check delUndoesAdd  with exactly ➀,➁for 18
check delUndoesAdd with exactly ➊,➋ for 20
check delUndoesAdd  with exactly ➀for 20
check delUndoesAdd  with exactly ➀,➁for 20

check addIdempotent with exactly ➊,➋ for 15
check addIdempotent  with exactly ➀for 15
check addIdempotent  with exactly ➀,➁for 15
check addIdempotent with exactly ➊,➋ for 18
check addIdempotent  with exactly ➀for 18
check addIdempotent  with exactly ➀,➁for 18
check addIdempotent with exactly ➊,➋ for 20
check addIdempotent  with exactly ➀for 20
check addIdempotent  with exactly ➀,➁for 20

check addLocal with exactly ➊,➋ for 15
check addLocal  with exactly ➀for 15
check addLocal  with exactly ➀,➁for 15 //counterexample
check addLocal with exactly ➊,➋ for 18
check addLocal  with exactly ➀for 18
check addLocal  with exactly ➀,➁for 18
check addLocal with exactly ➊,➋ for 20
check addLocal  with exactly ➀for 20
check addLocal  with exactly ➀,➁for 20
















