➀➁open util/ordering [Book] as BookOrder➁➀
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
}
➊➋pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}➋➊
run show with exactly ➊,➋ for 3 but 1 Book
➊➋pred add [b, b': Book, n: Name, a: Addr] {
	b'.addr = b.addr + n->a
}➋➊
➊➋pred del [b, b': Book, n: Name] {
	b'.addr = b.addr - n->Addr
}➋➊
➊➋fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}➋➊
➊➋pred showAdd [b, b': Book, n: Name, a: Addr] {
	add [b, b', n, a]
	#Name.(b'.addr) > 1
}➋➊
run showAdd with exactly ➊,➋ for 3 but 2 Book
➊➋assert delUndoesAdd {
	all b, b', b'': Book, n: Name, a: Addr |
		no n.(b.addr) and add [b, b', n, a] and del [b', b'', n]
		implies
		b.addr = b''.addr
}➋➊
➊➋assert addIdempotent {
	all b, b', b'': Book, n: Name, a: Addr |
		add [b, b', n, a] and add [b', b'', n, a]
		implies
		b'.addr = b''.addr
}➋➊
➊➋assert addLocal {
	all b, b': Book, n, n': Name, a: Addr |
		add [b, b', n, a] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}➋➊
check delUndoesAdd with exactly ➊,➋ for 3
check delUndoesAdd with exactly ➊,➋ for 10 but 3 Book
check addIdempotent with exactly ➊,➋ for 3
check addLocal with exactly ➊,➋ for 3 but 2 Book

➀➋fact factBook{
	all b:Book | no n: Name | n in n.^(b.addr)
	all b:Book,a: Alias | lone a.(b.addr)
}➋➀
➀➋pred add [b, b': Book, n: Name, t: Target] { b'.addr = b.addr + n->t }➋➀
➀➋pred del [b, b': Book, n: Name, t: Target] { b'.addr = b.addr - n->t }➋➀
➀➋fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }➋➀
➀➋assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr
}➋➀
check delUndoesAdd with exactly ➀,➋ for 3
➀➋assert addIdempotent {
	all b, b', b'': Book, n: Name, t: Target |
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr
}➋➀
check addIdempotent with exactly ➀,➋ for 3
➀➋assert addLocal {
	all b, b': Book, n, n': Name, t: Target |
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}➋➀
check addLocal with exactly ➀,➋ for 3 but 2 Book
➀➋assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}➋➀
check lookupYields with exactly ➀,➋ for 4 but 1 Book
➀➁fact factBook{
	all b:Book | no n: Name | n in n.^(b.addr)
	all b:Book,a: Alias | lone a.(b.addr)
}➁➀
➀➁pred add [b, b': Book, n: Name, t: Target] { b'.addr = b.addr + n->t }➁➀
➀➁pred del [b, b': Book, n: Name, t: Target] { b'.addr = b.addr - n->t }➁➀
➀➁fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }➁➀
➀➁pred init [b: Book]  { no b.addr }➁➀
➀➁fact traces {
	init [first]
	all b: Book-last |
	  let b' = b.next |
	    some n: Name, t: Target |
	      add [b, b', n, t] or del [b, b', n, t]
}➁➀
➀➁assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr
}➁➀
check delUndoesAdd with exactly ➀,➁for 3
➀➁assert addIdempotent {
	all b, b', b'': Book, n: Name, t: Target |
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr
}➁➀
check addIdempotent with exactly ➀,➁ for 3
➀➁assert addLocal {
	all b, b': Book, n, n': Name, t: Target |
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}➁➀
check addLocal with exactly ➀,➁ for 3 but 2 Book
➀➁assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}➁➀
check lookupYields with exactly ➀,➁ for 3 but 4 Book

