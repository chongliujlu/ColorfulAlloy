module vending

/*
 * ➀ No free drinks
 * ➁ Multiple selection
*/

➊➋open util/ordering[Time]➋➊
➀➋open util/ordering[Time]➋➀
➊➁open util/ordering[Time]➁➊
➀➁open util/ordering[Time]➁➀
➊➋abstract sig State {}➋➊
➀➋abstract sig State {}➋➀
➊➁abstract sig State {}➁➊
➀➁abstract sig State {}➁➀

➊➋one sig Ready extends State{} ➋➊
➀➋one sig Ready extends State{} ➋➀
➊➁one sig Ready extends State{} ➁➊
➀➁one sig Ready extends State{} ➁➀

➊➋one sig Selected extends State{} ➋➊
➀➋one sig Selected extends State{} ➋➀
➊➁one sig Selected extends State{} ➁➊
➀➁one sig Selected extends State{} ➁➀


➀➋one sig Served extends State {}➋➀
➀➁one sig Served extends State {}➁➀
➊➋sig Product { }➋➊
➀➋sig Product {
	price : one Int
	}➋➀
➊➁sig Product { }➁➊
➀➁sig Product {
	price : one Int
	}➁➀

➊➋sig Time {
	state : one State,
	stock : Product -> one Int,
	selection : lone Product
}➋➊
➀➋sig Time {
	state : one State,
	stock : Product -> one Int,
	selection : lone Product,
	coins : one Int
}➋➀
➊➁sig Time {
	state : one State,
	stock : Product -> one Int,
	quantity : Product -> one Int
}➁➊
➀➁sig Time {
	state : one State,
	stock : Product -> one Int,
	quantity : Product -> one Int,
	coins : one Int
}➁➀

➀➁pred insertcoin [t,t' : Time] {
	t.state in Ready
	t'.coins = plus[t.coins,1]
}➁➀



➊➋pred select [t,t' : Time, p : Product] {
	t.state = Ready
	no t.selection
	gt[t.stock[p],0]

	t'.state =Selected
t'.selection = p
	t'.stock = t.stock
}➋➊
➀➋pred select [t,t' : Time, p : Product] {
	t.state = Ready
	no t.selection
	gt[t.stock[p],0]
gte[t.coins,p.price]

	t'.state =Selected
t'.selection = p
	t'.stock = t.stock
t'.coins = minus[t.coins,p.price]
}➋➀

➊➁pred select [t,t' : Time, p : Product] {
	t.state = Ready
	gt[t.stock[p],t.quantity[p]]
	lt[t.quantity[p],max]
	t'.state =Ready
t'.quantity = t.quantity ++ p->plus[t.quantity[p],1]
	t'.stock = t.stock
}➁➊
➀➁pred select [t,t' : Time, p : Product] {
	t.state = Ready
	gt[t.stock[p],t.quantity[p]]
	lt[t.quantity[p],max]
gte[t.coins,p.price]
	t'.state =Ready
t'.quantity = t.quantity ++ p->plus[t.quantity[p],1]
	t'.stock = t.stock
t'.coins = minus[t.coins,p.price]
}➁➀



➊➁pred finish [t,t' : Time] {
	t.state = Ready
	some p : Product | gt[t.quantity[p],0]
	t'.state = Selected
	t'.quantity = t.quantity
	t'.stock = t.stock

}➁➊


➀➁pred finish [t,t' : Time] {
	t.state = Ready
	some p : Product | gt[t.quantity[p],0]
	t'.state = Selected
	t'.quantity = t.quantity
	t'.stock = t.stock
	t'.coins = t.coins
}➁➀

➊➋pred serve [t,t' : Time] {
	t.state = Selected
	t'.state = Ready
	no t'.selection
	t'.stock = t.stock ++ t.selection -> minus[t.stock[t.selection],1]
}➋➊
➀➋pred serve [t,t' : Time] {
	t.state = Selected
	t'.state = Served
	no t'.selection
	t'.stock = t.stock ++ t.selection -> minus[t.stock[t.selection],1]
	t'.coins = t.coins
}➋➀
➊➁pred serve [t,t' : Time] {
	t.state = Selected
	t'.state = Ready
	all p : Product | t'.quantity[p] = 0
	all p : Product | t'.stock[p] = minus[t.stock[p],t.quantity[p]]
}➁➊
➀➁pred serve [t,t' : Time] {
	t.state = Selected
	t'.state = Served
	all p : Product | t'.quantity[p] = 0
	all p : Product | t'.stock[p] = minus[t.stock[p],t.quantity[p]]
	t'.coins = t.coins
}➁➀

➀➋pred returnchange [t,t' : Time] {
	t.state in Served

	t'.state = Ready
	t'.selection = t.selection

	t'.stock = t.stock
	t'.coins = 0
}➋➀

➀➁pred returnchange [t,t' : Time] {
	t.state in Served

	t'.state = Ready

	t'.quantity = t.quantity
	t'.stock = t.stock
	t'.coins = 0
}➁➀




run {} with  ➊,➋ for 3 but 4 Int, 10 Time
run {} with  ➀,➋ for 3 but 4 Int, 10 Time
run {} with  ➊,➁ for 3 but 4 Int, 10 Time
run {} with  ➀,➁ for 3 but 4 Int, 10 Time

➊➋assert Stock {
	all t : Time, p : Product | gte[t.stock[p],0]
}➋➊
➀➋assert Stock {
	all t : Time, p : Product | gte[t.stock[p],0]
}➋➀
➊➁assert Stock {
	all t : Time, p : Product | gte[t.stock[p],0]
}➁➊
➀➁assert Stock {
	all t : Time, p : Product | gte[t.stock[p],0]
}➁➀

check Stock with exactly ➊,➋ for 5 but 4 Int, 15 Time
check Stock with exactly ➀,➋ for 5 but 4 Int, 15 Time
check Stock with exactly ➊,➁ for 5 but 4 Int, 15 Time
check Stock with exactly ➀,➁ for 5 but 4 Int, 15 Time

➊➋pred isSelected[t : Time, p : Product] {
	➋p in t.selection➋
}➋➊
➀➋pred isSelected[t : Time, p : Product] {
	p in t.selection
}➋➀
➊➁pred isSelected[t : Time, p : Product] {

	➁gt[t.quantity[p],0]➁
}➁➊
➀➁pred isSelected[t : Time, p : Product] {
	➁gt[t.quantity[p],0]➁
}➁➀

➊➋assert Selection {
	all t : Time, p : Product | t.stock[p] = 0 implies all t' : t.nexts | not isSelected[t',p]
}➋➊
➀➋assert Selection {
	all t : Time, p : Product | t.stock[p] = 0 implies all t' : t.nexts | not isSelected[t',p]
}
➋➀
➊➁assert Selection {
	all t : Time, p : Product | t.stock[p] = 0 implies all t' : t.nexts | not isSelected[t',p]
}
➁➊
➀➁assert Selection {
	all t : Time, p : Product | t.stock[p] = 0 implies all t' : t.nexts | not isSelected[t',p]
}
➁➀

check Selection with  ➊,➋ for 5 but 4 Int, 15 Time

