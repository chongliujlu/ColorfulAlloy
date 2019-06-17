module vending

/*
 * ➀ No free drinks
 * ➁ Multiple selection
*/

open util/ordering[Time]

abstract sig State {}
one sig Ready, Selected extends State {}
➀one sig Served extends State {}➀

sig Product {
	➀price : one Int➀
}

sig Time {
	state : one State,
	➋selection : lone Product➋,
	➁quantity : Product -> one Int➁,
	stock : Product -> one Int,
	➀coins : one Int➀
}

➀pred insertcoin [t,t' : Time] {
	t.state in Ready
	lt[t.coins,max]

	t'.state = t.state
	➋t'.selection = t.selection➋
	➁t'.quantity = t.quantity➁
	t'.stock = t.stock
	t'.coins = plus[t.coins,1]
}➀

pred select [t,t' : Time, p : Product] {
	t.state = Ready
	➋no t.selection➋
	➋gt[t.stock[p],0]➋
	➁gt[t.stock[p],t.quantity[p]]➁
	➁lt[t.quantity[p],max]➁
	➀gte[t.coins,p.price]➀

	t'.state = ➋Selected➋+➁Ready➁
	➋t'.selection = p➋
	➁t'.quantity = t.quantity ++ p->plus[t.quantity[p],1]➁
	t'.stock = t.stock
	➀t'.coins = minus[t.coins,p.price]➀
}

➁pred finish [t,t' : Time] {
	t.state = Ready
	some p : Product | gt[t.quantity[p],0]
	t'.state = Selected
	t'.quantity = t.quantity
	t'.stock = t.stock
	➀t'.coins = t.coins➀
}➁

pred serve [t,t' : Time] {
	t.state = Selected
	
	➊t'.state = Ready➊
	➀t'.state = Served➀
	➋no t'.selection➋
	➁all p : Product | t'.quantity[p] = 0➁
	➋t'.stock = t.stock ++ t.selection -> minus[t.stock[t.selection],1]➋
	➁all p : Product | t'.stock[p] = minus[t.stock[p],t.quantity[p]]➁
	➀t'.coins = t.coins➀
}

➀pred returnchange [t,t' : Time] {
	t.state in Served

	t'.state = Ready
	➋t'.selection = t.selection➋
	➁t'.quantity = t.quantity➁
	t'.stock = t.stock
	t'.coins = 0
}➀

fact Init {
	first.state = Ready
	➋no first.selection➋
	all p : Product | gte[first.stock[p],0] and ➀gt[p.price,0]➀ and ➁first.quantity[p] = 0➁
	➀first.coins = 0➀
}

fact Traces {
	all t : Time - last {
		(some p : Product | select[t,t.next,p]) or
		➀insertcoin[t,t.next]➀ or
		serve[t,t.next] or
		➀returnchange[t,t.next]➀ or
		➁finish[t,t.next]➁
	}
}

run {} with exactly ➊,➋ for 3 but 4 Int, 10 Time
run {} with exactly ➀ for 3 but 4 Int, 10 Time
run {} with exactly ➁ for 3 but 4 Int, 10 Time
run {} with exactly ➀,➁ for 3 but 4 Int, 10 Time

assert Stock {
	all t : Time, p : Product | gte[t.stock[p],0]
}

check Stock for 5 but 4 Int, 15 Time
check Stock with exactly ➊,➋ for 5 but 4 Int, 15 Time
check Stock with exactly ➀ for 5 but 4 Int, 15 Time
check Stock with exactly ➁ for 5 but 4 Int, 15 Time
check Stock with exactly ➀,➁ for 5 but 4 Int, 15 Time

pred isSelected[t : Time, p : Product] {
	➋p in t.selection➋
	➁gt[t.quantity[p],0]➁
}

assert Selection {
	all t : Time, p : Product | t.stock[p] = 0 implies all t' : t.nexts | not isSelected[t',p]
}

check Selection for 5 but 4 Int, 15 Time
check Selection with exactly ➊,➋ for 5 but 4 Int, 15 Time
check Selection with exactly ➀ for 5 but 4 Int, 15 Time
check Selection with exactly ➁ for 5 but 4 Int, 15 Time
check Selection with exactly ➀,➁ for 5 but 4 Int, 15 Time
