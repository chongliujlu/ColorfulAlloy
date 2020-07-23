module vending

/*
 * ➀ No free drinks
 * ➁ Multiple selection
*/

--open util/ordering[Time]
--sig Time{}
abstract sig State{ }


one sig Ready extends State{ }


one sig Selected extends State{ }



➀one sig Served extends State{ }➀

sig Product{
        ➀price:  one Int➀
        }

➊➋sig Time {
	stock : Product -> one Int,
}➋➊
➀➋sig Time {
	stock : Product -> one Int,
}➋➀
➊➁sig Time {
	stock : Product -> one Int,
	quantity : Product -> one Int
}➁➊
➀➁sig Time {
	stock : Product -> one Int,
	quantity : Product -> one Int,
}➁➀

/*sig Time {
	state : one State,
	➋selection : lone Product➋,
	➁quantity : Product -> one Int➁,
	stock : Product -> one Int,
	➀coins : one Int➀
}*/




















