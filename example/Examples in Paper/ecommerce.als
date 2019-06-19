module Ecommerce

/*
 * ➀ Categories
 * ➁ Hierarchical categories
 * ➂ Multiple categories
 * ➃ Images
 * ➄ Thumbnails
*/

fact FeatureModel {
	➁➊some none➊➁ -- Hierarchical requires Categories
	➂➊some none➊➂ -- Multiple requires Categories
	➄➍some none➍➄ -- Thumbnails requires Images
	➄➊some none➊➄ -- Thumbnails requires Categories
}


sig Product {
	➊catalog : one Catalog➊,
	➀category : some Category➀,
	➃images : set Image➃
}

➃sig Image {}➃

➀➌fact OneCategory {
	category in Product -> one Category
}➌➀

sig Catalog {}

➀sig Category {
	inside : one Catalog+➁Category➁,
	➃➄thumbnails : set Image➄➃
}➀

➀➁
fact Acyclic {
	all c : Category | c not in c.^inside
}➁➀

➀➃➄fact Thumbnails {
	all c : Category | c.thumbnails in (category.((iden+➁^inside➁).c)).images
}➄➃➀

fun catalogs [p : Product] : set Catalog {
	➊p.catalog➊+➀p.category.(➋inside➋+➁^inside➁) & ➁Catalog➁➀
}

run {} with exactly ➊,➋,➌,➍,➎
run {} with exactly ➀
run {} with exactly ➀,➁
run {} with exactly ➀,➂
run {} with exactly ➀,➁,➂
run {} with exactly ➀,➁,➂,➃
run {} with exactly ➀,➁,➂,➃,➄

assert AllCataloged {
	all p : Product | some catalogs[p] and catalogs[p] in Catalog
}
-- It should not give counter-examples
check AllCataloged for 10
