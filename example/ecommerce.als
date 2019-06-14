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

-- It was called Product, but that did not work and changed to Item
-- Instead of Feature and Product you should use unconmmon identifiers in the translation
-- such as _Feature_ or _Product_
sig Item {
	➊catalog : one Catalog➊,
	➀category : some Category➀,
	➃images : set Image➃
}

➃sig Image {}➃

➀➌fact OneCategory {
	category in Item -> one Category
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

fun catalogs [i : Item] : set Catalog {
	-- The following is not being handled correctly in the amalgamated: the neutral element of the
	-- outside plus should be none and not univ
	➊i.catalog➊+➀i.category.(➋inside➋+➁^inside➁) & ➁Catalog➁➀
}

run {} with exactly ➊,➋,➌,➍,➎
run {} with exactly ➀
run {} with exactly ➀,➁
run {} with exactly ➀,➂
run {} with exactly ➀,➁,➂
run {} with exactly ➀,➁,➂,➃
run {} with exactly ➀,➁,➂,➃,➄

assert AllCataloged {
	all i : Item | some catalogs[i] and catalogs[i] in Catalog
}

-- The following check is giving a counter-example because of the above bug
-- It should not give counter-examples
check AllCataloged for 10
