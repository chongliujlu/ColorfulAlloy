module Ecommerce

/*
 * ➀ Categories
 * ➁ Hierarchical categories
 * ➂ Multiple categories
 * ➃ Thumbnails
 * ➄ OnSale
*/

fact FeatureModel {
    ➁➊some none➊➁ -- Hierarchical requires Categories
    ➂➊some none➊➂ -- Multiple requires Categories
}

sig Product {
    ➊catalog : one Catalog➊,
    ➀➂category : some Category➂➀,
    ➀➌category : one Category➌➀,
    images : set Image
}
➄sig onSale in Product {}➄

sig Image {}

sig Catalog {
    ➃thumbnails : set Image➃
}

➀➁sig Category {
    inside : one Catalog+Category
}➁➀
➀➋sig Category {
    inside : one Catalog
}➋➀

➀➁fact Acyclic {
    all c : Category | c not in c.^inside
}➁➀

➃fact Thumbnails {
    all c : Catalog | c.thumbnails in (➀category.((➋inside➋+➁^inside➁).c)➀+➊catalog.c➊).images
}➃

➃➄fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃

fun catalogs [p : Product] : set Catalog {
    ➊p.catalog➊+➀p.category.(➋inside➋+➁^inside➁) & ➁Catalog➁➀
}


pred Scenario{
    some Product.images and ➀all c : Category | lone category.c➀
}
assert AllCataloged {
    all p:Product | some catalogs[p]
}
check AllCataloged for 10
check AllCataloged with exactly ➊,➋,➌,➍,➎ for 10
check AllCataloged with exactly ➀ for 10
check AllCataloged with exactly ➃ for 10
check AllCataloged with exactly ➄ for 10
check AllCataloged with exactly ➃,➄ for 10
check AllCataloged with exactly ➀,➁ for 10
check AllCataloged with exactly ➀,➂ for 10
check AllCataloged with exactly ➀,➃ for 10
check AllCataloged with exactly ➀,➄ for 10
check AllCataloged with exactly ➀,➃,➄ for 10
check AllCataloged with exactly ➀,➁,➂ for 10
check AllCataloged with exactly ➀,➁,➃ for 10
check AllCataloged with exactly ➀,➁,➄ for 10
check AllCataloged with exactly ➀,➁,➃,➄ for 10
check AllCataloged with exactly ➀,➂,➃ for 10
check AllCataloged with exactly ➀,➂,➄ for 10
check AllCataloged with exactly ➀,➂,➃,➄ for 10
check AllCataloged with exactly ➀,➁,➂,➃ for 10
check AllCataloged with exactly ➀,➁,➂,➄ for 10
check AllCataloged with exactly ➀,➁,➂,➃,➄ for 10
check AllCataloged for 11
check AllCataloged with exactly ➊,➋,➌,➍,➎ for 11
check AllCataloged with exactly ➀ for 11
check AllCataloged with exactly ➃ for 11
check AllCataloged with exactly ➄ for 11
check AllCataloged with exactly ➃,➄ for 11
check AllCataloged with exactly ➀,➁ for 11
check AllCataloged with exactly ➀,➂ for 11
check AllCataloged with exactly ➀,➃ for 11
check AllCataloged with exactly ➀,➄ for 11
check AllCataloged with exactly ➀,➃,➄ for 11
check AllCataloged with exactly ➀,➁,➂ for 11
check AllCataloged with exactly ➀,➁,➃ for 11
check AllCataloged with exactly ➀,➁,➄ for 11
check AllCataloged with exactly ➀,➁,➃,➄ for 11
check AllCataloged with exactly ➀,➂,➃ for 11
check AllCataloged with exactly ➀,➂,➄ for 11
check AllCataloged with exactly ➀,➂,➃,➄ for 11
check AllCataloged with exactly ➀,➁,➂,➃ for 11
check AllCataloged with exactly ➀,➁,➂,➄ for 11
check AllCataloged with exactly ➀,➁,➂,➃,➄ for 11
check AllCataloged for 12
check AllCataloged with exactly ➊,➋,➌,➍,➎ for 12
check AllCataloged with exactly ➀ for 12
check AllCataloged with exactly ➃ for 12
check AllCataloged with exactly ➄ for 12
check AllCataloged with exactly ➃,➄ for 12
check AllCataloged with exactly ➀,➁ for 12
check AllCataloged with exactly ➀,➂ for 12
check AllCataloged with exactly ➀,➃ for 12
check AllCataloged with exactly ➀,➄ for 12
check AllCataloged with exactly ➀,➃,➄ for 12
check AllCataloged with exactly ➀,➁,➂ for 12
check AllCataloged with exactly ➀,➁,➃ for 12
check AllCataloged with exactly ➀,➁,➄ for 12
check AllCataloged with exactly ➀,➁,➃,➄ for 12
check AllCataloged with exactly ➀,➂,➃ for 12
check AllCataloged with exactly ➀,➂,➄ for 12
check AllCataloged with exactly ➀,➂,➃,➄ for 12
check AllCataloged with exactly ➀,➁,➂,➃ for 12
check AllCataloged with exactly ➀,➁,➂,➄ for 12
check AllCataloged with exactly ➀,➁,➂,➃,➄ for 12
