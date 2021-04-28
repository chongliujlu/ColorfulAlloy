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
➊➋➌➍➎sig Product {
    catalog : one Catalog,
    images : set Image
}➎➍➌➋➊
➊➋➌➍➎sig Image {}➎➍➌➋➊
➊➋➌➍➎sig Catalog {}➎➍➌➋➊
➊➋➌➍➎fun catalogs [p : Product] : set Catalog {
    p.catalog
}➎➍➌➋➊
➊➋➌➍➎pred Scenario{
    some Product.images
}➎➍➌➋➊
➊➋➌➍➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➍➌➋➊

--➀➋➌➍➎   ➎➍➌➋➀ --➀
➀➋➌➍➎sig Product {
    category : one Category,
    images : set Image
}➎➍➌➋➀
➀➋➌➍➎sig Image {}➎➍➌➋➀
➀➋➌➍➎sig Catalog {}➎➍➌➋➀
➀➋➌➍➎sig Category {
    inside : one Catalog
}➎➍➌➋➀
➀➋➌➍➎fun catalogs [p : Product] : set Catalog {
p.category.inside
}➎➍➌➋➀
➀➋➌➍➎pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➍➌➋➀
➀➋➌➍➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➍➌➋➀

--➊➋➌➃➎    ➎➃➌➋➊--➃
➊➋➌➃➎ sig Product {
    catalog : one Catalog,
    images : set Image
}➎➃➌➋➊
➊➋➌➃➎ sig Image {}➎➃➌➋➊
➊➋➌➃➎ sig Catalog {
    thumbnails : set Image
}➎➃➌➋➊
➊➋➌➃➎ fact Thumbnails {
    all c : Catalog | c.thumbnails in catalog.c.images
}➎➃➌➋➊
➊➋➌➃➎ fun catalogs [p : Product] : set Catalog {
    p.catalog
}➎➃➌➋➊
➊➋➌➃➎ pred Scenario{
    some Product.images 
}➎➃➌➋➊
➊➋➌➃➎ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➃➌➋➊

--➊➋➌➍➄    ➄➍➌➋➊--➄
➊➋➌➍➄sig Product {
    catalog : one Catalog,
    images : set Image
}➄➍➌➋➊
➊➋➌➍➄sig onSale in Product{}➄➍➌➋➊
➊➋➌➍➄sig Image {}➄➍➌➋➊
➊➋➌➍➄sig Catalog {}➄➍➌➋➊
➊➋➌➍➄fun catalogs [p : Product] : set Catalog {
    p.catalog
}➄➍➌➋➊
➊➋➌➍➄pred Scenario{
    some Product.images 
}➄➍➌➋➊
➊➋➌➍➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➍➌➋➊

--➀➁➌➍➎   ➎➍➌➁➀
➀➁➌➍➎sig Product {
    category : one Category,
    images : set Image
}➎➍➌➁➀
➀➁➌➍➎sig Image {}➎➍➌➁➀
➀➁➌➍➎sig Catalog {}➎➍➌➁➀
➀➁➌➍➎sig Category {
    inside : one Catalog+Category
}➎➍➌➁➀
➀➁➌➍➎fact Acyclic {
    all c : Category | c not in c.^inside
}➎➍➌➁➀
➀➁➌➍➎fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➎➍➌➁➀
➀➁➌➍➎pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➍➌➁➀
➀➁➌➍➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➍➌➁➀

--➀➋➂➍➎    ➎➍➂➋➀
➀➋➂➍➎sig Product {
    category : some Category,
    images : set Image
}➎➍➂➋➀
➀➋➂➍➎sig Image {}➎➍➂➋➀
➀➋➂➍➎sig Catalog {}➎➍➂➋➀
➀➋➂➍➎sig Category {
    inside : one Catalog
}➎➍➂➋➀
➀➋➂➍➎fun catalogs [p : Product] : set Catalog {
    p.category.inside
}➎➍➂➋➀
➀➋➂➍➎pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➍➂➋➀
➀➋➂➍➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➍➂➋➀
--➀➋➌➃➎    ➎➃➌➋➀

➀➋➌➃➎sig Product {
    category : one Category,
    images : set Image
}➎➃➌➋➀
➀➋➌➃➎sig Image {}➎➃➌➋➀
➀➋➌➃➎sig Catalog {
    thumbnails : set Image
}➎➃➌➋➀
➀➋➌➃➎sig Category {
    inside : one Catalog
}➎➃➌➋➀
➀➋➌➃➎fact Thumbnails {
    all c : Catalog | c.thumbnails in category.(inside.c).images
}➎➃➌➋➀
➀➋➌➃➎fun catalogs [p : Product] : set Catalog {
    p.category.(inside) 
}➎➃➌➋➀
➀➋➌➃➎pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➃➌➋➀
➀➋➌➃➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➃➌➋➀
--➀➋➌➍➄    ➄➍➌➋➀

➀➋➌➍➄sig Product {
    category : one Category,
    images : set Image
}➄➍➌➋➀
➀➋➌➍➄sig onSale in Product{} ➄➍➌➋➀
➀➋➌➍➄sig Image {}➄➍➌➋➀
➀➋➌➍➄sig Catalog {}➄➍➌➋➀
➀➋➌➍➄sig Category {
    inside : one Catalog
}➄➍➌➋➀
➀➋➌➍➄fun catalogs [p : Product] : set Catalog {
    p.category.(inside)
}➄➍➌➋➀
➀➋➌➍➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➍➌➋➀
➀➋➌➍➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➍➌➋➀

--➊➋➌➃➄      ➄➃➌➋➊

➊➋➌➃➄sig Product {
    catalog : one Catalog,
    images : set Image
}➄➃➌➋➊
➊➋➌➃➄sig onSale in Product{}➄➃➌➋➊
➊➋➌➃➄sig Image {}➄➃➌➋➊
➊➋➌➃➄sig Catalog {
    thumbnails : set Image
}➄➃➌➋➊
➊➋➌➃➄fact Thumbnails {
    all c : Catalog | c.thumbnails in (catalog.c).images
}➄➃➌➋➊
➊➋➌➃➄fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃➌➋➊
➊➋➌➃➄fun catalogs [p : Product] : set Catalog {
    p.catalog
}➄➃➌➋➊
➊➋➌➃➄pred Scenario{
    some Product.images 
}➄➃➌➋➊
➊➋➌➃➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➃➌➋➊

--➀➁➂➍➎      ➎➍➂➁➀
➀➁➂➍➎sig Product {
    category : some Category,
    images : set Image
}➎➍➂➁➀
➀➁➂➍➎sig Image {}➎➍➂➁➀
➀➁➂➍➎sig Catalog {}➎➍➂➁➀
➀➁➂➍➎sig Category {
    inside : one Catalog+Category
}➎➍➂➁➀
➀➁➂➍➎fact Acyclic {
    all c : Category | c not in c.^inside
}➎➍➂➁➀
➀➁➂➍➎fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➎➍➂➁➀
➀➁➂➍➎pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➍➂➁➀
➀➁➂➍➎assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➍➂➁➀

--➀➁➌➃➎   ➎➃➌➁➀
➀➁➌➃➎ sig Product {
    category : one Category,
    images : set Image
}➎➃➌➁➀
➀➁➌➃➎ sig Image {}➎➃➌➁➀
➀➁➌➃➎ sig Catalog {
    thumbnails : set Image
}➎➃➌➁➀
➀➁➌➃➎ sig Category {
    inside : one Catalog+Category
}➎➃➌➁➀
➀➁➌➃➎ fact Acyclic {
    all c : Category | c not in c.^inside
}➎➃➌➁➀
➀➁➌➃➎ fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.((^inside).c)).images
}➎➃➌➁➀
➀➁➌➃➎ fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➎➃➌➁➀
➀➁➌➃➎ pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➃➌➁➀
➀➁➌➃➎ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➃➌➁➀

--➀➁➌➍➄     ➄➍➌➁➀
➀➁➌➍➄sig Product {
    category : one Category,
    images : set Image
}➄➍➌➁➀
➀➁➌➍➄sig onSale in Product {}➄➍➌➁➀
➀➁➌➍➄sig Image {}➄➍➌➁➀
➀➁➌➍➄sig Catalog {}➄➍➌➁➀
➀➁➌➍➄sig Category {
    inside : one Catalog+Category
}➄➍➌➁➀
➀➁➌➍➄fact Acyclic {
    all c : Category | c not in c.^inside
}➄➍➌➁➀
➀➁➌➍➄fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➄➍➌➁➀
➀➁➌➍➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➍➌➁➀
➀➁➌➍➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➍➌➁➀

--➀➋➂➃➎    ➎➃➂➋➀
➀➋➂➃➎ sig Product {
    ➀➂category : some Category➂➀,
    images : set Image
}➎➃➂➋➀
➀➋➂➃➎ sig Image {}➎➃➂➋➀
➀➋➂➃➎ sig Catalog {
    thumbnails : set Image
}➎➃➂➋➀
➀➋➂➃➎ sig Category {
    inside : one Catalog
}➎➃➂➋➀
➀➋➂➃➎ fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.(inside.c)).images
}➎➃➂➋➀
➀➋➂➃➎ fun catalogs [p : Product] : set Catalog {
    p.category.inside 
}➎➃➂➋➀
➀➋➂➃➎ pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➃➂➋➀
➀➋➂➃➎ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➃➂➋➀

--➀➋➂➍➄   ➄➍➂➋➀
➀➋➂➍➄sig Product {
    category : some Category,
    images : set Image
}➄➍➂➋➀
➀➋➂➍➄sig onSale in Product {}➄➍➂➋➀
➀➋➂➍➄sig Image {}➄➍➂➋➀
➀➋➂➍➄sig Catalog {}➄➍➂➋➀
➀➋➂➍➄sig Category {
    inside : one Catalog
}➄➍➂➋➀
➀➋➂➍➄fun catalogs [p : Product] : set Catalog {
    p.category.inside 
}➄➍➂➋➀
➀➋➂➍➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➍➂➋➀
➀➋➂➍➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➍➂➋➀

--➀➋➌➃➄     ➄➃➌➋➀
➀➋➌➃➄sig Product {
    category : one Category,
    images : set Image
}➄➃➌➋➀
➀➋➌➃➄sig onSale in Product{}➄➃➌➋➀
➀➋➌➃➄sig Image {}➄➃➌➋➀
➀➋➌➃➄sig Catalog {
    thumbnails : set Image
}➄➃➌➋➀
➀➋➌➃➄sig Category {
    inside : one Catalog
}➄➃➌➋➀
➀➋➌➃➄fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.(inside.c)).images
}➄➃➌➋➀
➀➋➌➃➄fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃➌➋➀
➀➋➌➃➄fun catalogs [p : Product] : set Catalog {
    p.category.(inside) 
}➄➃➌➋➀
➀➋➌➃➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➃➌➋➀
➀➋➌➃➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➃➌➋➀

--➀➁➂➃➎   ➎➃➂➁➀
➀➁➂➃➎ sig Product {
    category : some Category,
    images : set Image
}➎➃➂➁➀
➀➁➂➃➎ sig Image {}➎➃➂➁➀
➀➁➂➃➎ sig Catalog {
    thumbnails : set Image
}➎➃➂➁➀
➀➁➂➃➎ sig Category {
    inside : one Catalog+Category
}➎➃➂➁➀
➀➁➂➃➎ fact Acyclic {
    all c : Category | c not in c.^inside
}➎➃➂➁➀
➀➁➂➃➎ fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.((^inside).c)).images
}➎➃➂➁➀
➀➁➂➃➎ fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➎➃➂➁➀
➀➁➂➃➎ pred Scenario{
    some Product.images and all c : Category | lone category.c
}➎➃➂➁➀

➀➁➂➃➎ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➎➃➂➁➀

--➀➁➂➍➄   ➄➍➂➁➀
➀➁➂➍➄ sig Product {
    category : some Category,
    images : set Image
}➄➍➂➁➀
➀➁➂➍➄ sig onSale in Product {}➄➍➂➁➀
➀➁➂➍➄ sig Image {}➄➍➂➁➀
➀➁➂➍➄ sig Catalog {}➄➍➂➁➀
➀➁➂➍➄ sig Category {
    inside : one Catalog+Category
}➄➍➂➁➀

➀➁➂➍➄ fact Acyclic {
    all c : Category | c not in c.^inside
}➄➍➂➁➀
➀➁➂➍➄ fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➄➍➂➁➀
➀➁➂➍➄ pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➍➂➁➀
➀➁➂➍➄ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➍➂➁➀

--➀➁➌➃➄   ➄➃➌➁➀
➀➁➌➃➄sig Product {
    category : one Category,
    images : set Image
}➄➃➌➁➀
➀➁➌➃➄sig onSale in Product{}➄➃➌➁➀
➀➁➌➃➄sig Image {}➄➃➌➁➀
➀➁➌➃➄sig Catalog {
    thumbnails : set Image
}➄➃➌➁➀
➀➁➌➃➄sig Category {
    inside : one Catalog+➁Category➁
}➄➃➌➁➀
➀➁➌➃➄fact Acyclic {
    all c : Category | c not in c.^inside
}➄➃➌➁➀
➀➁➌➃➄fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.((^inside).c)).images
}➄➃➌➁➀
➀➁➌➃➄fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃➌➁➀
➀➁➌➃➄fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➄➃➌➁➀
➀➁➌➃➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➃➌➁➀
➀➁➌➃➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➃➌➁➀

--➀➋➂➃➄     ➄➃➂➋➀
➀➋➂➃➄ sig Product {
    category : some Category,
    images : set Image
}➄➃➂➋➀
➀➋➂➃➄ sig onSale in Product {}➄➃➂➋➀
➀➋➂➃➄ sig Image {}➄➃➂➋➀
➀➋➂➃➄ sig Catalog {
    thumbnails : set Image
}➄➃➂➋➀
➀➋➂➃➄ sig Category {
    inside : one Catalog
}➄➃➂➋➀
➀➋➂➃➄ fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.(inside.c)).images
}➄➃➂➋➀
➀➋➂➃➄ fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃➂➋➀
➀➋➂➃➄ fun catalogs [p : Product] : set Catalog {
    p.category.inside
}➄➃➂➋➀
➀➋➂➃➄ pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➃➂➋➀
➀➋➂➃➄ assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➃➂➋➀

--➀➁➂➃➄    ➄➃➂➁➀
➀➁➂➃➄sig Product {
    category : some Category,
    images : set Image
}➄➃➂➁➀
➀➁➂➃➄sig onSale in Product{}➄➃➂➁➀
➀➁➂➃➄sig Image {}➄➃➂➁➀
➀➁➂➃➄sig Catalog {
    thumbnails : set Image
}➄➃➂➁➀
➀➁➂➃➄sig Category {
    inside : one Catalog+Category
}➄➃➂➁➀
➀➁➂➃➄fact Acyclic {
    all c : Category | c not in c.^inside
}➄➃➂➁➀
➀➁➂➃➄fact Thumbnails {
    all c : Catalog | c.thumbnails in (category.((^inside).c)).images
}➄➃➂➁➀
➀➁➂➃➄fact OnSaleThumbnails {
    all p: onSale, c: catalogs[p]| some p.images & c.thumbnails
}➄➃➂➁➀
➀➁➂➃➄fun catalogs [p : Product] : set Catalog {
    p.category.(^inside) & Catalog
}➄➃➂➁➀
➀➁➂➃➄pred Scenario{
    some Product.images and all c : Category | lone category.c
}➄➃➂➁➀
➀➁➂➃➄assert AllCataloged { 
    all p:Product | some catalogs[p] 
}➄➃➂➁➀
check AllCataloged with exactly ➊,➋,➌,➍,➎ for 8
check AllCataloged with exactly ➀,➋,➌,➍,➎ for 8
check AllCataloged with exactly ➃,➊,➋,➌,➎ for 8
check AllCataloged with exactly ➄,➊,➋,➌,➍ for 8
check AllCataloged with exactly ➃,➄,➊,➋,➌ for 8
check AllCataloged with exactly ➀,➁,➌,➍,➎ for 8
check AllCataloged with exactly ➀,➂,➋,➍,➎ for 8
check AllCataloged with exactly ➀,➃,➋,➌,➎ for 8
check AllCataloged with exactly ➀,➄,➋,➌,➍ for 8
check AllCataloged with exactly ➀,➃,➄,➋,➌ for 8
check AllCataloged with exactly ➀,➁,➂,➍,➎ for 8
check AllCataloged with exactly ➀,➁,➃,➌,➎ for 8
check AllCataloged with exactly ➀,➁,➄,➌,➍ for 8
check AllCataloged with exactly ➀,➁,➃,➄,➌ for 8
check AllCataloged with exactly ➀,➂,➃,➋,➎ for 8
check AllCataloged with exactly ➀,➂,➄,➋,➍ for 8
check AllCataloged with exactly ➀,➂,➃,➄,➋ for 8
check AllCataloged with exactly ➀,➁,➂,➃,➎ for 8
check AllCataloged with exactly ➀,➁,➂,➄,➍ for 8
check AllCataloged with exactly ➀,➁,➂,➃,➄ for 8




