fact FeatureModel {
	➁➊some none➊➁
	➂➊some none➊➂
	}
➊➋➌sig Product {
 	catalog : one Catalog ,
    	images : set Image
    	}➌➋➊
➀➋➌sig Product {
    	category : one Category ,
    	images : set Image
    	}➌➋➀
➀➁➌sig Product {
     	category : one Category ,
    	images : set Image
   	 }➌➁➀
➀➋➂ sig Product {
     	category : some Category ,
    	 images : set Image
    	}➂➋➀
➀➁➂sig Product {
     	category : some Category ,
    	 images : set Image
    	}➂➁➀
➊➋➌sig Image {}➌➋➊
➀➋➌sig Image {}➌➋➀
➀➁➌sig Image {}➌➁➀
➀➋➂ sig Image {}➂➋➀
➀➁➂sig Image {}➂➁➀
➊➋➌sig Catalog {
	thumbnails : set Image
	}➌➋➊
➀➋➌sig Catalog {
	thumbnails : set Image
	}➌➋➀
➀➁➌sig Catalog {
	thumbnails : set Image
	}➌➁➀
➀➋➂ sig Catalog {
	thumbnails : set Image
	}➂➋➀
➀➁➂sig Catalog {
	thumbnails: set Image
	}➂➁➀
➀➋➌ sig Category {
	inside : one Catalog
    } ➌➋➀
➀➁➌sig Category {
	inside : one Catalog + Category
	}➌➁➀
➀➋➂ sig Category {
	inside : one Catalog
	} ➂➋➀
➀➁➂sig Category {
	inside : one Catalog + Category
	}➂➁➀
➀➁➌fact Acyclic {
    	all c : Category | c not in c.^inside
    }➌➁➀
➀➁➂fact Acyclic {
   	all c : Category | c not in c.^inside
	}➂➁➀
➊➋➌fact Thumbnails{
   	all c : Catalog | c.thumbnails in catalog.c.images
	}➌➋➊
➀➋➌fact Thumbnails{
     	all c : Catalog | c.thumbnails in (category.inside.c).images
	}➌➋➀
➀➁➌fact Thumbnails{
     	all c : Catalog | c.thumbnails in (category.( ^inside ).c).images
	}➌➁➀
➀➋➂ fact Thumbnails{
     	all c : Catalog | c.thumbnails in (category. inside.c).images
	}➂➋➀
➀➁➂fact Thumbnails{
     	all c : Catalog | c. thumbnails in (category.( ^inside ).c).images
	}➂➁➀
➊➋➌pred Scenario {
	some Product.images
	}➌➋➊
➀➋➌pred Scenario {
	some Product.images
	some Category
	}➌➋➀
➀➁➌pred Scenario {
	some Product.images
	some Category
	}➌➁➀
➀➋➂pred Scenario {
	some Product.images
	some Category
	}➂➋➀
➀➁➂pred Scenario {
	some Product.images
	some Category
	}➂➁➀
➊➋➌assert AllCataloged {}➌➋➊
➀➋➌assert AllCataloged {}➌➋➀
➀➁➌assert AllCataloged {
	all p:Product | some (p.category.^inside & Catalog)
	}➌➁➀
➀➋➂assert AllCataloged {}➂➋➀
➀➁➂assert AllCataloged {
 	all p: Product | some (p.category.^inside & Catalog)
	}➂➁➀
run Scenario with ➊,➋,➌ for 10
run Scenario with ➀,➋,➌ for 10
run Scenario with ➀,➁,➌ for 10
run Scenario with ➀,➋,➂ for 10
run Scenario with ➀,➁,➂ for 10
check AllCataloged with ➀,➁,➌ for 10
check AllCataloged with ➀,➁,➂ for 10

