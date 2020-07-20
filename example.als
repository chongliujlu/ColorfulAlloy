fact FeatureModel {
	➁➊some none➊➁
	➂➊some none➊➂
	}
➀➁sig Product{
        category:  set Category,
        images:  set Image
        }➁➀
➋➌sig Product{
        ➀category:  one Category➀,
        images:  set Image,
        ➊catalog:  one Catalog➊
        }➌➋
➋➀➂sig Product{
        category:  some Category,
        images:  set Image
        }➂➀➋

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



fact RemoveMultiplicity {
        ➀➁➂all s:Product | some s.category➂➁➀
        ➀➌➁all s:Product | one s.category➁➌➀
        }