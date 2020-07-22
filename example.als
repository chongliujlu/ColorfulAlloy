fact FeatureModel {
	➁➊some none➊➁
	➂➊some none➊➂
	}
sig    Product{
        ➀➋➌category:  one Category➌➋➀,
        images:  set Image,
        ➊➋➌catalog:  one Catalog➌➋➊,
        ➀➁➌category:  one Category➌➁➀,
        ➂category:  some Category➂
        }


➀➂sig Image{ }➂➀
➋➌sig Image{ }➌➋
➀➌➁sig Image{ }➁➌➀

➀➂sig Catalog{
        thumbnails:  set Image
        }➂➀
➀➌➁sig Catalog{
        thumbnails:  set Image
        }➁➌➀
➋➌sig Catalog{
        thumbnails:  set Image
        }➌➋

➀sig Category{
        inside:  one ((➋➂Catalog➂➋ + (➁➂Catalog + Category➂➁)) + (➌➋Catalog➋ + (➁Catalog + Category➁)➌))
        }➀

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











