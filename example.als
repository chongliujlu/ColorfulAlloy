fact FeatureModel {
	➁➊some none➊➁
	➂➊some none➊➂
	}
sig Product{
        ➀category:  set Category➀,
        images:  set Image,
        ➊➋➌catalog:  one Catalog➌➋➊
        }
sig Image{ }


sig Catalog{
        thumbnails:  set Image
        }


➀sig Category{
        inside:  one (➀Catalog➀ + ➀➁Category➁➀)
        }➀

fact Acyclic{
        ➀➁all  c :  one Category |  c  !in  c . ^(inside)➁➀
        }
fact Thumbnails{
        ➊➋➌all  c :  one Catalog |  c .thumbnails in catalog. c .images➌➋➊   and ➀all  c :  one Catalog |  c .thumbnails in category.(➋inside➋ & ➁ ^(inside)➁). c .images   ➀
        }
pred Scenario{
        some Product.images   and ➀ some Category➀
        }
assert AllCataloged{
        ➀➁all  p :  one Product |  some ( p .category. ^(inside) & Catalog)➁➀
        }


check AllCataloged for 10

fact RemoveQualtifier{
        ➀all  s :  one Product | ➌ one  s .category➌   and ➂ some  s .category➂   ➀
        }







