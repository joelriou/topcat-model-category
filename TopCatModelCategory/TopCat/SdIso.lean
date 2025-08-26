import TopCatModelCategory.SemiSimplexCategory
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.AffineMap

universe u

open CategoryTheory

namespace SimplexCategory

noncomputable abbrev sdToTop : CosimplicialObject TopCat.{u} :=
  sd ⋙ SSet.toTop

end SimplexCategory

namespace SemiSimplexCategory

@[simps!]
def toTop : SemiCosimplicialObject TopCat.{u} :=
  CosimplicialObject.toSemiCosimplicialObject SimplexCategory.toTop.{u}

noncomputable def sdToTop : SemiCosimplicialObject TopCat.{u} :=
  SimplexCategory.sdToTop.toSemiCosimplicialObject

def sdIso : sdToTop.{u} ≅ toTop := sorry

end SemiSimplexCategory
