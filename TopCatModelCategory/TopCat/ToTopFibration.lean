import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.ModelCategoryTopCat

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  TopCat.modelCategory

namespace SSet

instance {E B : SSet} (p : E ⟶ B) [Fibration p] :
    Fibration (toTop.map p) := sorry

end SSet
