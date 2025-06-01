import TopCatModelCategory.SSet.CategoryWithWeakEquivalences

open CategoryTheory HomotopicalAlgebra

namespace SSet.modelCategoryQuillen

lemma weakEquivalence_iff_of_fibration
    {X Y : SSet.{0}} (p : X ⟶ Y) [Fibration p] :
    I.rlp p ↔ WeakEquivalence p :=
  sorry

end SSet.modelCategoryQuillen
