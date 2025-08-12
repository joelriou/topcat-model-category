import TopCatModelCategory.SSet.KanComplexWHomotopy
import TopCatModelCategory.SSet.KanComplexWRetracts
import TopCatModelCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SingularSet

universe u

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen

namespace TopCat

namespace modelCategory

instance : CategoryWithWeakEquivalences TopCat.{u} where
  weakEquivalences := SSet.KanComplex.W.inverseImage TopCat.toSSet

lemma weakEquivalences_eq :
    weakEquivalences TopCat = SSet.KanComplex.W.inverseImage TopCat.toSSet := rfl

lemma weakEquivalence_iff {X Y : TopCat} (f : X ⟶ Y) :
    WeakEquivalence f ↔ SSet.KanComplex.W (TopCat.toSSet.map f) := by
  rw [HomotopicalAlgebra.weakEquivalence_iff, weakEquivalences_eq,
    MorphismProperty.inverseImage_iff]

instance : (weakEquivalences TopCat).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (weakEquivalences TopCat).IsStableUnderRetracts := by
  rw [weakEquivalences_eq]
  infer_instance

end modelCategory

end TopCat
