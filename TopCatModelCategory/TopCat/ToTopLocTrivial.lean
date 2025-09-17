import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.TrivialBundleOver
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.ModelCategoryTopCat

universe u

open Simplicial CategoryTheory MorphismProperty HomotopicalAlgebra
  TopCat.modelCategory

namespace SSet

variable {E B : SSet.{u}} (p : E ⟶ B) {F : SSet.{u}}
  (τ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ)

include τ
lemma fibration_toTop_map_of_trivialBundle_over_simplices :
    Fibration (toTop.map p) := by
  have := τ
  sorry

end SSet
