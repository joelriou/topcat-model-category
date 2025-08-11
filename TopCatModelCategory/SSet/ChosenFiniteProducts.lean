import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Opposite

namespace SSet

variable (X Y : SSet.{u})

@[simp]
lemma fst_app {n : SimplexCategoryᵒᵖ} (z : (X ⊗ Y).obj n) : (fst X Y).app _ z = z.1 := rfl

@[simp]
lemma snd_app {n : SimplexCategoryᵒᵖ} (z : (X ⊗ Y).obj n) : (snd X Y).app _ z = z.2 := rfl

instance : BraidedCategory SSet.{u} := .ofCartesianMonoidalCategory

end SSet
