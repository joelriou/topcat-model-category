module

public import TopCatModelCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

@[expose] public section

universe w v u

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

instance : IsStableUnderTransfiniteComposition.{w} (trivialCofibrations C) := by
  rw [← fibrations_llp]
  infer_instance

instance : IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
  rw [← trivialFibrations_llp]
  infer_instance

instance : IsStableUnderCoproducts.{w} (trivialCofibrations C) := by
  rw [← fibrations_llp]
  infer_instance

instance : IsStableUnderCoproducts.{w} (cofibrations C) := by
  rw [← trivialFibrations_llp]
  infer_instance

end HomotopicalAlgebra
