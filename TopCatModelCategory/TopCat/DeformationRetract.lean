import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.Topology.UnitInterval
import TopCatModelCategory.TopCat.Monoidal

universe u

open CategoryTheory MonoidalCategory ChosenFiniteProducts

namespace TopCat

variable (X Y : TopCat.{u})

structure DeformationRetract extends Retract X Y where
  h : Y ⊗ I ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i := by aesop_cat
  h₀ : ι₀ ≫ h = r ≫ i := by aesop_cat
  h₁ : ι₁ ≫ h = 𝟙 Y := by aesop_cat

def deformationRetracts : MorphismProperty TopCat.{u} := fun _ _ f ↦
  ∃ (h : DeformationRetract _ _), h.i = f

end TopCat
