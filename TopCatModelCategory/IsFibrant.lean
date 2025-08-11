import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)

lemma isCofibrant_iff (X : C) :
    IsCofibrant X ↔ Cofibration (initial.to X) := Iff.rfl

variable [(cofibrations C).RespectsIso]

lemma isCofibrant_iff_of_isInitial {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)

lemma isFibrant_iff (X : C) :
    IsFibrant X ↔ Fibration (terminal.from X) := Iff.rfl

variable [(fibrations C).RespectsIso]

lemma isFibrant_iff_of_isTerminal {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

lemma isFibrant_of_iso {X Y : C} (e : X ≅ Y)
    [hX : IsFibrant X] :
    IsFibrant Y := by
  rw [isFibrant_iff, fibration_iff] at hX ⊢
  exact ((fibrations C).arrow_mk_iso_iff (Arrow.isoMk e (Iso.refl _))).1 hX

end

end HomotopicalAlgebra
