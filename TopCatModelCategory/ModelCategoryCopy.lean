module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import TopCatModelCategory.MorphismProperty

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

namespace ModelCategory

variable {C : Type*} [Category C]

def copy [cof : CategoryWithCofibrations C]
    [fib : CategoryWithFibrations C] [W : CategoryWithWeakEquivalences C]
    (h : ModelCategory C) (h₁ : cofibrations C = h.categoryWithCofibrations.cofibrations)
    (h₂ : fibrations C = h.categoryWithFibrations.fibrations)
    (h₃ : weakEquivalences C = h.categoryWithWeakEquivalences.weakEquivalences) :
    ModelCategory C := by
  have h₄ : trivialCofibrations C = h.categoryWithCofibrations.cofibrations ⊓
      h.categoryWithWeakEquivalences.weakEquivalences := by
    rw [trivialCofibrations, h₁, h₃]
  have h₅ : trivialFibrations C = h.categoryWithFibrations.fibrations ⊓
    h.categoryWithWeakEquivalences.weakEquivalences := by
    rw [trivialFibrations, h₂, h₃]
  exact {
    cm2 := by rw [h₃]; exact h.cm2
    cm3a := by rw [h₃]; exact h.cm3a
    cm3b := by rw [h₂]; exact h.cm3b
    cm3c := by rw [h₁]; exact h.cm3c
    cm4a i p _ _ _ := by
      refine @h.cm4a _ _ _ _ i p ?_ ?_ ?_
      · rw [cofibration_iff]
        change h.categoryWithCofibrations.cofibrations _
        rwa [← h₁, ← cofibration_iff]
      · rw [weakEquivalence_iff]
        change h.categoryWithWeakEquivalences.weakEquivalences _
        rwa [← h₃, ← weakEquivalence_iff]
      · rw [fibration_iff]
        change h.categoryWithFibrations.fibrations _
        rwa [← h₂, ← fibration_iff]
    cm4b i p _ _ _ := by
      refine @h.cm4b _ _ _ _ i p ?_ ?_ ?_
      · rw [cofibration_iff]
        change h.categoryWithCofibrations.cofibrations _
        rwa [← h₁, ← cofibration_iff]
      · rw [fibration_iff]
        change h.categoryWithFibrations.fibrations _
        rwa [← h₂, ← fibration_iff]
      · rw [weakEquivalence_iff]
        change h.categoryWithWeakEquivalences.weakEquivalences _
        rwa [← h₃, ← weakEquivalence_iff]
    cm5a := by rw [h₄, h₂]; exact h.cm5a
    cm5b := by rw [h₅, h₁]; exact h.cm5b }

end ModelCategory

end HomotopicalAlgebra
