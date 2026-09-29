module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C]
  {W₁ W₂ W₁' W₂' : MorphismProperty C}
  (le₁ : W₁ ≤ W₁') (le₂ : W₂ ≤ W₂')

lemma hasFunctorialFactorization_of_le [HasFunctorialFactorization W₁ W₂]
    (le₁ : W₁ ≤ W₁') (le₂ : W₂ ≤ W₂') :
    HasFunctorialFactorization W₁' W₂' :=
  ⟨⟨(functorialFactorizationData W₁ W₂).ofLE le₁ le₂⟩⟩

end MorphismProperty

end CategoryTheory
