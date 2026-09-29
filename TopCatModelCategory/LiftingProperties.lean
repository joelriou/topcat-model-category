module

public import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] public section

namespace CategoryTheory

-- #28489
/-
variable {C : Type*} [Category C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

def HasLiftingPropertyFixedTop (t : A ⟶ X) : Prop :=
  ∀ (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift-/

end CategoryTheory
