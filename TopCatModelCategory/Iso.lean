module

public import Mathlib.CategoryTheory.Iso

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C]

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp] lemma isIso_comp_left_iff [IsIso f] : IsIso (f ≫ g) ↔ IsIso g :=
  ⟨fun _ ↦ IsIso.of_isIso_comp_left f g, fun _ ↦ inferInstance⟩

@[simp] lemma isIso_comp_right_iff [IsIso g] : IsIso (f ≫ g) ↔ IsIso f :=
  ⟨fun _ ↦ IsIso.of_isIso_comp_right f g, fun _ ↦ inferInstance⟩

end CategoryTheory
