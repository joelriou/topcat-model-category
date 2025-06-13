import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace IsPushout

/-- Same as `IsPushout.of_iso`, but using the data and compatibilities involve
the inverse isomorphisms instead. -/
lemma of_iso' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z' ≅ Z) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : P' ≅ P)
    (commf : e₁.hom ≫ f = f' ≫ e₂.hom)
    (commg : e₁.hom ≫ g = g' ≫ e₃.hom)
    (comminl : e₂.hom ≫ inl = inl' ≫ e₄.hom)
    (comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom) :
    IsPushout f' g' inl' inr' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminl, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminr, Iso.inv_hom_id_assoc]

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

lemma exists_desc (sq : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) :
    ∃ (d : P ⟶ W), inl ≫ d = h ∧ inr ≫ d = k :=
  ⟨sq.desc h k w, by simp, by simp⟩

noncomputable def isColimitBinaryCofan (sq : IsPushout f g inl inr) (hZ : IsInitial Z) :
    IsColimit (BinaryCofan.mk inl inr) :=
  BinaryCofan.IsColimit.mk _ (fun {U} s t ↦ sq.desc s t (hZ.hom_ext _ _))
    (by simp) (by simp) (fun s t m h₁ h₂ ↦ by apply sq.hom_ext <;> simpa)

end IsPushout

namespace IsPullback

variable {P X Y Z : C} {t : P ⟶ X} {l : P ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}

lemma exists_lift (sq : IsPullback t l r b)
    {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ r = k ≫ b) :
    ∃ (d : W ⟶ P), d ≫ t = h ∧ d ≫ l = k :=
  ⟨sq.lift h k w, by simp, by simp⟩

end IsPullback

end CategoryTheory
