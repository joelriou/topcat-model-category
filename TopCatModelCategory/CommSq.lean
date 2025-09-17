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

namespace IsPullback

variable {C : Type*} [Category C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b)
  {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄} (sq' : IsPullback t' l' r' b')
  (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
  (commr : r ≫ e₄.hom = e₂.hom ≫ r') (commb : b ≫ e₄.hom = e₃.hom ≫ b')

include sq sq' commr commb
lemma exists_iso_of_isos :
    ∃ (e₁ : X₁ ≅ Y₁), t ≫ e₂.hom = e₁.hom ≫ t' ∧
      l ≫ e₃.hom = e₁.hom ≫ l' :=
   ⟨{ hom := sq'.lift (t ≫ e₂.hom) (l ≫ e₃.hom)
        (by simp only [Category.assoc, ← commr, sq.w_assoc, commb])
      inv := sq.lift (t' ≫ e₂.inv) (l' ≫ e₃.inv)
        (by simp only [Category.assoc, ← cancel_mono e₄.hom, commr,
          Iso.inv_hom_id_assoc, sq'.w, commb])
      hom_inv_id := by apply sq.hom_ext <;> simp
      inv_hom_id := by apply sq'.hom_ext <;> simp}, by simp, by simp⟩

noncomputable def isoOfIsos : X₁ ≅ Y₁ :=
  (sq.exists_iso_of_isos sq' e₂ e₃ e₄ commr commb).choose

@[reassoc (attr := simp)]
lemma isoOfIsos_hom_comm₁ :
    (isoOfIsos sq sq' e₂ e₃ e₄ commr commb).hom ≫ t' = t ≫ e₂.hom :=
  (sq.exists_iso_of_isos sq' e₂ e₃ e₄ commr commb).choose_spec.1.symm

@[reassoc (attr := simp)]
lemma isoOfIsos_hom_comm₂ :
    (isoOfIsos sq sq' e₂ e₃ e₄ commr commb).hom ≫ l' = l ≫ e₃.hom :=
  (sq.exists_iso_of_isos sq' e₂ e₃ e₄ commr commb).choose_spec.2.symm

end IsPullback

namespace IsPushout

variable {C : Type*} [Category C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPushout t l r b)
  {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄} (sq' : IsPushout t' l' r' b')
  (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
  (commt : t ≫ e₂.hom = e₁.hom ≫ t') (comml : l ≫ e₃.hom = e₁.hom ≫ l')

include sq sq' commt comml
lemma exists_iso_of_isos :
    ∃ (e₄ : X₄ ≅ Y₄), r ≫ e₄.hom = e₂.hom ≫ r' ∧
      b ≫ e₄.hom = e₃.hom ≫ b' :=
   ⟨{ hom := sq.desc (e₂.hom ≫ r') (e₃.hom ≫ b')
        (by simp only [reassoc_of% comml, reassoc_of% commt, sq'.w])
      inv := sq'.desc (e₂.inv ≫ r) (e₃.inv ≫ b)
        (by
          simp only [← cancel_epi e₁.hom, ← reassoc_of% commt, Iso.hom_inv_id_assoc,
            ← reassoc_of% comml, sq.w])
      hom_inv_id := by apply sq.hom_ext <;> simp
      inv_hom_id := by apply sq'.hom_ext <;> simp }, by simp, by simp⟩

end IsPushout

namespace IsPullback

variable {D : Type*} [Category D]
  {P X₁ X₂ S : C} {t : P ⟶ X₁} {l : P ⟶ X₂} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (sq : IsPullback t l f₁ f₂)
  (F : C ⥤ D)
  {Q : D} {t' : Q ⟶ F.obj X₁} {l' : Q ⟶ F.obj X₂}
  (sq' : IsPullback t' l' (F.map f₁) (F.map f₂))

include sq sq' in
lemma preservesLimit_of_iso (e : F.obj P ≅ Q) (he₁ : e.hom ≫ t' = F.map t)
    (he₂ : e.hom ≫ l' = F.map l) :
    PreservesLimit (cospan f₁ f₂) F :=
  preservesLimit_of_preserves_limit_cone sq.isLimit
    ((PullbackCone.isLimitMapConeEquiv _ _).2
      (IsLimit.ofIsoLimit sq'.isLimit
        (PullbackCone.ext e he₁.symm he₂.symm).symm))

include sq sq' in
lemma isIso_of_preservesLimit (φ : F.obj P ⟶ Q) (he₁ : φ ≫ t' = F.map t)
    (he₂ : φ ≫ l' = F.map l) [PreservesLimit (cospan f₁ f₂) F] : IsIso φ := by
  let e := (sq.map F).isLimit.conePointUniqueUpToIso sq'.isLimit
  suffices e.hom = φ by rw [← this]; infer_instance
  apply sq'.hom_ext
  · rw [he₁]
    exact (sq.map F).isLimit.conePointUniqueUpToIso_hom_comp sq'.isLimit .left
  · rw [he₂]
    exact (sq.map F).isLimit.conePointUniqueUpToIso_hom_comp sq'.isLimit .right

end IsPullback

end CategoryTheory
