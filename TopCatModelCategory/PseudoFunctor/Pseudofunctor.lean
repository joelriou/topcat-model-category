module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.CatCommSq

@[expose] public section

universe w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory

namespace CommSq

variable {B : Type*} [Category B]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
    {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
    (sq : CommSq t l m b) (sq' : CommSq t' m r b')
    {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
    (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

include ht hb sq sq'

lemma horiz_comp' : CommSq t'' l r b'' := by
  subst ht hb
  exact sq.horiz_comp sq'

end CommSq

namespace Pseudofunctor

section

variable {B C : Type*} [Bicategory B] [Bicategory C] (F : Pseudofunctor B C)

/-
/-- More flexible variant of `mapId`. -/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by aesop_cat) :
    F.map f ≅ 𝟙 _ :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. -/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : fg = f ≫ g := by aesop_cat) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']
-/
end

section

variable {B C : Type*} [Bicategory B] [Bicategory C]
  [IsLocallyDiscrete B]
  (F : Pseudofunctor B C)

lemma mapComp'_comp_id {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' f (𝟙 b₁) f (by nth_rw 1 [Category.comp_id f]) =
    (ρ_ _).symm ≪≫ whiskerLeftIso _ (F.mapId b₁).symm := by
  ext
  dsimp [mapComp']
  rw [mapComp_id_right_hom, Subsingleton.elim (ρ_ f).hom (eqToHom (by simp)),
    ← Category.assoc, ← PrelaxFunctor.map₂_comp, eqToHom_trans, eqToHom_refl,
    F.map₂_id, Category.id_comp]

lemma mapComp'_id_comp {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' (𝟙 b₀) f f (by nth_rw 1 [Category.id_comp f]) =
      (λ_ _).symm ≪≫ whiskerRightIso (F.mapId b₀).symm _ := by
  ext
  dsimp [mapComp']
  rw [mapComp_id_left_hom, Subsingleton.elim ((λ_ f).hom) (eqToHom (by simp)),
    ← Category.assoc, ← PrelaxFunctor.map₂_comp, eqToHom_trans, eqToHom_refl,
    F.map₂_id, Category.id_comp]

@[reassoc]
lemma mapComp'_assoc {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
    (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃)
    (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (f : b₀ ⟶ b₃)
    (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f hf).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom =
      (F.mapComp' f₀₂ f₂₃ f (by rw [← hf, ← h₀₂, ← h₁₃, Category.assoc])).hom ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp, mapComp'_eq_mapComp,
    mapComp_assoc_right_hom,
    Subsingleton.elim (α_ f₀₁ f₁₂ f₂₃).inv (eqToHom (by simp)),
    mapComp']
  simp

@[reassoc]
lemma mapComp'_inv_mapComp'_hom {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
    (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃)
    (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂ ) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃ ) (f : b₀ ⟶ b₃)
    (hf : f₀₁ ≫ f₁₃ = f) :
      (F.mapComp' f₀₁ f₁₃ f hf).inv ≫
        (F.mapComp' f₀₂ f₂₃ f (by rw [← hf, ← h₀₂, ← h₁₃, Category.assoc])).hom =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
        (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f hf).hom, Iso.hom_inv_id_assoc,
    F.mapComp'_assoc_assoc _ _ _ _ _ h₀₂ h₁₃ _ hf]
  simp

@[reassoc]
lemma mapComp'_hom_whiskerRight_mapComp'_hom {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
    (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃)
    (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃)
    (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂ ) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃) (f : b₀ ⟶ b₃)
    (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f (by rw [← hf, ← h₀₂, ← h₁₃, Category.assoc])).hom ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ =
    (F.mapComp' f₀₁ f₁₃ f hf).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'_assoc_assoc _ _ _ _ _ h₀₂ h₁₃ f hf]
  simp

section

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B}

section

variable {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

def isoMapOfSq : F.map t ≫ F.map r ≅ F.map l ≫ F.map b :=
  (F.mapComp t r).symm ≪≫ F.mapComp' _ _ _ (by rw [sq.w])

lemma isoMapOfSq_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) :
    F.isoMapOfSq sq =
    (F.mapComp' t r φ (by rw [hφ])).symm ≪≫
      F.mapComp' l b φ (by rw [← hφ, sq.w]) := by
  subst hφ
  simp [isoMapOfSq, mapComp'_eq_mapComp]

end

lemma isoMapOfSq_horiz_id (f : X₁ ⟶ X₂) :
    F.isoMapOfSq (t := 𝟙 _) (b := 𝟙 _) (l := f) (r := f) ⟨by simp⟩ =
        whiskerRightIso (F.mapId X₁) (F.map f) ≪≫
        λ_ _  ≪≫ (ρ_ _).symm ≪≫
        (whiskerLeftIso (F.map f) (F.mapId X₂)).symm := by
  ext
  rw [isoMapOfSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

section

variable {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
    {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
    (sq : CommSq t l m b) (sq' : CommSq t' m r b')
    {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
    (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

include ht hb sq sq'

lemma isoMapOfSq_horiz_comp :
    F.isoMapOfSq (sq.horiz_comp' sq' ht hb) =
      whiskerRightIso (F.mapComp' t t' t'' (by rw [← ht])) (F.map r) ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso (F.map t) (F.isoMapOfSq sq') ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso (F.isoMapOfSq sq) (F.map b') ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso (F.map l)
        ((F.mapComp' b b' b'' (by rw [← hb])).symm) := by
  ext
  obtain ⟨φ, hφ⟩ : ∃ φ, t ≫ m = φ := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, t' ≫ r = ψ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, t ≫ ψ = δ := ⟨_, rfl⟩
  have hδ' : t'' ≫ r = δ := by rw [← hδ, ← hψ, reassoc_of% ht]
  rw [F.isoMapOfSq_eq ((sq.horiz_comp' sq' ht hb)) δ hδ',
    F.isoMapOfSq_eq sq' ψ hψ, F.isoMapOfSq_eq sq φ hφ]
  dsimp
  simp only [Bicategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [← F.mapComp'_inv_mapComp'_hom_assoc _ _ _ _ _ _ _ _ hδ,
    F.mapComp'_hom_whiskerRight_mapComp'_hom_assoc _ _ _ _ _ _ hb _
      (by rw [← hδ, ← hψ, ← hb, sq'.w, sq.w_assoc]),
    Iso.inv_hom_id_assoc, whiskerLeft_hom_inv, Category.comp_id,
    ← cancel_epi (F.mapComp' t'' r δ hδ').hom,
    F.mapComp'_hom_whiskerRight_mapComp'_hom_assoc _ _ _ _ ψ ht hψ _ hδ,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc,
    Iso.hom_inv_id_assoc]

end

end

end

section

variable {B : Type u₁} [Category.{v₁} B]
  (F : Pseudofunctor (LocallyDiscrete B) Cat.{v₂, u₂})

section

variable {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂}
  (sq : CommSq t l r b)

def isoMapOfSq' : F.map ⟨t⟩ ≫ F.map ⟨r⟩ ≅ F.map ⟨l⟩ ≫ F.map ⟨b⟩ :=
  isoMapOfSq _ ⟨congr_arg Quiver.Hom.toLoc sq.w⟩

@[simps]
def catCommSqOfSq :
    CatCommSq (F.map ⟨t⟩) (F.map ⟨l⟩) (F.map ⟨r⟩) (F.map ⟨b⟩) :=
  ⟨F.isoMapOfSq' sq⟩

lemma isoMapOfSq'_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) :
    F.isoMapOfSq' sq =
    (F.mapComp' ⟨t⟩ ⟨r⟩ ⟨φ⟩ (by subst hφ; rfl)).symm ≪≫
      F.mapComp' ⟨l⟩ ⟨b⟩ ⟨φ⟩ (by rw [← hφ, sq.w]; rfl) :=
  isoMapOfSq_eq _ ⟨congr_arg Quiver.Hom.toLoc sq.w⟩ _
    (congr_arg Quiver.Hom.toLoc hφ)

end

section

variable {X Y : B} (f : X ⟶ Y)

lemma isoMapOfSq'_horiz_id :
    F.isoMapOfSq' (t := 𝟙 _) (b := 𝟙 _) (l := f) (r := f) ⟨by simp⟩ =
        Functor.isoWhiskerRight (F.mapId ⟨X⟩) (F.map ⟨f⟩) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
        (Functor.isoWhiskerLeft (F.map ⟨f⟩) (F.mapId ⟨Y⟩)).symm := by
  apply isoMapOfSq_horiz_id

end

section

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
    {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
    (sq : CommSq t l m b) (sq' : CommSq t' m r b')
    {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
    (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

include ht hb sq sq'

lemma isoMapOfSq'_horiz_comp :
    F.isoMapOfSq' (sq.horiz_comp' sq' ht hb) =
      Functor.isoWhiskerRight (F.mapComp' ⟨t⟩ ⟨t'⟩ ⟨t''⟩ (by rw [← ht]; rfl)) (F.map ⟨r⟩) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.map ⟨t⟩) (F.isoMapOfSq' sq') ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (F.isoMapOfSq' sq) (F.map ⟨b'⟩) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.map ⟨l⟩)
        ((F.mapComp' ⟨b⟩ ⟨b'⟩ ⟨b''⟩ (by rw [← hb]; rfl)).symm) :=
  isoMapOfSq_horiz_comp _ _ _ (by rw [← ht]; rfl) (by rw [← hb]; rfl)

end

end

end Pseudofunctor

end CategoryTheory
