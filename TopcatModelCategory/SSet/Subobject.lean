/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf


/-!
# Subobjects of simplicial sets

-/

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)

instance : CompleteLattice (Subpresheaf P) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h|h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h|h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map := sorry }
  le_sSup := sorry
  sSup_le := sorry
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map := sorry }
  sInf_le := sorry
  le_sInf := sorry
  bot :=
    { obj U := ⊥
      map := by simp }
  le_top _ _ := le_top
  bot_le _ _ := bot_le

lemma sSup_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iSup S).obj U = iSup (fun i ↦ (S i).obj U) := by
  simp [iSup, sSup_obj]

end CategoryTheory.GrothendieckTopology

namespace SSet

variable (X Y : SSet.{u})

protected abbrev Subobject := GrothendieckTopology.Subpresheaf X

namespace Subobject

variable {X Y}

variable (S : X.Subobject) (T : Y.Subobject)

instance : CoeOut X.Subobject SSet.{u} where
  coe := fun S ↦ S.toPresheaf

variable {S} in
@[ext]
lemma coe_ext {Δ : SimplexCategoryᵒᵖ} {x y : S.obj Δ} (h : x.val = y.val) : x = y :=
  Subtype.ext h

abbrev ι : (S : SSet.{u}) ⟶ X := GrothendieckTopology.Subpresheaf.ι S

@[simp]
lemma ι_app {Δ : SimplexCategoryᵒᵖ} (x : S.obj Δ) :
    S.ι.app Δ x = x.val := rfl

instance : Mono S.ι := by
  change Mono (GrothendieckTopology.Subpresheaf.ι S)
  infer_instance

@[simps]
noncomputable def prod : (X ⊗ Y).Subobject where
  obj Δ := (S.obj Δ).prod (T.obj Δ)
  map i _ hx := ⟨S.map i hx.1, T.map i hx.2⟩

lemma prod_monotone {S₁ S₂ : X.Subobject} (hX : S₁ ≤ S₂) {T₁ T₂ : Y.Subobject} (hY : T₁ ≤ T₂) :
    S₁.prod T₁ ≤ S₂.prod T₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

example : PartialOrder X.Subobject := inferInstance
example : SemilatticeSup X.Subobject := inferInstance

section

variable {S₁ S₂ : X.Subobject} (h : S₁ ≤ S₂)

def homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u}) := GrothendieckTopology.Subpresheaf.homOfLe h

@[simp]
lemma homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ) :
    ((homOfLE h).app Δ x).val = x.val := rfl

@[reassoc (attr := simp)]
lemma homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι := rfl

instance : Mono (homOfLE h) := mono_of_mono_fac (homOfLE_ι h)

end

noncomputable def unionProd : (X ⊗ Y).Subobject := ((⊤ : X.Subobject).prod T) ⊔ (S.prod ⊤)

lemma top_prod_le_unionProd : (⊤ : X.Subobject).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_top_prod : S.prod T ≤ (⊤ : X.Subobject).prod T :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top : S.prod T ≤ S.prod ⊤ :=
  prod_monotone (by rfl) le_top

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

end Subobject

def subobjectBoundary (n : ℕ) : (Δ[n] : SSet.{u}).Subobject where
  obj _ s := ¬Function.Surjective (asOrderHom s)
  map φ s hs := ((boundary n).map φ ⟨s, hs⟩).2

lemma subobjectBoundary_toSSet (n : ℕ) : subobjectBoundary.{u} n = ∂Δ[n] := rfl

lemma subobjectBoundary_ι (n : ℕ) :
    (subobjectBoundary.{u} n).ι = boundaryInclusion n := rfl

def subobjectHorn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subobject where
  obj _ s := Set.range (asOrderHom s) ∪ {i} ≠ Set.univ
  map φ s hs := ((horn n i).map φ ⟨s, hs⟩).2

lemma subobjectHorn_toSSet (n : ℕ) (i : Fin (n + 1)) :
    subobjectHorn.{u} n i = Λ[n, i] := rfl

lemma subobjectHorn_ι (n : ℕ) (i : Fin (n + 1)) :
    (subobjectHorn.{u} n i).ι = hornInclusion n i := rfl

section

variable {X Y}
variable (f : X ⟶ Y)

attribute [local simp] FunctorToTypes.naturality

@[simps]
def Subobject.image : Y.Subobject where
  obj Δ := Set.range (f.app Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, rfl⟩
    exact ⟨X.map φ x, by simp⟩

def toImageSubobject : X ⟶ Subobject.image f where
  app Δ x := ⟨f.app Δ x, ⟨x, rfl⟩⟩

@[simp]
lemma toImageSubobject_apply_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    ((toImageSubobject f).app Δ x).val = f.app Δ x := rfl

@[reassoc (attr := simp)]
lemma toImageSubobject_ι : toImageSubobject f ≫ (Subobject.image f).ι = f := rfl

end

end SSet