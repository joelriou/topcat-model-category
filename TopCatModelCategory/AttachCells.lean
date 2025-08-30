import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-import Mathlib.CategoryTheory.MorphismProperty.Limits

universe w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} (j : ∀ i, A i ⟶ B i)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

structure AttachCells where
  ι : Type w
  π : ι → α
  cofan₁ : Cofan (fun i ↦ A (π i))
  cofan₂ : Cofan (fun i ↦ B (π i))
  isColimit₁ : IsColimit cofan₁
  isColimit₂ : IsColimit cofan₂
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = j (π i) ≫ cofan₂.inj i := by aesop_cat
  g₁ : cofan₁.pt ⟶ X₁
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

attribute [reassoc (attr := simp)] hm

variable {j f} (c : AttachCells.{w} j f)

include c

lemma pushouts_coproducts : (coproducts.{w} (ofHoms j)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ ↦ by exact j (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ ↦ by rw [IsColimit.fac]; exact c.hm i)
  rw [this, coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i ↦ ⟨_⟩⟩⟩

def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂

lemma cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂ := rfl

lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : ∀ i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

section

variable {α' : Type t'} {A' B' : α' → C} (j' : ∀ i', A' i' ⟶ B' i')
  (a : α → α') (ha : ∀ (i : α), Arrow.mk (j i) ≅ Arrow.mk (j' (a i)))

def chg : AttachCells j' f where
  ι := c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i ↦ Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i ↦ Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i ↦ A (c.π i)) ≅
        Discrete.functor (fun i ↦ A' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.leftFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₁ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocones.precompose, e, Cofan.inj]
  isColimit₂ := by
    let e : Discrete.functor (fun i ↦ B (c.π i)) ≅
        Discrete.functor (fun i ↦ B' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.rightFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₂ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocones.precompose, e, Cofan.inj]
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

end

end AttachCells

open MorphismProperty in
lemma nonempty_attachCells_iff :
    Nonempty (AttachCells.{w} j f) ↔ (coproducts.{w} (ofHoms j)).pushouts f := by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
    rw [coproducts_iff, ← hm'] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (j (π i)) :=
      eqToIso (((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose_spec)
    let e₁ (i : ι) : F₁.obj ⟨i⟩ ≅ A (π i) := Arrow.leftFunc.mapIso (e i)
    let e₂ (i : ι) : F₂.obj ⟨i⟩ ≅ B (π i) := Arrow.rightFunc.mapIso (e i)
    exact ⟨{
        ι := ι
        π := π
        cofan₁ := Cofan.mk c₁.pt (fun i ↦ (e₁ i).inv ≫ c₁.ι.app ⟨i⟩)
        cofan₂ := Cofan.mk c₂.pt (fun i ↦ (e₂ i).inv ≫ c₂.ι.app ⟨i⟩)
        isColimit₁ :=
          (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₁ i)) _).1
            (IsColimit.ofIsoColimit h₁ (Cocones.ext (Iso.refl _) (by simp)))
        isColimit₂ :=
          (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₂ i)) _).1
            (IsColimit.ofIsoColimit h₂ (Cocones.ext (Iso.refl _) (by simp)))
        hm i := by
          have eq₁ := c₁.ι.app ⟨i⟩ ≫= hm'
          have eq₂ := (e i).inv.w
          rw [IsColimit.fac] at eq₁
          dsimp [e₁, e₂] at eq₁ eq₂ ⊢
          rw [Category.assoc, ← eq₁, reassoc_of% eq₂]
        isPushout := sq }⟩

end HomotopicalAlgebra-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

namespace AttachCells

variable {C D : Type*} [Category C] [Category D]
  {α : Type*} {A B : α → C} {g : ∀ a, A a ⟶ B a}
  {X Y : C} {f : X ⟶ Y} (hf : AttachCells g f)
  (F : C ⥤ D)
  [PreservesColimit (Discrete.functor (fun i ↦ A (hf.π i))) F]
  [PreservesColimit (Discrete.functor (fun i ↦ B (hf.π i))) F]
  [PreservesColimit (span hf.g₁ hf.m) F]

@[simps]
noncomputable def map : AttachCells (g := fun a ↦ F.map (g a)) (F.map f) where
  ι := hf.ι
  π := hf.π
  cofan₁ := Cofan.mk _ (fun i ↦ F.map (hf.cofan₁.inj i))
  cofan₂ := Cofan.mk _ (fun i ↦ F.map (hf.cofan₂.inj i))
  isColimit₁ := (isColimitMapCoconeCofanMkEquiv _ _ _).1 (isColimitOfPreserves F hf.isColimit₁)
  isColimit₂ := (isColimitMapCoconeCofanMkEquiv _ _ _).1 (isColimitOfPreserves F hf.isColimit₂)
  m := F.map hf.m
  hm i := by simp [← Functor.map_comp]
  g₁ := F.map hf.g₁
  g₂ := F.map hf.g₂
  isPushout := hf.isPushout.map F

end AttachCells

end HomotopicalAlgebra
