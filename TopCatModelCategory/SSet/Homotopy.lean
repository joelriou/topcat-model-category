import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.Monoidal
import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Horn

open HomotopicalAlgebra CategoryTheory Category Simplicial MonoidalCategory Opposite
  ChosenFiniteProducts Limits SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex} {φ : (A : SSet) ⟶ (B : SSet)}

namespace Subcomplex

variable (A B φ)

noncomputable def relativeMorphism : ((ihom X).obj Y).Subcomplex :=
  Subcomplex.fiber ((MonoidalClosed.pre A.ι).app Y)
    (ihom₀Equiv.symm (φ ≫ B.ι))

lemma range_le_relativeMorphism_iff {T : SSet.{u}} (f : T ⟶ (ihom X).obj Y) :
    range f ≤ relativeMorphism A B φ ↔
      f ≫ (MonoidalClosed.pre A.ι).app Y = const (ihom₀Equiv.symm (φ ≫ B.ι)) := by
  apply range_le_fiber_iff

@[reassoc (attr := simp)]
lemma relativeMorphism_ι_comp_pre_app :
    (relativeMorphism A B φ).ι ≫ (MonoidalClosed.pre A.ι).app Y =
      const (ihom₀Equiv.symm (φ ≫ B.ι)) := by
  simp [relativeMorphism]

instance [IsFibrant Y] :
    IsFibrant (C := SSet.{u}) (relativeMorphism A B φ) := by
  dsimp [relativeMorphism]
  infer_instance

variable {A B φ}

namespace RelativeMorphism

@[simps]
noncomputable def equiv :
    RelativeMorphism A B φ ≃ (relativeMorphism A B φ : SSet.{u}) _⦋0⦌ where
  toFun f := ⟨ihom₀Equiv.symm f.map, by
    dsimp [relativeMorphism, fiber]
    rw [ofSimplex_obj₀, Set.mem_preimage, Set.mem_singleton_iff, ← f.comm,
      ihom₀Equiv_symm_comp]⟩
  invFun g :=
    { map := ihom₀Equiv g.1
      comm := by
        have := g.2
        simp [relativeMorphism, fiber] at this
        apply ihom₀Equiv.symm.injective
        rw [← this, ihom₀Equiv_symm_comp, Equiv.symm_apply_apply] }
  left_inv _ := by aesop
  right_inv _ := by aesop

namespace Homotopy

noncomputable def equiv {f g : RelativeMorphism A B φ} :
    Homotopy f g ≃ KanComplex.FundamentalGroupoid.Edge (X := relativeMorphism A B φ)
        (.mk (RelativeMorphism.equiv f))
        (.mk (RelativeMorphism.equiv g)) where
  toFun h := KanComplex.FundamentalGroupoid.Edge.mk
      (Subcomplex.lift (MonoidalClosed.curry h.h) (by
        rw [← top_le_iff, ← Subcomplex.image_le_iff, Subcomplex.image_top,
          range_le_relativeMorphism_iff, MonoidalClosed.curry_pre_app, h.rel]
        rfl)) (by
        rw [← cancel_mono (Subpresheaf.ι _), assoc, Subcomplex.lift_ι, const_comp,
          Subpresheaf.ι_app, equiv_apply_coe, ← h.h₀,
          ← MonoidalClosed.curry_natural_left, ← stdSimplex.rightUnitor_hom_ι₀, assoc]
        rfl) (by
        rw [← cancel_mono (Subpresheaf.ι _), assoc, Subcomplex.lift_ι, const_comp,
          Subpresheaf.ι_app, equiv_apply_coe, ← h.h₁,
          ← MonoidalClosed.curry_natural_left, ← stdSimplex.rightUnitor_hom_ι₁, assoc]
        rfl)
  invFun h :=
    { h := MonoidalClosed.uncurry (h.map ≫ Subpresheaf.ι _)
      h₀ := by
        rw [← cancel_epi (stdSimplex.rightUnitor X).hom,
          stdSimplex.rightUnitor_hom_ι₀_assoc,
          MonoidalClosed.uncurry_natural_left,
          ← MonoidalCategory.whiskerLeft_comp_assoc, h.comm₀]
        rfl
      h₁ := by
        rw [← cancel_epi (stdSimplex.rightUnitor X).hom,
          stdSimplex.rightUnitor_hom_ι₁_assoc,
          MonoidalClosed.uncurry_natural_left,
          ← MonoidalCategory.whiskerLeft_comp_assoc, h.comm₁]
        rfl
      rel := by
        rw [MonoidalClosed.whiskerRight_comp_uncurry, assoc,
          relativeMorphism_ι_comp_pre_app]
        rfl }
  left_inv h := by aesop
  right_inv h := by aesop

noncomputable def symm {f g : RelativeMorphism A B φ}
    (hfg : Homotopy f g) [IsFibrant Y] : Homotopy g f := by
  apply Nonempty.some
  obtain ⟨h, _⟩ := KanComplex.FundamentalGroupoid.homMk_surjective
    (Groupoid.inv (KanComplex.FundamentalGroupoid.homMk (equiv hfg)))
  exact ⟨equiv.symm h⟩

noncomputable def trans {f₁ f₂ f₃ : RelativeMorphism A B φ}
    (h₁₂ : Homotopy f₁ f₂) (h₂₃ : Homotopy f₂ f₃) [IsFibrant Y] : Homotopy f₁ f₃ :=
  equiv.symm ((equiv h₁₂).comp (equiv h₂₃))

variable (A B φ) in
lemma equivalence [IsFibrant Y] :
    _root_.Equivalence (α := RelativeMorphism A B φ)
      (fun f g ↦ Nonempty (Homotopy f g)) where
  refl _ := ⟨refl _⟩
  symm h := ⟨h.some.symm⟩
  trans h₁₂ h₂₃ := ⟨h₁₂.some.trans h₂₃.some⟩

end Homotopy

noncomputable def Homotopy.of_eq {f g : RelativeMorphism A B φ} [IsFibrant Y]
    (h : f.homotopyClass = g.homotopyClass) : Homotopy f g :=
  ((Equivalence.quot_mk_eq_iff (Homotopy.equivalence A B φ) _ _).1 h).some

@[simps]
def botEquiv :
    RelativeMorphism (⊥ : X.Subcomplex) (⊥ : Y.Subcomplex)
      (botIsInitial.to _) ≃ (X ⟶ Y) where
  toFun f := f.map
  invFun f := { map := f }
  left_inv _ := rfl
  right_inv _ := rfl

end RelativeMorphism

end Subcomplex

def Homotopy (f g : X ⟶ Y) := (Subcomplex.RelativeMorphism.botEquiv.symm f).Homotopy
      (Subcomplex.RelativeMorphism.botEquiv.symm g)

namespace Homotopy

variable {f g : X ⟶ Y}

section

variable (h : Homotopy f g)

@[reassoc (attr := simp)]
lemma h₀ : ι₀ ≫ h.h = f :=
  Subcomplex.RelativeMorphism.Homotopy.h₀ h

@[reassoc (attr := simp)]
lemma h₁ : ι₁ ≫ h.h = g :=
  Subcomplex.RelativeMorphism.Homotopy.h₁ h

end

@[simps h]
def mk (h : X ⊗ Δ[1] ⟶ Y) (h₀ : ι₀ ≫ h = f) (h₁ : ι₁ ≫ h = g) : Homotopy f g where
  h := h
  rel := by
    ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx

@[simps! h]
def congr (h : Homotopy f g) {f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    Homotopy f' g' :=
  mk h.h (by aesop) (by aesop)

@[simps! h]
noncomputable def whiskerRight (h : Homotopy f g) (Z : SSet.{u}) :
    Homotopy (f ▷ Z) (g ▷ Z) :=
  mk ((α_ _ _ _).hom ≫ X ◁ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ h.h ▷ Z)
    (by simp only [← h.h₀]; rfl) (by simp only [← h.h₁]; rfl)

@[simps! h]
noncomputable def whiskerLeft (h : Homotopy f g) (Z : SSet.{u}) :
    Homotopy (Z ◁ f) (Z ◁ g) :=
  mk ((α_ _ _ _).hom ≫ Z ◁ h.h)
    (by simp only [← h.h₀]; rfl) (by simp only [← h.h₁]; rfl)

end Homotopy

end SSet
