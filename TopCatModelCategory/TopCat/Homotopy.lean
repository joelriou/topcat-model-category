import TopCatModelCategory.TopCat.Monoidal
import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.TopCat.ToTopExact

universe u

open CategoryTheory Limits MonoidalCategory Opposite Simplicial CartesianMonoidalCategory

lemma CategoryTheory.Limits.IsTerminal.isIso
    {C : Type*} [Category C] {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y)
    (f : X ⟶ Y) : IsIso f :=
  ⟨hX.from _, hX.hom_ext _ _, hY.hom_ext _ _⟩

namespace TopCat

variable {X Y : TopCat.{u}} (f g : X ⟶ Y)

structure Homotopy where
  h : X ⊗ I ⟶ Y
  h₀ : ι₀ ≫ h = f := by aesop_cat
  h₁ : ι₁ ≫ h = g := by aesop_cat

variable {f g}

open Functor.Monoidal

-- see also `TopCat.Adj` for the same definition for deformation retracts
noncomputable def Homotopy.toSSet (h : Homotopy f g) :
    SSet.Homotopy (toSSet.map f) (toSSet.map g) where
  h := _ ◁ SSet.stdSimplex.toSSetObjI ≫ (μIso TopCat.toSSet _ _).hom ≫ TopCat.toSSet.map h.h
  rel := by
    rw [← cancel_epi (β_ _ _).hom]
    exact MonoidalClosed.curry_injective (by subsingleton)
  h₀ := by
    dsimp
    simpa only [sSetι₀_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map h.h₀
  h₁ := by
    dsimp
    simpa only [sSetι₁_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map h.h₁

end TopCat

namespace SSet

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

namespace stdSimplex

noncomputable def toTopObjIsoI : toTop.{u}.obj Δ[1] ≅ TopCat.I :=
  TopCat.isoOfHomeo toTopObjHomeoUnitInterval

@[simp]
lemma toTopObjIsoI_hom_toTopObjMk_zero :
    toTopObjIsoI.{u}.hom (toTopObjMk (stdSimplex.const _ 0 _)) = 0 := by
  simp [toTopObjIsoI]

@[simp]
lemma toTopObjIsoI_hom_toTopObjMk_one :
    toTopObjIsoI.{u}.hom (toTopObjMk (stdSimplex.const _ 1 _)) = 1 := by
  simp [toTopObjIsoI]

variable (X Y)

section

noncomputable def toTopTensorComparison :
    toTop.obj (X ⊗ Y) ⟶ toTop.obj X ⊗ toTop.obj Y :=
  CartesianMonoidalCategory.lift (toTop.map (fst _ _)) (toTop.map (snd _ _))

variable (n : SimplexCategory)

instance : IsIso (toTopTensorComparison X (stdSimplex.obj n)) := sorry

noncomputable def toTopTensorIso :
    toTop.obj (X ⊗ stdSimplex.obj n) ≅ toTop.obj X ⊗ toTop.obj (stdSimplex.obj n) :=
  asIso (toTopTensorComparison X (stdSimplex.obj n))

@[reassoc (attr := simp)]
lemma toTopTensorIso_hom_fst :
    (toTopTensorIso X n).hom ≫ fst _ _ = toTop.map (fst _ _) := by
  simp [toTopTensorIso, toTopTensorComparison]

@[reassoc (attr := simp)]
lemma toTopTensorIso_hom_snd :
    (toTopTensorIso X n).hom ≫ snd _ _ = toTop.map (snd _ _) := by
  simp [toTopTensorIso, toTopTensorComparison]

end

noncomputable def toTopTensorDeltaOneIso :
    toTop.obj (X ⊗ Δ[1]) ≅ toTop.obj X ⊗ TopCat.I :=
  toTopTensorIso X _ ≪≫ (Iso.refl _ ⊗ᵢ toTopObjIsoI)

@[reassoc (attr := simp)]
lemma ι₀_toTopTensorDeltaOneIso_inv :
    TopCat.ι₀ ≫ (toTopTensorDeltaOneIso X).inv = toTop.map ι₀ := by
  rw [← cancel_mono (toTopTensorDeltaOneIso X).hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp [toTopTensorDeltaOneIso]
  ext : 1
  · simp [← Functor.map_comp]
  · simp [← Functor.map_comp_assoc]
    ext x
    simp [TopCat.const]

@[reassoc (attr := simp)]
lemma ι₁_toTopTensorDeltaOneIso_inv :
    TopCat.ι₁ ≫ (toTopTensorDeltaOneIso X).inv = toTop.map ι₁ := by
  rw [← cancel_mono (toTopTensorDeltaOneIso X).hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp [toTopTensorDeltaOneIso]
  ext : 1
  · simp [← Functor.map_comp]
  · simp [← Functor.map_comp_assoc]
    ext x
    simp [TopCat.const]

end stdSimplex

protected noncomputable def Homotopy.toTop (h : Homotopy f g) :
    TopCat.Homotopy (toTop.map f) (toTop.map g) where
  h := (stdSimplex.toTopTensorDeltaOneIso X).inv ≫ toTop.map h.h
  h₀ := by simp only [stdSimplex.ι₀_toTopTensorDeltaOneIso_inv_assoc, ← Functor.map_comp, h.h₀]
  h₁ := by simp only [stdSimplex.ι₁_toTopTensorDeltaOneIso_inv_assoc, ← Functor.map_comp, h.h₁]

instance : IsIso (sSetTopAdj.{u}.unit.app Δ[0]) :=
  stdSimplex.isTerminalObj₀.isIso (by
    dsimp
    apply IsTerminal.isTerminalObj
    apply IsTerminal.isTerminalObj
    exact stdSimplex.isTerminalObj₀) _

noncomputable def Contractible.toSSetToTop {X : SSet.{u}} (h : Contractible X) :
    Contractible (TopCat.toSSet.obj (SSet.toTop.obj X)) where
  pt := (sSetTopAdj.unit.app X).app _ h.pt
  h :=
    { h := h.h.toTop.toSSet.h
      h₀ := by
        simp only [Subcomplex.RelativeMorphism.Homotopy.h₀,
          Subcomplex.RelativeMorphism.botEquiv_symm_apply_map, Functor.id_obj,
          Functor.comp_obj]
        let α : X ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from X
        let β : Δ[0] ⟶ X := const h.pt
        have hβ : TopCat.toSSet.map (toTop.map β) =
            const (((sSetTopAdj.unit.app X).app (op ⦋0⦌) h.pt)) := by
          have : Epi (sSetTopAdj.{u}.unit.app Δ[0]) := by infer_instance
          have := sSetTopAdj.unit.naturality β
          dsimp at this ⊢
          simp [← cancel_epi (sSetTopAdj.unit.app Δ[0]), ← this, β]
        rw [show (const h.pt : X ⟶ X) = α ≫ β by rfl,
          Functor.map_comp, Functor.map_comp, hβ, comp_const] }

instance (X : SSet.{u}) [X.IsContractible] :
    (TopCat.toSSet.obj (SSet.toTop.obj X)).IsContractible :=
  ⟨Contractible.toSSetToTop (Classical.arbitrary _)⟩

end SSet
