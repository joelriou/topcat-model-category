import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SingularSet
import TopCatModelCategory.TopCat.W
import TopCatModelCategory.TopCat.T1Inclusion
import TopCatModelCategory.TopCat.DeformationRetract
import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Skeleton

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial NNReal Limits MonoidalCategory Opposite

scoped [Simplicial] notation "|" X "|" => SSet.toTop.obj X

namespace SSet

def uliftFunctor₀IsoId : uliftFunctor.{0, 0} ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦
    NatIso.ofComponents (fun n ↦ Equiv.ulift.toIso))

noncomputable def stdSimplexCompToTopIso :
    stdSimplex ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  isoWhiskerRight (isoWhiskerLeft _ uliftFunctor₀IsoId ≪≫
    Functor.rightUnitor _ ) _ ≪≫ SSet.toTopSimplex

instance : toTop.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint

instance {J : Type*} [LinearOrder J] :
    PreservesWellOrderContinuousOfShape J SSet.toTop where
end SSet

namespace SimplexCategory

open SSet

noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.obj n| ≃ₜ n.toTopObj :=
  TopCat.homeoOfIso (stdSimplexCompToTopIso.app n)

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.toFun.comp (SSet.toTop.map (stdSimplex.map f)) =
    (toTopMap f).comp n.toTopHomeo := by
  ext x : 1
  exact congr_fun ((forget _).congr_map
    (stdSimplexCompToTopIso.hom.naturality f)) x

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.map (stdSimplex.map f) x)) =
      (toTopMap f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.invFun.comp (toTopMap f) =
      (SSet.toTop.map (stdSimplex.map f)).hom.1.comp n.toTopHomeo.invFun := by
  ext x : 1
  exact congr_fun ((forget _).congr_map
    (stdSimplexCompToTopIso.inv.naturality f)) x

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : n.toTopObj) :
    m.toTopHomeo.symm (toTopMap f x) =
      SSet.toTop.map (stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

namespace TopCat

instance : toSSet.IsRightAdjoint := sSetTopAdj.isRightAdjoint

@[simps symm_apply]
def toSSetObj₀Equiv {X : TopCat.{0}} :
    toSSet.obj X _⦋0⦌ ≃ X where
  toFun f := f.hom.1 (default : ⦋0⦌.toTopObj)
  invFun x := ofHom ⟨fun _ ↦ x, by continuity⟩
  left_inv _ := by
    apply ConcreteCategory.hom_ext
    intro (x : ⦋0⦌.toTopObj)
    obtain rfl := Subsingleton.elim x default
    rfl
  right_inv _ := rfl

@[simp]
lemma toSSet_map_const (X : TopCat.{0}) {Y : TopCat.{0}} (y : Y) :
    toSSet.map (TopCat.const (X := X) y) =
      SSet.const (toSSetObj₀Equiv.symm y) :=
  rfl

end TopCat

noncomputable instance : Unique (|Δ[0]|) := ⦋0⦌.toTopHomeo.unique

lemma sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{0}}
    (f : |Δ[0]| ⟶ X) :
    sSetTopAdj.homEquiv Δ[0] X f =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (f default)) := by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) := by
    apply SSet.yonedaEquiv.injective
    apply TopCat.toSSetObj₀Equiv.injective
    apply Subsingleton.elim
  rw [Adjunction.homEquiv_unit, TopCat.toSSetObj₀Equiv_symm_apply, this]
  rfl

namespace SSet

section

variable (X : SSet.{0})

@[simps]
def functorFromElementsOp : X.Elementsᵒᵖ ⥤ SimplexCategory where
  obj e := e.unop.1.unop
  map f := f.unop.1.unop

@[simps]
noncomputable def coconeFromElementsOp :
    Cocone (X.functorFromElementsOp ⋙ stdSimplex) where
  pt := X
  ι :=
    { app e := yonedaEquiv.symm e.unop.2
      naturality _ _ f := by
        dsimp
        rw [← yonedaEquiv_symm_map]
        simp }

noncomputable def isColimitCoconeFromElementsOp : IsColimit X.coconeFromElementsOp := by
  let e : X.functorFromElementsOp ⋙ stdSimplex ≅ Presheaf.functorToRepresentables X :=
    NatIso.ofComponents (fun e ↦ uliftFunctor₀IsoId.app _)
  exact (IsColimit.precomposeInvEquiv e _).1 (Presheaf.colimitOfRepresentable X)

end

noncomputable def sigmaToTopObj (X : SSet) :
    (Σ (s : (Σ (n : ℕ), X.nonDegenerate n)), SimplexCategory.toTopObj (.mk s.1)) → |X| :=
  fun ⟨s, x⟩ ↦
    toTop.map (yonedaEquiv.symm s.2.1) ((SimplexCategory.toTopHomeo (.mk s.1)).symm x)

lemma continuous_sigmaToTopObj (X : SSet) : Continuous X.sigmaToTopObj := by
  apply continuous_sigma
  rintro s
  apply Continuous.comp
  · exact (toTop.map _).hom.2
  · apply Homeomorph.continuous_symm

lemma surjective_sigmaToTopObj (X : SSet) : Function.Surjective X.sigmaToTopObj := by
  intro x
  obtain ⟨⟨⟨n⟩, s⟩, x, rfl⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (SSet.toTop ⋙ forget _) X.isColimitCoconeFromElementsOp) x
  induction' n using SimplexCategory.rec with n
  dsimp at x ⊢
  obtain ⟨m, p, _, s, rfl⟩ := X.exists_nonDegenerate s
  refine ⟨⟨⟨m, s⟩, SimplexCategory.toTopMap p (⦋n⦌.toTopHomeo x)⟩, ?_⟩
  simp [sigmaToTopObj, SimplexCategory.toTopHomeo_symm_naturality_apply,
    yonedaEquiv_symm_map]

@[simp]
lemma range_sigmaToTopObj (X : SSet) : Set.range X.sigmaToTopObj = Set.univ := by
  ext x
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  exact X.surjective_sigmaToTopObj x

section

lemma isCompact_toTopObj (n : SimplexCategory) : IsCompact n.toTopObj := by
  induction' n using SimplexCategory.rec with n
  let S : Set (Fin (n + 1) → ℝ≥0) := Set.pi Set.univ (fun _ ↦ Set.Iic 1)
  have hS : IsCompact S := isCompact_univ_pi (fun _ ↦ by
    convert isCompact_Icc (α := ℝ≥0) (a := 0) (b := 1)
    aesop)
  apply IsCompact.of_isClosed_subset hS
  · exact IsClosed.preimage (f := fun (f : Fin (n + 1) → ℝ≥0) ↦ ∑ i, f i)
      (by continuity) isClosed_singleton
  · intro f hf
    dsimp only [SimplexCategory.toTopObj] at hf
    erw [Set.mem_setOf] at hf
    intro i _
    simpa [Set.mem_Iic, ← hf] using Finset.sum_le_univ_sum_of_nonneg
      (f := f) (s := {i}) (by simp)

instance (n : SimplexCategory) : CompactSpace n.toTopObj := by
  rw [← isCompact_iff_compactSpace]
  apply isCompact_toTopObj

end

example (X : SSet) [X.IsFinite] :
    CompactSpace ((Σ (s : (Σ (n : ℕ), X.nonDegenerate n)),
      SimplexCategory.toTopObj (.mk s.1))) := by
  infer_instance

instance (T : SSet.{0}) [T.IsFinite] :
    CompactSpace (SSet.toTop.obj T) where
  isCompact_univ := by
    simpa using IsCompact.image CompactSpace.isCompact_univ T.continuous_sigmaToTopObj

open TopCat

namespace stdSimplex


noncomputable def toTopObjHomeoUnitInterval :
    |Δ[1]| ≃ₜ I :=
  ((SimplexCategory.toTopHomeo _).trans SimplexCategory.toTopObjOneHomeo).trans
    (unitInterval.symmHomeomorph.trans Homeomorph.ulift.symm)

noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj I :=
  sSetTopAdj.homEquiv _ _ (ofHom (toContinuousMap toTopObjHomeoUnitInterval))

@[simp]
lemma δ_one_toSSetObjI :
    stdSimplex.δ 1 ≫ toSSetObjI = SSet.const (toSSetObj₀Equiv.symm 0) := by
  dsimp only [toSSetObjI]
  rw [← Adjunction.homEquiv_naturality_left,
    sSetTopAdj_homEquiv_stdSimplex_zero]
  dsimp
  congr 3
  ext x
  obtain rfl := Subsingleton.elim x default
  dsimp only [toTopObjHomeoUnitInterval]
  simp [ContinuousMap.comp, Function.comp]
  dsimp only [DFunLike.coe, EquivLike.coe]
  dsimp
  apply Homeomorph.ulift.injective
  simp only [Homeomorph.apply_symm_apply]
  change _ = 0
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  have : ⦋0⦌.toTopHomeo default = default := Subsingleton.elim _ _
  rw [this]
  rw [Subtype.ext_iff]
  simp [SimplexCategory.toTopObjOneHomeo]
  trans 1 - 1
  · congr
    simp
    rw [Finset.sum_eq_single 0 (by simp) (by simp; rfl)]; rfl
  · simp

@[simp]
lemma δ_zero_toSSetObjI :
    stdSimplex.δ 0 ≫ toSSetObjI = SSet.const (toSSetObj₀Equiv.symm 1) := by
  -- needs cleanup...
  dsimp only [toSSetObjI]
  rw [← Adjunction.homEquiv_naturality_left,
    sSetTopAdj_homEquiv_stdSimplex_zero]
  dsimp
  congr 3
  ext x
  obtain rfl := Subsingleton.elim x default
  dsimp only [toTopObjHomeoUnitInterval]
  simp [ContinuousMap.comp, Function.comp]
  dsimp only [DFunLike.coe, EquivLike.coe]
  dsimp
  apply Homeomorph.ulift.injective
  simp only [Homeomorph.apply_symm_apply]
  change _ = 1
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  have : ⦋0⦌.toTopHomeo default = default := Subsingleton.elim _ _
  rw [this]
  rw [Subtype.ext_iff]
  simp [SimplexCategory.toTopObjOneHomeo]
  change ¬ (1 = 0)
  omega

@[simp]
lemma toSSetObj_app_const_zero :
    toSSetObjI.app (op ⦋0⦌) (const _ 0 _) = toSSetObj₀Equiv.symm 0 := by
  -- needs cleanup...
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp]
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · congr
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    ext i
    fin_cases i
    rfl
  · simp

@[simp]
lemma toSSetObj_app_const_one :
    toSSetObjI.app (op ⦋0⦌) (const _ 1 _) = toSSetObj₀Equiv.symm 1 := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp]
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · congr
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    ext i
    fin_cases i
    rfl
  · simp

end stdSimplex

end SSet

namespace TopCat

open Functor.Monoidal Functor.LaxMonoidal

noncomputable instance : toSSet.Monoidal := toSSet.monoidalOfChosenFiniteProducts

@[reassoc (attr := simp)]
lemma sSetι₀_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{0}) :
    SSet.ι₀ ≫ toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      μ TopCat.toSSet X I = toSSet.map TopCat.ι₀ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply ChosenFiniteProducts.hom_ext <;> simp [← Functor.map_comp]

@[reassoc (attr := simp)]
lemma sSetι₁_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{0}) :
    SSet.ι₁ ≫ toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X I = toSSet.map TopCat.ι₁ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply ChosenFiniteProducts.hom_ext <;> simp [← Functor.map_comp]

namespace DeformationRetract

variable (X Y : TopCat.{0})

open Functor.Monoidal Functor.LaxMonoidal

variable (hf : DeformationRetract X Y)

noncomputable def toSSet : SSet.DeformationRetract (toSSet.obj X) (toSSet.obj Y) where
  toRetract := hf.toRetract.map TopCat.toSSet
  h := _ ◁ SSet.stdSimplex.toSSetObjI ≫ (μIso TopCat.toSSet _ _).hom ≫ TopCat.toSSet.map hf.h
  hi := by
    dsimp
    rw [← whisker_exchange_assoc, μ_natural_left_assoc, ← Functor.map_comp, hf.hi,
      Functor.map_comp, μ_fst_assoc, ChosenFiniteProducts.whiskerLeft_fst_assoc]
  h₀ := by
    dsimp
    simpa only [sSetι₀_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map hf.h₀
  h₁ := by
    dsimp
    simpa only [sSetι₁_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map hf.h₁

end DeformationRetract

end TopCat
