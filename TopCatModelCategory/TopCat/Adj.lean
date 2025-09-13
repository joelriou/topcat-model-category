import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.AlgebraicTopology.SingularSet
import TopCatModelCategory.TopCat.W
import TopCatModelCategory.TopCat.T1Inclusion
import TopCatModelCategory.TopCat.DeformationRetract
import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Skeleton
import TopCatModelCategory.SSet.Contractible

universe u

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial NNReal Limits MonoidalCategory Opposite

scoped [Simplicial] notation "|" X "|" => SSet.toTop.obj X

namespace SSet

instance : toTop.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint

instance {J : Type*} [LinearOrder J] :
    PreservesWellOrderContinuousOfShape J SSet.toTop where

end SSet

namespace SimplexCategory

open SSet

noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ n.toTopObj :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

instance (n : SimplexCategory) : T2Space |stdSimplex.{u}.obj n| := n.toTopHomeo.symm.t2Space

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (toTopHomeo m).toFun.comp (SSet.toTop.{u}.map (stdSimplex.map f)) =
    (toTopMap f).comp n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (congr_fun ((forget _).congr_map
    (toTopSimplex.hom.naturality f)) x)

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (stdSimplex.map f) x)) =
      (toTopMap f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.invFun.comp (toTopMap f) =
      (SSet.toTop.{u}.map (stdSimplex.map f)).hom.1.comp n.toTopHomeo.invFun := by
  ext x : 1
  exact congr_fun ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : n.toTopObj) :
    m.toTopHomeo.symm (toTopMap f x) =
      SSet.toTop.{u}.map (stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

noncomputable instance : Unique (SSet.toTop.obj Δ[0]) := ⦋0⦌.toTopHomeo.unique

noncomputable def SSet.isTerminalToTopObjStdSimplex₀ : IsTerminal (SSet.toTop.obj Δ[0]) :=
  IsTerminal.ofUniqueHom (fun _ ↦
    (TopCat.ofHom ⟨fun _ ↦ default, by continuity⟩)) (fun _ _ ↦ by
      ext
      apply Subsingleton.elim)

namespace TopCat

instance : toSSet.IsRightAdjoint := sSetTopAdj.isRightAdjoint

@[simps! symm_apply]
def toSSetObj₀Equiv {X : TopCat.{u}} :
    toSSet.obj X _⦋0⦌ ≃ X :=
  (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : ⦋0⦌.toTopObj)
      invFun x := ⟨fun _ ↦ x, by continuity⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]
lemma toSSet_map_const (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y) :
    toSSet.map (TopCat.const (X := X) y) =
      SSet.const (toSSetObj₀Equiv.symm y) :=
  rfl

end TopCat

noncomputable instance : Unique (|Δ[0]| : Type u) := ⦋0⦌.toTopHomeo.unique

lemma sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{u}}
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

variable (X : SSet.{u})

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

noncomputable def isColimitCoconeFromElementsOp : IsColimit X.coconeFromElementsOp :=
  Presheaf.colimitOfRepresentable.{u} X

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

instance (n : SimplexCategory) : CompactSpace |stdSimplex.{u}.obj n| :=
  n.toTopHomeo.symm.compactSpace

end

example (X : SSet) [X.IsFinite] :
    CompactSpace ((Σ (s : (Σ (n : ℕ), X.nonDegenerate n)),
      SimplexCategory.toTopObj (.mk s.1))) := by
  infer_instance

instance (T : SSet.{u}) [T.IsFinite] :
    CompactSpace (SSet.toTop.obj T) where
  isCompact_univ := by
    simpa using IsCompact.image CompactSpace.isCompact_univ T.continuous_sigmaToTopObj

open TopCat

namespace stdSimplex

def simplexCategoryToTopObjHomeoUnitInterval :
    ⦋1⦌.toTopObj ≃ₜ I :=
  (SimplexCategory.toTopObjOneHomeo).trans
    (unitInterval.symmHomeomorph.trans Homeomorph.ulift.symm)

noncomputable def toTopObjHomeoUnitInterval :
    |Δ[1]| ≃ₜ I :=
  (SimplexCategory.toTopHomeo _).trans
    simplexCategoryToTopObjHomeoUnitInterval

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
  dsimp only [toTopObjHomeoUnitInterval, simplexCategoryToTopObjHomeoUnitInterval]
  simp [ContinuousMap.comp]
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
  dsimp only [toTopObjHomeoUnitInterval, simplexCategoryToTopObjHomeoUnitInterval]
  simp [ContinuousMap.comp]
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

@[simp]
lemma SimplexCategory.toTopObjOneHomeo_toTopMap_δ_one_default (x : ⦋0⦌.toTopObj):
    SimplexCategory.toTopObjOneHomeo (SimplexCategory.toTopMap (SimplexCategory.δ 1) x) = 1 := by
  obtain rfl := Subsingleton.elim x default
  dsimp [SimplexCategory.toTopMap, SimplexCategory.toTopObjOneHomeo]
  ext
  dsimp
  rw [Finset.sum_eq_single 0 (by simp)]; rfl
  simp
  rfl

@[simp]
lemma SimplexCategory.toTopObjOneHomeo_toTopMap_δ_zero_default (x : ⦋0⦌.toTopObj):
    SimplexCategory.toTopObjOneHomeo (SimplexCategory.toTopMap (SimplexCategory.δ 0) x) = 0 := by
  rfl

namespace TopCat

open Functor.Monoidal Functor.LaxMonoidal

noncomputable instance : toSSet.Monoidal := .ofChosenFiniteProducts _

@[reassoc (attr := simp)]
lemma sSetι₀_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{u}) :
    SSet.ι₀ ≫ toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      μ TopCat.toSSet X I = toSSet.map TopCat.ι₀ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

@[reassoc (attr := simp)]
lemma sSetι₁_whiskerLeft_toSSetObjI_μIso_hom (X : TopCat.{u}) :
    SSet.ι₁ ≫ toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X I = toSSet.map TopCat.ι₁ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

namespace DeformationRetract

variable (X Y : TopCat.{u})

open Functor.Monoidal Functor.LaxMonoidal

variable (hf : DeformationRetract X Y)

noncomputable def toSSet : SSet.DeformationRetract (toSSet.obj X) (toSSet.obj Y) where
  toRetract := hf.toRetract.map TopCat.toSSet
  h := _ ◁ SSet.stdSimplex.toSSetObjI ≫ (μIso TopCat.toSSet _ _).hom ≫ TopCat.toSSet.map hf.h
  hi := by
    dsimp
    rw [← whisker_exchange_assoc, μ_natural_left_assoc, ← Functor.map_comp, hf.hi,
      Functor.map_comp, μ_fst_assoc, CartesianMonoidalCategory.whiskerLeft_fst_assoc]
  h₀ := by
    dsimp
    simpa only [sSetι₀_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map hf.h₀
  h₁ := by
    dsimp
    simpa only [sSetι₁_whiskerLeft_toSSetObjI_μIso_hom_assoc]
      using TopCat.toSSet.congr_map hf.h₁

end DeformationRetract

lemma toSSetObj₀Equiv_toSSet_obj_δ_one (X : TopCat.{u}) (x : toSSet.obj X _⦋1⦌) :
    toSSetObj₀Equiv ((toSSet.obj X).δ 1 x) =
      toSSetObjEquiv _ _ x (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 0) := by
  obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective x
  rw [Equiv.apply_symm_apply]
  apply congr_arg f
  apply SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.injective
  apply Homeomorph.ulift.injective
  rw [Homeomorph.apply_symm_apply]
  erw [Homeomorph.apply_symm_apply]
  dsimp [SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval, unitInterval.symm]
  ext : 1
  convert sub_self _
  dsimp
  erw [SimplexCategory.toTopObjOneHomeo_toTopMap_δ_one_default]
  rfl

lemma toSSetObj₀Equiv_toSSet_obj_δ_zero (X : TopCat.{u}) (x : toSSet.obj X _⦋1⦌) :
    toSSetObj₀Equiv ((toSSet.obj X).δ 0 x) =
      toSSetObjEquiv _ _ x (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 1) := by
  obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective x
  rw [Equiv.apply_symm_apply]
  apply congr_arg f
  apply SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.injective
  apply Homeomorph.ulift.injective
  rw [Homeomorph.apply_symm_apply]
  erw [Homeomorph.apply_symm_apply]
  dsimp [SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval, unitInterval.symm]
  ext : 1
  apply sub_zero

end TopCat

open Topology

namespace SimplexCategory

@[simp]
lemma const_apply' (x y : SimplexCategory)
    (i : Fin (y.len + 1)) (j : Fin (x.len + 1)) :
    const x y i j = i :=
  rfl

section

variable {n : ℕ}

def toTopObjι (f : ⦋n⦌.toTopObj) (i : Fin (n + 1)) : ℝ := (f.1 i).1

@[simp]
lemma toTopObjι_apply (f : ⦋n⦌.toTopObj) (i : Fin (n + 1)) :
    toTopObjι f i = f i := rfl

lemma isClosedEmbedding_toTopObjι :
    IsClosedEmbedding (toTopObjι (n := n)) :=
  Isometry.isClosedEmbedding (fun _ _ ↦ rfl)

end

namespace toTopObj

variable {n m : SimplexCategory}

def vertex (i : Fin (n.len + 1)) : n.toTopObj :=
  ⟨fun j ↦ if j = i then 1 else 0, by simp [toTopObj]⟩

@[simp]
lemma toTopMap_vertex (f : n ⟶ m) (i : Fin (n.len + 1)) :
    toTopMap f (vertex i) = vertex (f i) := by
  dsimp [toTopMap, vertex]
  aesop

end toTopObj

end SimplexCategory

namespace SSet

variable {X Y : SSet.{u}}

noncomputable def toTopObjMk (x : X _⦋0⦌) : toTop.obj X :=
  toTop.map (yonedaEquiv.symm x) default

@[simp]
lemma toTop_map_toTopObjMk (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTop.map f (toTopObjMk x) = toTopObjMk (f.app _ x) := by
  dsimp [toTopObjMk]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, yonedaEquiv_symm_comp]

variable (X) in
@[simp]
lemma toTop_map_const_apply (y : Y _⦋0⦌) (x : toTop.obj X) :
    toTop.map (SSet.const (X := X) y) x = toTopObjMk y := by
  let p : X ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from _
  have : (TopCat.Hom.hom (toTop.map p)) x = toTopObjMk (stdSimplex.const _ 0 _) :=
    Subsingleton.elim _ _
  rw [← SSet.comp_const (f := p), Functor.map_comp]
  simp [this]

@[simp]
lemma _root_.SimplexCategory.toTopHomeo_toTopObjMk {n : ℕ} (i : Fin (n + 1)):
    ⦋n⦌.toTopHomeo (toTopObjMk.{u} (stdSimplex.const _ i _))=
      SimplexCategory.toTopObj.vertex (n := ⦋n⦌) i := by
  apply (SimplexCategory.toTopHomeo_naturality_apply.{u}
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) _).trans
  rw [show ⦋0⦌.toTopHomeo default = default by subsingleton]
  ext j
  simp
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (a := 0) (by simp) (by simp; rfl)]
    simp [SimplexCategory.toTopObj.vertex]
  · rw [Finset.sum_eq_zero (fun _ ↦ by simp; tauto)]
    simp [SimplexCategory.toTopObj.vertex]
    tauto

namespace stdSimplex

@[simp]
lemma toTopObjHomeoUnitInterval_zero :
    toTopObjHomeoUnitInterval (toTopObjMk (stdSimplex.const _ 0 _)) = 0 := by
  dsimp [toTopObjHomeoUnitInterval]
  simp
  have : SimplexCategory.toTopObjOneHomeo (SimplexCategory.toTopObj.vertex 0) = 1 := rfl
  simp [simplexCategoryToTopObjHomeoUnitInterval, this]
  rfl

@[simp]
lemma toTopObjHomeoUnitInterval_one :
    toTopObjHomeoUnitInterval (toTopObjMk (stdSimplex.const _ 1 _)) = 1 := by
  dsimp [toTopObjHomeoUnitInterval]
  simp
  have : SimplexCategory.toTopObjOneHomeo (SimplexCategory.toTopObj.vertex 1) = 0 := rfl
  simp [simplexCategoryToTopObjHomeoUnitInterval, this]
  rfl

end stdSimplex

instance : IsEmpty (toTop.obj (⊥ : Subcomplex X).toSSet) := by
  have : IsEmpty (asEmptyCocone PEmpty.{u + 1}).pt := by dsimp; infer_instance
  exact (Iso.toEquiv (((Subcomplex.isInitialBot X).isInitialObj
    (toTop ⋙ forget _)).coconePointUniqueUpToIso Types.isInitialPunit)).isEmpty

end SSet
