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
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

instance (n : SimplexCategory) : T2Space |stdSimplex.{u}.obj n| := n.toTopHomeo.symm.t2Space

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (toTopHomeo m).toFun.comp (SSet.toTop.{u}.map (SSet.stdSimplex.map f)) =
    (stdSimplex.map f).comp n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (congr_fun ((forget _).congr_map
    (toTopSimplex.hom.naturality f)) x)

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.invFun.comp (stdSimplex.map f) =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom.1.comp n.toTopHomeo.invFun := by
  ext x : 1
  exact congr_fun ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

instance : Unique (stdSimplex ℝ (Fin (⦋0⦌.len + 1))) :=
  inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))

noncomputable instance : Unique (SSet.toTop.obj Δ[0]) := ⦋0⦌.toTopHomeo.unique

noncomputable def SSet.isTerminalToTopObjStdSimplex₀ : IsTerminal (SSet.toTop.obj Δ[0]) :=
  IsTerminal.ofUniqueHom (fun _ ↦
    (TopCat.ofHom ⟨fun _ ↦ default, by continuity⟩)) (fun _ _ ↦ by
      ext
      apply Subsingleton.elim)

namespace TopCat

instance : toSSet.IsRightAdjoint := sSetTopAdj.isRightAdjoint

@[simps! symm_apply]
noncomputable def toSSetObj₀Equiv {X : TopCat.{u}} :
    toSSet.obj X _⦋0⦌ ≃ X :=
  (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
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
    (Σ (s : (Σ (n : ℕ), X.nonDegenerate n)), _root_.stdSimplex ℝ (Fin (s.1 + 1))) → |X| :=
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
  induction n using SimplexCategory.rec with | _ n
  dsimp at x ⊢
  obtain ⟨m, p, _, s, rfl⟩ := X.exists_nonDegenerate s
  refine ⟨⟨⟨m, s⟩, stdSimplex.map p (⦋n⦌.toTopHomeo x)⟩, ?_⟩
  simp [sigmaToTopObj, yonedaEquiv_symm_map]
  erw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  simp

@[simp]
lemma range_sigmaToTopObj (X : SSet) : Set.range X.sigmaToTopObj = Set.univ := by
  ext x
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  exact X.surjective_sigmaToTopObj x

section

alias isCompact_toTopObj := isCompact_stdSimplex

/-lemma isCompact_toTopObj (n : SimplexCategory) : IsCompact n.toTopObj := by
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
      (f := f) (s := {i}) (by simp)-/

/-instance (n : SimplexCategory) : CompactSpace (_root_.stdSimplex ℝ (Fin (n.len + 1))) := by
  infer_instance-/

instance (n : SimplexCategory) : CompactSpace |stdSimplex.{u}.obj n| :=
  n.toTopHomeo.symm.compactSpace

end

example (X : SSet) [X.IsFinite] :
    CompactSpace ((Σ (s : (Σ (n : ℕ), X.nonDegenerate n)),
      _root_.stdSimplex ℝ (Fin (s.1 + 1)))) := by
  infer_instance

instance (T : SSet.{u}) [T.IsFinite] :
    CompactSpace (SSet.toTop.obj T) where
  isCompact_univ := by
    simpa using IsCompact.image CompactSpace.isCompact_univ T.continuous_sigmaToTopObj

open TopCat

namespace stdSimplex

def simplexCategoryToTopObjHomeoUnitInterval :
    _root_.stdSimplex ℝ (Fin 2) ≃ₜ I :=
  stdSimplexHomeomorphUnitInterval.trans (Homeomorph.ulift.symm)

noncomputable def toTopObjHomeoUnitInterval :
    |Δ[1]| ≃ₜ I :=
  (SimplexCategory.toTopHomeo _).trans
    simplexCategoryToTopObjHomeoUnitInterval

noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj I :=
  sSetTopAdj.homEquiv _ _ (ofHom (toContinuousMap toTopObjHomeoUnitInterval))

@[simp]
lemma δ_one_toSSetObjI :
    stdSimplex.δ 1 ≫ toSSetObjI = SSet.const (toSSetObj₀Equiv.symm 0) := by
  dsimp only [toSSetObjI, toTopObjHomeoUnitInterval, simplexCategoryToTopObjHomeoUnitInterval]
  rw [← Adjunction.homEquiv_naturality_left,
    sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  simp
  apply congr_arg
  convert stdSimplexHomeomorphUnitInterval_zero
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
  rfl

@[simp]
lemma δ_zero_toSSetObjI :
    stdSimplex.δ 0 ≫ toSSetObjI = SSet.const (toSSetObj₀Equiv.symm 1) := by
  dsimp only [toSSetObjI, toTopObjHomeoUnitInterval, simplexCategoryToTopObjHomeoUnitInterval]
  rw [← Adjunction.homEquiv_naturality_left,
    sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  simp
  apply congr_arg
  convert stdSimplexHomeomorphUnitInterval_one
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
  rfl

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
lemma SimplexCategory.toTopObjOneHomeo_toTopMap_δ_one_default (x : stdSimplex ℝ (Fin 1)) :
    stdSimplexHomeomorphUnitInterval (stdSimplex.map (SimplexCategory.δ 1) x) = 0 :=  by
  obtain rfl := Subsingleton.elim x (stdSimplex.vertex 0)
  convert stdSimplexHomeomorphUnitInterval_zero
  aesop

@[simp]
lemma SimplexCategory.toTopObjOneHomeo_toTopMap_δ_zero_default (x : stdSimplex ℝ (Fin 1)) :
    stdSimplexHomeomorphUnitInterval (stdSimplex.map (SimplexCategory.δ 0) x) = 1 :=  by
  obtain rfl := Subsingleton.elim x (stdSimplex.vertex 0)
  convert stdSimplexHomeomorphUnitInterval_one
  aesop

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
  exact homeomorphI.injective (SimplexCategory.toTopObjOneHomeo_toTopMap_δ_one_default default)

lemma toSSetObj₀Equiv_toSSet_obj_δ_zero (X : TopCat.{u}) (x : toSSet.obj X _⦋1⦌) :
    toSSetObj₀Equiv ((toSSet.obj X).δ 0 x) =
      toSSetObjEquiv _ _ x (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 1) := by
  obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective x
  rw [Equiv.apply_symm_apply]
  apply congr_arg f
  apply SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.injective
  exact homeomorphI.injective (SimplexCategory.toTopObjOneHomeo_toTopMap_δ_zero_default default)

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

abbrev toTopObjι (f : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) : ℝ := f.1 i

@[simp]
lemma toTopObjι_apply (f : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    toTopObjι f i = f i := rfl

lemma isClosedEmbedding_toTopObjι :
    IsClosedEmbedding (toTopObjι (n := n)) :=
  Isometry.isClosedEmbedding (fun _ _ ↦ rfl)

end

/-namespace toTopObj

variable {n m : SimplexCategory}

def vertex (i : Fin (n.len + 1)) : n.toTopObj :=
  ⟨fun j ↦ if j = i then 1 else 0, by simp [toTopObj]⟩

@[simp]
lemma toTopMap_vertex (f : n ⟶ m) (i : Fin (n.len + 1)) :
    toTopMap f (vertex i) = vertex (f i) := by
  dsimp [toTopMap, vertex]
  aesop

end toTopObj-/

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
      stdSimplex.vertex i := by
  apply (SimplexCategory.toTopHomeo_naturality_apply.{u}
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) _).trans
  rw [show ⦋0⦌.toTopHomeo default = stdSimplex.vertex 0 by subsingleton]
  aesop

namespace stdSimplex


--@[simp]
lemma toTopObjHomeoUnitInterval_zero :
    toTopObjHomeoUnitInterval.{u, u} (toTopObjMk.{u} (stdSimplex.const _ 0 _)) = 0 := by
  apply toTopObjHomeoUnitInterval.{u}.symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply ⦋1⦌.toTopHomeo.injective
  dsimp [toTopObjMk]
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0),
    stdSimplex.map_vertex]
  dsimp [toTopObjHomeoUnitInterval]
  erw [Equiv.apply_symm_apply]
  apply simplexCategoryToTopObjHomeoUnitInterval.{u}.injective
  rw [Homeomorph.apply_symm_apply]
  apply ULift.down_injective
  apply stdSimplexHomeomorphUnitInterval_zero

@[simp]
lemma toTopObjHomeoUnitInterval_one :
    toTopObjHomeoUnitInterval.{u, u} (toTopObjMk (stdSimplex.const _ 1 _)) = 1 := by
  apply toTopObjHomeoUnitInterval.{u}.symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply ⦋1⦌.toTopHomeo.injective
  dsimp [toTopObjMk]
  erw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0),
    stdSimplex.map_vertex]
  dsimp [toTopObjHomeoUnitInterval]
  erw [Equiv.apply_symm_apply]
  apply simplexCategoryToTopObjHomeoUnitInterval.{u}.injective
  rw [Homeomorph.apply_symm_apply]
  apply ULift.down_injective
  apply stdSimplexHomeomorphUnitInterval_one

end stdSimplex

instance : IsEmpty (toTop.obj (⊥ : Subcomplex X).toSSet) := by
  have : IsEmpty (asEmptyCocone PEmpty.{u + 1}).pt := by dsimp; infer_instance
  exact (Iso.toEquiv (((Subcomplex.isInitialBot X).isInitialObj
    (toTop ⋙ forget _)).coconePointUniqueUpToIso Types.isInitialPunit)).isEmpty

end SSet

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {X Y Z : Type*}

noncomputable def FunOnFinite.linearMap_apply_apply_of_injective
    [Finite X] [Finite Y] (s : X → M) {f : X → Y} (hf : Function.Injective f)
    (x : X) : linearMap R M f s (f x) = s x := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  rw [FunOnFinite.linearMap_apply_apply]
  refine Finset.sum_eq_single _ (fun b hb ↦ ?_) (by simp)
  obtain rfl : b = x := hf (by simpa using hb)
  simp

end

namespace stdSimplex

@[simp]
lemma map_injective {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (map (S := S) f) := by
  intro a b h
  ext x
  simpa [map_coe, FunOnFinite.linearMap_apply_apply_of_injective _ _ _ hf]
    using DFunLike.congr_fun h (f x)

@[simp]
lemma mem_range_map_iff {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y)
    (g : stdSimplex S Y) :
    g ∈ Set.range (map f) ↔
      ∀ (x : Y) (_ : x ∉ Set.range f), g x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    intro i hi
    rw [map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_eq_zero]
    intro a ha
    exact (hi ⟨a, by simpa using ha⟩).elim
  · intro hg
    have h (y : Y) (hy : g y ≠ 0) : ∃ (x : X), f x = y := by
      by_contra!
      exact hy (hg _ (by simpa))
    choose r hr using h
    classical
    let P (x : X) : Prop := ∃ (y : Y) (hy : g y ≠ 0), r y hy = x
    have prop (y : Y) (hy : g y ≠ 0) : P (r y hy) := ⟨_, _, rfl⟩
    let v (x : X) : S := if h : P x then g.1 h.choose else 0
    have v_eq_zero (x : X) (hx : ¬ P x) : v x = 0 := dif_neg hx
    have v_apply (y : Y) (hy : g y ≠ 0) : v (r y hy) = g y := by
      dsimp [v]
      have : (prop y hy).choose = y := by
        obtain ⟨h₁, h₂⟩ := (prop y hy).choose_spec
        rw [← hr _ h₁, h₂, hr _ hy]
      rw [dif_pos (prop y hy), this]
      rfl
    refine ⟨⟨v, ?_, ?_⟩, ?_⟩
    · intro x
      by_cases hx : P x
      · obtain ⟨y, hy, rfl⟩ := hx
        simp [v_apply]
      · rw [v_eq_zero _ hx]
    · trans ∑ x with P x, v x
      · rw [Finset.sum_filter_of_ne]
        intro x _ hx
        by_contra!
        exact hx (v_eq_zero _ this)
      · rw [← stdSimplex.sum_eq_one g]
        apply Finset.sum_of_injOn (e := f)
        · intro x₁ hx₁ x₂ hx₂ h
          simp at hx₁ hx₂
          obtain ⟨y₁, _, rfl⟩ := hx₁
          obtain ⟨y₂, _, rfl⟩ := hx₂
          simp [hr] at h
          subst h
          rfl
        · intro
          simp
        · simp
          intro y hy
          by_contra!
          exact hy _ (prop y this) (hr _ this)
        · intro x hx
          simp at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [hr, v_apply y hy]
    · ext y
      rw [map_coe, FunOnFinite.linearMap_apply_apply]
      by_cases hy : g y = 0
      · rw [hy]
        apply Finset.sum_eq_zero
        intro x hx
        apply v_eq_zero
        rintro ⟨z, hz, rfl⟩
        obtain rfl : z = y := by simpa [hr] using hx
        exact hz hy
      · rw [Finset.sum_eq_single (a := r y hy)]
        · apply v_apply
        · intro x hx hx'
          simp at hx
          subst hx
          refine v_eq_zero _ ?_
          rintro ⟨z, hz, rfl⟩
          simp [hr] at hx'
        · simp [hr y hy]

end stdSimplex
