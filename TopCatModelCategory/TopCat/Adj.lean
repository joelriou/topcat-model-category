import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SingularSet

import TopCatModelCategory.TopCat.W
import TopCatModelCategory.TopCat.T1Inclusion
import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Skeleton

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial NNReal Limits

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

instance (n : SimplexCategory) : CompactSpace n.toTopObj := by
  rw [← isCompact_iff_compactSpace]
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

end

example (X : SSet) [X.IsFinite] :
    CompactSpace ((Σ (s : (Σ (n : ℕ), X.nonDegenerate n)),
      SimplexCategory.toTopObj (.mk s.1))) := by
  infer_instance

end SSet

namespace TopCat

instance (T : SSet.{0}) [T.IsFinite] :
    CompactSpace (SSet.toTop.obj T) where
  isCompact_univ := by
    simpa using IsCompact.image CompactSpace.isCompact_univ T.continuous_sigmaToTopObj

instance (X : TopCat.{0}) : IsFibrant (TopCat.toSSet.obj X) := by
  sorry

lemma t₁Inclusions_sSet_toObj_map_of_mono {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    t₁Inclusions (SSet.toTop.map i) := by
  sorry

end TopCat
