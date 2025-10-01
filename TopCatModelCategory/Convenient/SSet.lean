import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.ToTopObjHomeo
import TopCatModelCategory.Homeomorph
import TopCatModelCategory.ConvexCompact

universe u

open CategoryTheory Limits Topology Simplicial NormedSpace

namespace SimplexCategory

namespace Hyperplane

noncomputable def stdSimplexHomeoClosedBall (n : ℕ) :
    stdSimplex n ≃ₜ (Metric.closedBall (0 : Hyperplane n) 1) := by
  obtain _ | n := n
  · exact
      { toFun _ := ⟨0, by simp⟩
        invFun _ := default
        left_inv _ := by subsingleton
        right_inv _ := by subsingleton }
  · exact homeoClosedBallOfConvexCompact (Hyperplane.convex_stdSimplex (n + 1))
      (Hyperplane.isCompact_stdSimplex _) (Hyperplane.zero_mem_interior_stdSimplex _)

end Hyperplane

end SimplexCategory

namespace SSet

section

open NormedSpace SimplexCategory

instance (n : ℕ) : DeltaGeneratedSpace' (Hyperplane.stdSimplex n) :=
  (Hyperplane.stdSimplexHomeoClosedBall n).symm.isQuotientMap.isGeneratedBy

instance (n : SimplexCategory) : DeltaGeneratedSpace' n.toTopObj := by
  induction' n using SimplexCategory.rec with n
  exact (Hyperplane.stdSimplexHomeo n).isQuotientMap.isGeneratedBy

end

instance (n : SimplexCategory) : DeltaGeneratedSpace' (SimplexCategory.toTop.{u}.obj n) :=
  (Homeomorph.ulift.{u} (X := n.toTopObj)).symm.isQuotientMap.isGeneratedBy

instance (n : SimplexCategory) : DeltaGeneratedSpace' (toTop.{u}.obj (stdSimplex.obj n)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).symm.isQuotientMap.isGeneratedBy

instance (X : SSet.{u}) : DeltaGeneratedSpace' (toTop.obj X) :=
  isGeneratedBy.of_isColimit (isColimitOfPreserves toTop X.isColimitCoconeFromElementsOp)
    (fun _ ↦ by dsimp; infer_instance)

noncomputable def toDeltaGenerated : SSet.{u} ⥤ DeltaGenerated' where
  obj X := .of (toTop.obj X)
  map f := toTop.map f

noncomputable def toDeltaGeneratedCompIso :
    toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat ≅ toTop := Iso.refl _

noncomputable def toDeltaGeneratedIso :
    toDeltaGenerated.{u} ≅ toTop ⋙ TopCat.toDeltaGenerated' :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ DeltaGenerated'.adjUnitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso TopCat.toDeltaGenerated'

instance (J : Type*) [Category J] :
    ReflectsColimitsOfShape J DeltaGenerated'.toTopCat.{u} where
  reflectsColimit := ⟨fun hc ↦ ⟨ObjectProperty.ιReflectsIsColimit _ hc⟩⟩

instance (J : Type*) [Category J] :
    PreservesColimitsOfShape J toDeltaGenerated.{u} where
  preservesColimit :=
    ⟨fun hc ↦ ⟨isColimitOfReflects DeltaGenerated'.toTopCat (isColimitOfPreserves toTop hc)⟩⟩

end SSet

namespace SimplexCategory.Hyperplane.stdSimplex

variable (n : ℕ)

def barycenterCompl : Set (Hyperplane n) :=
  stdSimplex n ∩ {⟨0, by simp⟩}ᶜ

lemma barycenterCompl_subset_stdSimplex : barycenterCompl n ⊆ stdSimplex n :=
  Set.inter_subset_left

@[simp]
lemma barycenterCompl_zero :
    barycenterCompl 0 = ∅ := by
  ext ⟨x, hx⟩
  simp [barycenterCompl]
  intro
  ext i
  fin_cases i
  simpa using hx

def ιBarycenterCompl : C(barycenterCompl n, stdSimplex n) :=
  ⟨fun x ↦ ⟨x.1, barycenterCompl_subset_stdSimplex _ x.2⟩, by continuity⟩

lemma isOpenEmbedding_ιBarycenterCompl :
    IsOpenEmbedding (ιBarycenterCompl n) :=
  IsOpenEmbedding.inclusion (barycenterCompl_subset_stdSimplex n) (by
    simp [barycenterCompl]
    convert isClosed_singleton (X := stdSimplex n) (x := ⟨⟨0, by simp⟩, by simp [stdSimplex]⟩)
    aesop)

instance : DeltaGeneratedSpace' (barycenterCompl n) :=
  (isOpenEmbedding_ιBarycenterCompl n).isGeneratedBy

def boundary : Set (Hyperplane n) :=
  stdSimplex n ∩ setOf (fun x ↦ ∃ (i : Fin (n + 1)), (n + 1) • x.1 i + 1 = 0)

instance : IsEmpty (boundary 0) where
  false := by
    rintro ⟨⟨x, hx⟩, hx', i, hi⟩
    obtain rfl : x = 0 := by
      ext i
      fin_cases i
      simpa using hx
    simp at hi

instance : IsEmpty |(∂Δ[0] : SSet.{u})| := by
  simp only [SSet.boundary_zero]
  infer_instance

noncomputable def boundaryHomeo : boundary n ≃ₜ (|∂Δ[n]| : Type u) := by
  obtain _ | n := n
  · exact
      { toFun x := by exfalso; exact IsEmpty.false x
        invFun x := by exfalso; exact IsEmpty.false x
        left_inv _ := by subsingleton
        right_inv _ := by subsingleton }
  · refine Homeomorph.trans ?_
      (SSet.boundary.t₁Inclusions_toTop_map_ι.{u} (n + 1)).homeomorphRange.symm
    sorry

lemma boundary_subset_barycenterCompl : boundary n ⊆ barycenterCompl n := by
  rintro x ⟨hx, i, hi⟩
  simp only [barycenterCompl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨hx, by rintro rfl; simp at hi⟩

def boundaryToBarycenterCompl : C(boundary n, barycenterCompl n) :=
  ⟨fun x ↦ ⟨x.1, boundary_subset_barycenterCompl n x.2⟩, by continuity⟩

lemma boundaryHomeo_compatibility (x : (|∂Δ[n]| : Type u)) :
    ⦋n⦌.toTopHomeo.symm (stdSimplexHomeo n (stdSimplex.ιBarycenterCompl n
      (stdSimplex.boundaryToBarycenterCompl n ((stdSimplex.boundaryHomeo n).symm x)))) =
        SSet.toTop.map ∂Δ[n].ι x := by
  obtain _ | n := n
  · exfalso
    exact IsEmpty.false x
  · sorry

lemma boundary_eq :
    boundary (n + 1) =
      retractionBoundaryOfConvexCompact.boundary (stdSimplex (n + 1)) := sorry

noncomputable def boundaryRetraction : C(barycenterCompl n, boundary n) := by
  obtain _ | n := n
  · exact ⟨fun ⟨x, hx⟩ ↦ by simp at hx, by continuity⟩
  · exact ContinuousMap.comp ⟨_, (Homeomorph.ofSetEq (boundary_eq n)).symm.continuous⟩
      ⟨fun x ↦ retractionBoundaryOfConvexCompact.retraction
        (Hyperplane.convex_stdSimplex (n + 1)) (Hyperplane.isCompact_stdSimplex _)
        (Hyperplane.zero_mem_interior_stdSimplex _) ⟨x, x.2.2⟩, by continuity⟩

@[simp]
lemma boundaryRetraction_boundaryToBarycenterCompl (x : boundary n):
    stdSimplex.boundaryRetraction n
      (stdSimplex.boundaryToBarycenterCompl n x) = x := by
  obtain _ | n := n
  · exfalso
    exact IsEmpty.false x
  · obtain ⟨x, hx⟩ := x
    have := retractionBoundaryOfConvexCompact.retraction_boundaryι_apply
      (Hyperplane.convex_stdSimplex (n + 1)) (Hyperplane.isCompact_stdSimplex _)
        (Hyperplane.zero_mem_interior_stdSimplex _) ⟨x, by rwa [← boundary_eq]⟩
    rwa [Subtype.ext_iff] at this ⊢

end SimplexCategory.Hyperplane.stdSimplex
