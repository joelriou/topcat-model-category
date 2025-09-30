import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.ToTopObjHomeo
import TopCatModelCategory.ConvexCompact

universe u

open CategoryTheory Limits Topology Simplicial

namespace SimplexCategory

namespace Hyperplane

open NormedSpace

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

def barycenterCompl : TopologicalSpace.Opens (stdSimplex n) where
  carrier := {⟨⟨fun _ ↦ 0, by simp⟩, by simp [stdSimplex]⟩}ᶜ
  is_open' := isOpen_compl_singleton

lemma notMem_barycenterCompl_zero (x : stdSimplex 0) :
    x ∉ (barycenterCompl 0).1 := by
  simpa [barycenterCompl] using Subsingleton.elim _ _

instance : DeltaGeneratedSpace' (barycenterCompl n) := by
  infer_instance

def ιBarycenterCompl : C(barycenterCompl n, stdSimplex n) :=
  ⟨_, continuous_subtype_val⟩

lemma isOpenEmbedding_ιBarycenterCompl :
    IsOpenEmbedding (ιBarycenterCompl n) :=
  TopologicalSpace.Opens.isOpenEmbedding' _

def boundary : Set (stdSimplex n) :=
  setOf (fun x ↦ ∃ (i : Fin (n + 1)), (n + 1) • x.1.1 i + 1 = 0)

instance : IsEmpty (boundary 0) where
  false := by
    rintro ⟨⟨⟨x, hx⟩, hx'⟩, i, hi⟩
    obtain rfl : x = 0 := by
      ext i
      fin_cases i
      simpa using hx
    simp at hi

instance : IsEmpty |(∂Δ[0] : SSet.{u})| := by
  simp only [SSet.boundary_zero]
  infer_instance

def boundaryHomeo : boundary n ≃ₜ (|∂Δ[n]| : Type u) := by
  obtain _ | n := n
  · exact
      { toFun x := by exfalso; exact IsEmpty.false x
        invFun x := by exfalso; exact IsEmpty.false x
        left_inv _ := by subsingleton
        right_inv _ := by subsingleton }
  · sorry

lemma boundary_subset_barycenterCompl : boundary n ⊆ barycenterCompl n := by
  rintro x ⟨i, hi⟩
  rintro rfl
  simp at hi

def boundaryToBarycenterCompl : C(boundary n, barycenterCompl n) :=
  ⟨fun x ↦ ⟨x.1, boundary_subset_barycenterCompl n x.2⟩, by continuity⟩

def boundaryRetraction : C(barycenterCompl n, boundary n) := by
  obtain _ | n := n
  · exact ⟨fun x ↦ (notMem_barycenterCompl_zero x x.2).elim, by continuity⟩
  · sorry

@[simp]
lemma boundaryRetraction_boundaryToBarycenterCompl (x : boundary n):
    stdSimplex.boundaryRetraction n
      (stdSimplex.boundaryToBarycenterCompl n x) = x := by
  obtain _ | n := n
  · exfalso
    exact IsEmpty.false x
  · sorry

lemma boundaryHomeo_compatibility (x : (|∂Δ[n]| : Type u)) :
    ⦋n⦌.toTopHomeo.symm (stdSimplexHomeo n (stdSimplex.ιBarycenterCompl n
      (stdSimplex.boundaryToBarycenterCompl n ((stdSimplex.boundaryHomeo n).symm x)))) =
        SSet.toTop.map ∂Δ[n].ι x := by
  obtain _ | n := n
  · exfalso
    exact IsEmpty.false x
  · sorry

end SimplexCategory.Hyperplane.stdSimplex
