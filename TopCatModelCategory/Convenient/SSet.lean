import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.ToTopObjHomeo
import TopCatModelCategory.Homeomorph
import TopCatModelCategory.ConvexCompact
import TopCatModelCategory.TopCat.ToTopDecomposition

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

def boundary' : Set (stdSimplex n) :=
  setOf (fun x ↦ ∃ (i : Fin (n + 1)), (n + 1) • x.1.1 i + 1 = 0)

def boundary : Set (Hyperplane n) :=
  stdSimplex n ∩ setOf (fun x ↦ ∃ (i : Fin (n + 1)), (n + 1) • x.1 i + 1 = 0)

lemma zero_notMem_boundary : 0 ∉ boundary n := by
  intro hx
  simp [boundary] at hx

@[simps]
def boundaryHomeoBoundary' : boundary n ≃ₜ boundary' n where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩

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

lemma boundary'_eq_preimage :
    boundary' n =
      ((stdSimplexHomeo n).trans ⦋n⦌.toTopHomeo.symm) ⁻¹'
        Set.range (SSet.toTop.{u}.map ∂Δ[n].ι) := by
  suffices Set.range (SSet.toTop.{u}.map ∂Δ[n].ι) =
      (⦋n⦌.toTopHomeo.trans (stdSimplexHomeo n).symm) ⁻¹' boundary' n by aesop
  ext x
  obtain ⟨x, rfl⟩ := ⦋n⦌.toTopHomeo.symm.surjective x
  obtain ⟨⟨⟨x, hx₀⟩, hx⟩, rfl⟩ := (stdSimplexHomeo n).surjective x
  simp [stdSimplex] at hx
  rw [← not_iff_not, ← Set.mem_compl_iff, ← stdSimplex.toTopHomeo_mem_interior_iff,
    Set.mem_preimage, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    Homeomorph.symm_apply_apply]
  simp [stdSimplex.interior, stdSimplexHomeo, boundary']
  refine forall_congr' (fun i ↦ ?_)
  trans 0 < (↑n + 1) * x i + 1
  · have h : 0 < (n : ℝ) + 1 := by positivity
    rw [← Subtype.coe_lt_coe]
    dsimp
    rw [← mul_pos_iff_of_pos_left h, mul_add, mul_inv_cancel₀ h.ne']
  · exact LE.le.lt_iff_ne' (hx i)

noncomputable def boundaryHomeo : boundary n ≃ₜ (|∂Δ[n]| : Type u) := by
  obtain _ | n := n
  · exact
      { toFun x := by exfalso; exact IsEmpty.false x
        invFun x := by exfalso; exact IsEmpty.false x
        left_inv _ := by subsingleton
        right_inv _ := by subsingleton }
  · exact ((boundaryHomeoBoundary' (n + 1)).trans
      (Homeomorph.restrict ((stdSimplexHomeo (n + 1)).trans ⦋n + 1⦌.toTopHomeo.symm)
        (boundary'_eq_preimage (n + 1)).symm)).trans
      (SSet.boundary.t₁Inclusions_toTop_map_ι.{u} (n + 1)).homeomorphRange.symm

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
  · simp [ιBarycenterCompl, boundaryToBarycenterCompl, boundaryHomeo, Homeomorph.restrict]
    rfl

open retractionBoundaryOfConvexCompact homeoClosedBallOfConvexCompact in
lemma boundary_eq :
    boundary (n + 1) =
      retractionBoundaryOfConvexCompact.boundary (stdSimplex (n + 1)) := by
  ext x
  simp only [mem_boundary_iff]
  refine ⟨fun hx ↦ le_antisymm ?_ ?_, fun hx ↦ ?_⟩
  · obtain ⟨hx, i, hi⟩ := hx
    generalize ht : sup (stdSimplex (n + 1)) x = t
    have h₁ := (sup_mem_set (Hyperplane.isCompact_stdSimplex (n + 1))
      (Hyperplane.zero_mem_interior_stdSimplex _) x).2
    rw [ht, mem_stdSimplex_iff] at h₁
    replace h₁ := h₁ i
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, SetLike.val_smul, Pi.smul_apply,
      smul_eq_mul, add_eq_zero_iff_eq_neg'] at hi h₁
    nth_rw 3 [hi] at h₁
    simp only [le_add_neg_iff_add_le, zero_add] at h₁
    rw [mul_le_mul_iff_of_pos_left (by positivity)] at h₁
    have h₂ : 0 < - x.1 i := by
      by_contra! h₃
      have := mul_nonneg (show 0 ≤ (n : ℝ) + 1 + 1 by positivity)
        (Left.neg_nonpos_iff.1 h₃)
      grind
    rwa [← mul_le_iff_le_one_left h₂, mul_neg, neg_le_neg_iff]
  · rw [homeoClosedBallOfConvexCompact.le_sup_iff
      (Hyperplane.convex_stdSimplex (n + 1)) (Hyperplane.isCompact_stdSimplex _)
        (Hyperplane.zero_mem_interior_stdSimplex _) _ _ (by simp)]
    · simpa only [one_smul] using hx.1
    · rintro rfl
      exact zero_notMem_boundary (n + 1) hx
  · by_contra! h₁
    have h₂ := sup_mem_set (Hyperplane.isCompact_stdSimplex (n + 1))
      (Hyperplane.zero_mem_interior_stdSimplex _) x
    simp only [hx, mem_set_iff, zero_le_one, one_smul, true_and] at h₂
    simp only [boundary, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Set.mem_inter_iff,
      Set.mem_setOf_eq, not_and, not_exists] at h₁
    have hx₀ : x ≠ 0 := by
      rintro rfl
      rw [sup_zero (E := Hyperplane (n + 1))
        (Hyperplane.zero_mem_interior_stdSimplex (n + 1))] at hx
      exact zero_ne_one hx
    replace h₁ (i : Fin (n + 2)) :=
      lt_of_le_of_ne (by simpa using h₂ i) fun h => h₁ h₂ i h.symm
    have h₃ (i : Fin (n + 2)) : ∃ (t : ℝ), 1 < t ∧
        0 ≤ ((n : ℝ) + 1 + 1) * t * x.1 i + 1 := by
      by_cases hi : 0 ≤ x.1 i
      · exact ⟨2, by simp, by positivity⟩
      · replace hi : ((n : ℝ) + 1 + 1) * x.1 i < 0 :=
          mul_neg_of_pos_of_neg (by positivity) (not_le.1 hi)
        replace h₁ := h₁ i
        obtain ⟨u, hu⟩ : ∃ u, ((n : ℝ) + 1 + 1) * x.1 i = -u := ⟨_, (neg_neg _).symm⟩
        simp only [mul_assoc]
        simp only [mul_comm _ (x.1 i)]
        simp only [← mul_assoc]
        simp only [hu, lt_neg_add_iff_add_lt, add_zero, Left.neg_neg_iff, neg_mul,
          le_neg_add_iff_add_le] at h₁ hi ⊢
        exact ⟨u⁻¹, (one_lt_inv₀ hi).2 h₁, mul_inv_le_one⟩
    choose t ht using h₃
    let t' := (Finset.image t .univ).min' (by simp)
    obtain ⟨i, hi⟩ : ∃ i, t i = t' := by
      simpa using (Finset.image t .univ).min'_mem (by simp)
    have ht'₀ : 0 ≤ t' := by
      rw [← hi]
      exact le_trans (by simp) (ht i).1.le
    have ht' : t' • x ∈ stdSimplex (n + 1) := fun j ↦ by
      dsimp
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      by_cases hj : 0 ≤ x.1 j
      · positivity
      · refine le_trans (ht j).2 ?_
        simp only [not_le] at hj
        simp only [add_le_add_iff_right, mul_assoc]
        rw [mul_le_mul_iff_of_pos_left (by positivity), mul_le_mul_right_of_neg hj]
        exact Finset.min'_le _ _ (by simp)
    rw [← homeoClosedBallOfConvexCompact.le_sup_iff
      (Hyperplane.convex_stdSimplex (n + 1)) (Hyperplane.isCompact_stdSimplex _)
        (Hyperplane.zero_mem_interior_stdSimplex _) hx₀ _ ht'₀] at ht'
    rw [hx, ← hi] at ht'
    exact not_lt.2 ht' (ht i).1

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
