import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

universe u

open Topology

lemma Topology.IsQuotientMap.retraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (r : C(X, Y)) (s : C(Y, X)) (hrs : r.comp s = .id _) :
    IsQuotientMap r := by
  refine ⟨fun y ↦ ⟨s y, DFunLike.congr_fun hrs y⟩, ?_⟩
  ext U
  change IsOpen U ↔ IsOpen (r ⁻¹' U)
  refine ⟨fun h ↦ r.continuous.isOpen_preimage U h,
    fun h ↦ ?_⟩
  convert s.continuous.isOpen_preimage _ h
  simp [← Set.preimage_comp, ← ContinuousMap.coe_comp, hrs]

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Metric.closedBall

noncomputable def retraction (v : E) : Metric.closedBall (0 : E) 1 :=
  if hv : ‖v‖ ≤ 1 then ⟨v, by simpa using hv⟩ else ⟨‖v‖⁻¹ • v, by
    simpa [norm_smul] using inv_mul_le_one⟩

variable {E}

lemma retraction_of_dist_le_one (v : E) (hv : ‖v‖ ≤ 1) :
    retraction E v = ⟨v, by simpa using hv⟩ := by
  dsimp [retraction]
  aesop

lemma retraction_of_one_le_dist (v : E) (hv : 1 ≤ ‖v‖) :
    retraction E v = ⟨‖v‖⁻¹ • v, by simpa [norm_smul] using inv_mul_le_one⟩ := by
  obtain hv | hv := hv.lt_or_eq
  · exact dif_neg (by aesop)
  · simp [retraction_of_dist_le_one v (by grind), hv.symm]

variable (E)

lemma retraction_restrict_closedBall :
    (closedBall 0 1).restrict (retraction E) = fun v ↦ v := by
  ext v
  dsimp
  rw [retraction_of_dist_le_one _ (by simpa [closedBall] using v.2)]

@[continuity]
lemma continuous_retraction : Continuous (retraction E) := by
  rw [← continuousOn_univ]
  have : Set.univ = Metric.closedBall (0 : E) 1 ∪ { v | 1 ≤ ‖v‖} := by
    ext
    simpa using LinearOrder.le_total _ _
  rw [this]
  apply ContinuousOn.union_of_isClosed _ _ isClosed_closedBall
    (isClosed_le (by continuity) (by continuity))
  · have : (closedBall 0 1).restrict (retraction E) = id := by
      ext v
      dsimp
      rw [retraction_of_dist_le_one _ (by simpa [closedBall] using v.2)]
    rw [continuousOn_iff_continuous_restrict,
      retraction_restrict_closedBall]
    continuity
  · have : ({v | 1 ≤ ‖v‖}.restrict (retraction E)) =
        fun v ↦ ⟨‖v.1‖⁻¹ • v, by simpa [norm_smul] using inv_mul_le_one⟩ := by
      ext v
      dsimp
      rw [retraction_of_one_le_dist _ v.2]
    rw [continuousOn_iff_continuous_restrict, this]
    refine Continuous.subtype_mk (Continuous.smul (Continuous.inv₀ (by continuity) ?_)
      continuous_induced_dom) _
    rintro ⟨x, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    grind

@[simp]
lemma retraction_apply (x : Metric.closedBall (0 : E) 1) :
    retraction E x = x :=
  retraction_of_dist_le_one _ (by simpa [closedBall] using x.2)

lemma retraction_isQuotientMap :
    IsQuotientMap (retraction E) :=
  IsQuotientMap.retraction ⟨retraction E, by continuity⟩ ⟨Subtype.val, by continuity⟩
    (by aesop)

instance (n : ℕ) : DeltaGeneratedSpace (Fin n → ℝ) where
  le_deltaGenerated U hU := by
    rw [isOpen_deltaGenerated_iff] at hU
    exact hU n (.id _)

instance [FiniteDimensional ℝ E] : DeltaGeneratedSpace E := by
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₜ E :=
    AffineEquiv.toHomeomorphOfFiniteDimensional
      (finDimVectorspaceEquiv _ (by simp)).symm.toAffineEquiv
  exact e.isQuotientMap.deltaGeneratedSpace

instance [FiniteDimensional ℝ E] :
    DeltaGeneratedSpace (Metric.closedBall (0 : E) 1) :=
  (retraction_isQuotientMap E).deltaGeneratedSpace

end Metric.closedBall
