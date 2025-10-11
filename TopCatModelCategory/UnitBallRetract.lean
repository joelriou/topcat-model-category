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

end Metric.closedBall

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
noncomputable def unitBallHomeo :
    Metric.ball (0 : E) 1 ≃ₜ E where
  toFun v := (1 - ‖v.1‖)⁻¹ • v
  invFun u := ⟨(1 + ‖u‖)⁻¹ • u, by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [inv_mul_lt_one₀ (by positivity), abs_of_pos (by positivity)]
    grind⟩
  left_inv v := by
    ext
    simp [smul_smul, norm_smul]
    rw [abs_of_pos (by
      simpa only [sub_pos, Metric.mem_ball, dist_zero_right] using v.2)]
    trans (1 : ℝ) • v
    · congr 1
      have : 1 - ‖v.1‖ ≠ 0 := by
        have := v.2
        simp only [Metric.mem_ball, dist_zero_right] at this
        rw [sub_ne_zero]
        intro hv'
        grind
      field_simp
      simp
    · rw [one_smul]
  right_inv u := by
    simp [smul_smul, norm_smul]
    rw [abs_of_pos (by positivity)]
    trans (1 : ℝ) • u
    · congr 1
      field_simp
      simp
    · rw [one_smul]
  continuous_toFun := by
    exact Continuous.smul (Continuous.inv₀ (by continuity) (by simp; grind)) continuous_subtype_val
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.smul (Continuous.inv₀ (by continuity) (by intro; positivity)) (by continuity)) _

noncomputable def openBallHomeoUnitBall (x : E) (e : ℝ) (he : 0 < e) :
    (Metric.ball x e) ≃ₜ Metric.ball (0 : E) 1 where
  toFun v := ⟨e⁻¹ • (v - x), by
    obtain ⟨v, hv⟩ := v
    simpa [dist_eq_norm, norm_smul, abs_of_pos he, inv_mul_lt_one₀ he] using hv⟩
  invFun u := ⟨x + e • u, by
    obtain ⟨u, hu⟩ := u
    simp only [Metric.mem_ball, dist_zero_right] at hu
    simpa [norm_smul, abs_of_pos he] using mul_lt_of_lt_one_right he hu⟩
  left_inv v := by
    ext
    simp [smul_smul, mul_inv_cancel₀ he.ne']
  right_inv u := by
    ext
    simp [smul_smul, inv_mul_cancel₀ he.ne']
  continuous_toFun := by exact (continuous_const.smul (by continuity)).subtype_mk _
  continuous_invFun :=
    by exact Continuous.subtype_mk (continuous_const.add (continuous_const.smul (by continuity))) _
