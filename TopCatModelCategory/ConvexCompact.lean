import TopCatModelCategory.Polar
import Mathlib.Topology.Maps.Basic

open Topology

universe u

namespace NormedSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Set E} (hX₁ : Convex ℝ X) (hX₂ : IsCompact X) (hX₃ : 0 ∈ interior X)

omit [NormedSpace ℝ E] in
@[simp]
lemma sphere_ne_zero (v : Metric.sphere (0 : E) 1) : v.1 ≠ 0 := by
  aesop

namespace homeoClosedBallOfConvexCompact

variable (X) in
def set (v : E) : Set ℝ := { t : ℝ | 0 ≤ t ∧ t • v ∈ X }

@[simp]
lemma mem_set_iff (v : E) (t : ℝ) : t ∈ set X v ↔ 0 ≤ t ∧ t • v ∈ X := Iff.rfl

include hX₃ in
lemma zero_mem_set (v : E) : 0 ∈ set X v := by
  simpa using interior_subset hX₃

include hX₁ hX₃ in
lemma mem_set_of_le {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (ht₁ : 0 ≤ t₁) {v : E}
    (ht₂ : t₂ ∈ set X v) :
    t₁ ∈ set X v := by
  obtain ⟨b, hb₀, hb₁, hb₂⟩ : ∃ (b : ℝ), 0 ≤ b ∧ b ≤ 1 ∧ b * t₂ = t₁ := by
    by_cases h' : t₂ = 0
    · subst h'
      obtain rfl : t₁ = 0 := le_antisymm h ht₁
      exact ⟨0, by simp⟩
    · exact ⟨t₁ / t₂, div_nonneg ht₁ (by grind), (div_le_one₀ (by grind)).2 h,
        div_mul_cancel₀ t₁ h'⟩
  use ht₁
  simpa [smul_smul, hb₂] using
    hX₁ (zero_mem_set hX₃ v).2 ht₂.2 (a := 1 - b) (by grind) hb₀ (by simp)

include hX₂ in
lemma bddAbove_set {v : E} (hv : v ≠ 0) : BddAbove (set X v) := by
  obtain ⟨r, hr, h⟩ := (IsCompact.isBounded hX₂).subset_ball_lt 0 0
  refine ⟨r / ‖v‖, fun t ⟨h₁, h₂⟩ ↦ ?_⟩
  have := h h₂
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁] at this
  rw [← mul_le_mul_iff_of_pos_right (a := ‖v‖) (by positivity)]
  exact le_of_le_of_eq this.le (div_mul_cancel₀ _ (by positivity)).symm

include hX₂ in
lemma isClosed_set (v : E) : IsClosed (set X v) :=
  IsClosed.inter isClosed_Ici
    (IsClosed.preimage (show Continuous (fun (t : ℝ) ↦ t • v) by continuity)
    (IsCompact.isClosed hX₂))

variable (X) in
noncomputable def sup (v : E) : ℝ := sSup (set X v)

include hX₂ hX₃ in
lemma isLUB_sup {v : E} (hv : v ≠ 0) : IsLUB (set X v) (sup X v) :=
  Real.isLUB_sSup (Set.nonempty_of_mem (zero_mem_set hX₃ v)) (bddAbove_set hX₂ hv)

include hX₃ in
lemma sup_zero : sup X 0 = 0 := by
  dsimp [sup, Real.sSup_def]
  apply dif_neg
  rintro ⟨_, ⟨x, hx⟩⟩
  simp only [mem_upperBounds, mem_set_iff, smul_zero, and_imp] at hx
  have hx₀ := hx 0 (by simp) (interior_subset hX₃)
  have := hx (x + 1) (by positivity) (interior_subset hX₃)
  grind

include hX₂ hX₃ in
lemma sup_mem_set (v : E) : sup X v ∈ set X v := by
  by_cases hv : v = 0
  · subst hv
    simpa [sup_zero hX₃] using interior_subset hX₃
  · exact IsClosed.csSup_mem (isClosed_set hX₂ v) (Set.nonempty_of_mem (zero_mem_set hX₃ v))
      (bddAbove_set hX₂ hv)

include hX₁ hX₂ hX₃ in
lemma le_sup_iff {v : E} (hv : v ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    t ≤ sup X v ↔ t • v ∈ X :=
  ⟨fun h ↦ (mem_set_of_le hX₁ hX₃ h ht (sup_mem_set hX₂ hX₃ v)).2,
    fun h ↦ (isLUB_sup hX₂ hX₃ hv).1 (by aesop)⟩

include hX₂ hX₃ in
lemma zero_le_sup (v : E) : 0 ≤ sup X v := (sup_mem_set hX₂ hX₃ v).1

include hX₁ hX₂ hX₃ in
lemma le_sup_of_ball_subset {v : E} (hv : v ≠ 0) (ε : ℝ) (_ : 0 < ε) (hε : Metric.ball 0 ε ⊆ X)
    (δ : ℝ) (hδ₀ : 0 ≤ δ) (h : δ * ‖v‖ < ε) : δ ≤ sup X v := by
  rw [le_sup_iff hX₁ hX₂ hX₃ hv δ hδ₀]
  exact hε (by simpa [norm_smul, abs_of_nonneg hδ₀])

include hX₁ hX₂ hX₃ in
lemma sup_ne_zero {v : E} (hv : v ≠ 0) :
    sup X v ≠ 0 := by
  have := hX₃
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at this
  obtain ⟨ε, hε₀, hε⟩ := this
  intro h
  obtain ⟨ε', hε'₀, hε'⟩ : ∃ (ε' : ℝ), 0 < ε' ∧ ε' * ‖v‖ < ε :=
    ⟨ε / (2 * ‖v‖), by positivity, by
      rw [← mul_lt_mul_iff_of_pos_right (a := 2) (by positivity), mul_assoc,
        mul_comm _ 2, div_mul_cancel₀ ε (by positivity)]
      grind⟩
  have := le_sup_of_ball_subset hX₁ hX₂ hX₃ hv ε hε₀ hε ε' hε'₀.le hε'
  rw [h] at this
  grind

include hX₁ hX₂ hX₃ in
lemma zero_lt_sup {v : E} (hv : v ≠ 0) :
    0 < sup X v :=
  lt_of_le_of_ne (zero_le_sup hX₂ hX₃ v) (sup_ne_zero hX₁ hX₂ hX₃ hv).symm

include hX₁ hX₂ hX₃ in
lemma continuousOn : ContinuousOn (sup X) {0}ᶜ := by
  have := hX₁
  have := hX₂
  have := hX₃
  sorry

@[simps -isSimp]
noncomputable def map : C(unitInterval × Metric.sphere (0 : E) 1, X) :=
  ⟨fun ⟨r, v⟩ ↦ ⟨((r : ℝ) * sup X v) • v, by
    simpa [smul_smul] using
      hX₁ (interior_subset hX₃) (sup_mem_set hX₂ hX₃ v).2 (a := 1 - r) (b := r)
        (by have := r.2.2; grind) r.2.1 (by simp)⟩,
    Continuous.subtype_mk (Continuous.smul (Continuous.mul (by continuity)
      ((continuousOn hX₁ hX₂ hX₃).comp_continuous
        continuous_subtype_val.snd' (by aesop))) (by continuity)) _⟩

@[simp]
lemma map_zero (v : Metric.sphere (0 : E) 1) :
    map hX₁ hX₂ hX₃ ⟨0, v⟩ = ⟨0, interior_subset hX₃⟩ := by
  simp [Subtype.ext_iff, map_apply_coe]

lemma map_coe_eq_zero_iff (x : unitInterval × Metric.sphere (0 : E) 1) :
    (map hX₁ hX₂ hX₃ x).1 = 0 ↔ x.1 = 0 := by
  rw [map_apply_coe, smul_eq_zero, mul_eq_zero, Set.Icc.coe_eq_zero]
  refine ⟨?_, by tauto⟩
  obtain ⟨r, v, hv⟩ := x
  rintro ((h | h) | h)
  · exact h
  · refine (sup_ne_zero hX₁ hX₂ hX₃ ?_ h).elim
    dsimp
    rintro rfl
    simp at hv
  · aesop

lemma factorsThrough :
    Function.FactorsThrough (map hX₁ hX₂ hX₃) (polarParametrizationClosedBall E) := by
  simp [NormedSpace.factorThrough_polarParametrizationClosedBall_iff]

variable [Nontrivial E] [ProperSpace E]

noncomputable def inducedMap : C(Metric.closedBall (0 : E) 1, X) :=
  (isQuotientMap_polarParametrizationClosedBall E).lift (map hX₁ hX₂ hX₃) (factorsThrough _ _ _)

@[simp]
lemma inducedMap_apply (x : unitInterval × Metric.sphere (0 : E) 1) :
    inducedMap hX₁ hX₂ hX₃ (polarParametrizationClosedBall E x) =
      map hX₁ hX₂ hX₃ x :=
  DFunLike.congr_fun ((isQuotientMap_polarParametrizationClosedBall E).lift_comp
    (map hX₁ hX₂ hX₃) (factorsThrough _ _ _)) x

@[simp]
lemma inducedMap_zero :
    (inducedMap hX₁ hX₂ hX₃ ⟨0, by simp⟩).1 = 0 := by
  simpa only [Subtype.ext_iff, map_zero, polarParametrizationClosedBall_zero]
    using inducedMap_apply hX₁ hX₂ hX₃ ⟨0, Classical.arbitrary _⟩

lemma bijective_inducedMap : Function.Bijective (inducedMap hX₁ hX₂ hX₃) := by
  constructor
  · intro x₁ x₂ h
    obtain ⟨⟨r₁, v₁⟩, rfl⟩ := (isQuotientMap_polarParametrizationClosedBall E).surjective x₁
    obtain ⟨⟨r₂, v₂⟩, rfl⟩ := (isQuotientMap_polarParametrizationClosedBall E).surjective x₂
    simp only [inducedMap_apply, Subtype.ext_iff] at h
    ext
    dsimp
    by_cases h₀ : (map hX₁ hX₂ hX₃ ⟨r₁, v₁⟩).1 = 0
    . rw [h₀] at h
      replace h := h.symm
      rw [map_coe_eq_zero_iff] at h h₀
      dsimp at h h₀
      subst h h₀
      aesop
    . have h₁ : r₁.1 ≠ 0 := by
        rw [map_coe_eq_zero_iff] at h₀
        aesop
      have h₂ : r₂.1 ≠ 0 := by
        rw [h, map_coe_eq_zero_iff] at h₀
        aesop
      simp only [map_apply_coe] at h
      rw [smul_sphere_eq_iff
        (mul_pos (by grind) (zero_lt_sup hX₁ hX₂ hX₃ (by simp)))
        (mul_pos (by grind) (zero_lt_sup hX₁ hX₂ hX₃ (by simp)))] at h
      obtain ⟨h, rfl⟩ := h
      rw [mul_left_injective₀ (sup_ne_zero hX₁ hX₂ hX₃ (by simp)) h]
  · rintro ⟨x, hx⟩
    by_cases hx₀ : x = 0
    · exact ⟨⟨0, by simp⟩, by aesop⟩
    · obtain ⟨r, hr, v, rfl⟩ :
          ∃ (r : ℝ) (hr : 0 < r) (v : Metric.sphere (0 : E) 1), x = r • v := by
        refine ⟨‖x‖, by positivity, ⟨‖x‖⁻¹ • x, ?_⟩, ?_⟩
        · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (by positivity)]
        · rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      obtain ⟨t, ht₀, ht, ht₁⟩ : ∃ (t : ℝ), 0 ≤ t ∧ t * sup X v = r ∧ t ≤ 1 := by
        refine ⟨r / sup X v, div_nonneg hr.le (zero_le_sup hX₂ hX₃ v),
          div_mul_cancel₀ _ (sup_ne_zero hX₁ hX₂ hX₃ (by simp)), ?_⟩
        rwa [div_le_one₀ (zero_lt_sup hX₁ hX₂ hX₃ (by simp)),
          le_sup_iff hX₁ hX₂ hX₃ (by simp) _ hr.le]
      exact ⟨polarParametrizationClosedBall E ⟨⟨t, ht₀, ht₁⟩, v⟩,
        by ext; simp [map_apply_coe, ht]⟩

lemma isHomeomorph_inducedMap : IsHomeomorph (inducedMap hX₁ hX₂ hX₃) := by
  have := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : E) 1)
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨by continuity, bijective_inducedMap _ _ _⟩

end homeoClosedBallOfConvexCompact

variable [Nontrivial E] [ProperSpace E]

open homeoClosedBallOfConvexCompact in
noncomputable def homeoClosedBallOfConvexCompact :
    X ≃ₜ Metric.closedBall (0 : E) 1 :=
  (isHomeomorph_inducedMap hX₁ hX₂ hX₃).homeomorph.symm

end NormedSpace
