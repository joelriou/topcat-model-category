import TopCatModelCategory.Polar
import Mathlib.Topology.Maps.Basic

open Topology

lemma Real.abs_lt_iff (x y : ℝ) : abs x < y ↔ x < y ∧ - y < x := by
  refine ⟨fun h ↦ ⟨lt_of_le_of_lt (le_abs_self x) h, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [← neg_lt_neg_iff, neg_neg]
    exact lt_of_le_of_lt (neg_le_abs x) h
  · by_cases hx : 0 ≤ x
    · rwa [abs_of_nonneg hx]
    · rwa [abs_of_neg (by simpa using hx), ← neg_lt_neg_iff, neg_neg]

lemma Real.abs_le_iff (x y : ℝ) : abs x ≤ y ↔ x ≤ y ∧ - y ≤ x := by
  refine ⟨fun h ↦ ⟨(le_abs_self x).trans h, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [← neg_le_neg_iff, neg_neg]
    exact (neg_le_abs x).trans h
  · by_cases hx : 0 ≤ x
    · rwa [abs_of_nonneg hx]
    · rwa [abs_of_neg (by simpa using hx), ← neg_le_neg_iff, neg_neg]

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
lemma sup_smul {a : ℝ} (ha : 0 ≤ a) (v : E) :
    sup X (a • v) = a⁻¹ • sup X v := by
  by_cases hv : v = 0
  · subst hv
    simp [sup_zero hX₃]
  · by_cases ha₀ : a = 0
    · subst ha₀
      simp [sup_zero hX₃]
    · refine le_antisymm ?_ ?_
      · rw [smul_eq_mul, le_inv_mul_iff₀ (lt_of_le_of_ne ha (Ne.symm ha₀)),
          le_sup_iff hX₁ hX₂ hX₃ hv _ (mul_nonneg ha (zero_le_sup hX₂ hX₃ _))]
        have := sup_mem_set hX₂ hX₃ (a • v)
        rw [mem_set_iff, smul_smul, mul_comm] at this
        exact this.2
      · rw [le_sup_iff hX₁ hX₂ hX₃ (by simp; tauto)]
        · rw [smul_smul, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ ha₀, one_mul]
          have := sup_mem_set hX₂ hX₃ v
          rw [mem_set_iff] at this
          exact this.2
        · exact mul_nonneg (by positivity) (zero_le_sup hX₂ hX₃ v)

include hX₁ hX₂ hX₃ in
lemma zero_lt_sup {v : E} (hv : v ≠ 0) :
    0 < sup X v :=
  lt_of_le_of_ne (zero_le_sup hX₂ hX₃ v) (sup_ne_zero hX₁ hX₂ hX₃ hv).symm

namespace continuousOn

variable {v : E} (hv : v ≠ 0) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < sup X v)

include hv hε₀ hε hX₁ hX₂ hX₃

lemma upper_bound : ∃ δ > 0, ∀ (u : E), ‖u‖ < δ → sup X v - ε ≤ sup X (v + u) := by
  have hX := hX₃
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hX
  obtain ⟨α, hα₀, hα⟩ := hX
  let μ := sup X v
  have hμ₀ : 0 < μ := zero_lt_sup hX₁ hX₂ hX₃ hv
  have h : 0 < μ * (μ - ε) / ε := div_pos (mul_pos hμ₀ (by grind)) hε₀
  obtain ⟨δ, hδ₀, hδ₁, hδ₂⟩ : ∃ δ > 0, δ < ‖v‖ ∧ μ * (μ - ε) / ε * δ < α := by
    refine ⟨min (2⁻¹ * ‖v‖) (2⁻¹ * ((μ * (μ - ε) / ε)⁻¹ * α)), ?_, ?_, ?_⟩
    · rw [gt_iff_lt, lt_inf_iff]
      constructor
      · exact mul_pos (by simp) (by simpa)
      · exact mul_pos (by simp) (mul_pos (inv_pos.2 h) hα₀)
    · simp only [inv_div, inf_lt_iff]
      left
      rw [inv_mul_lt_iff₀ (by grind)]
      exact lt_two_mul_self (by simpa)
    · refine lt_of_le_of_lt
        (le_of_le_of_eq (mul_le_mul_of_nonneg_left (min_le_right _ _) h.le) ?_)
        ((inv_mul_lt_iff₀ (by simp)).2 (lt_two_mul_self hα₀))
      rw [← mul_assoc, ← mul_assoc, mul_comm _ 2⁻¹]
      nth_rw 2 [mul_assoc]
      rw [mul_inv_cancel₀ h.ne', mul_one]
  refine ⟨δ, hδ₀, fun u hu ↦ ?_⟩
  change μ - ε ≤ _
  have huv : v + u ≠ 0 := fun huv ↦ by
    rw [add_eq_zero_iff_eq_neg'] at huv
    subst huv
    simp only [norm_neg] at hu
    grind
  rw [le_sup_iff hX₁ hX₂ hX₃ huv _ (by grind)]
  let m : E := ((μ * (μ - ε)) / ε) • u
  have hm : m ∈ X := hα (by
    simp only [Metric.mem_ball, dist_zero_right, m, norm_smul,
      norm_div, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg hμ₀.le, abs_of_nonneg hε₀.le, abs_of_nonneg (by grind)]
    exact ((mul_lt_mul_left h).2 hu).trans hδ₂)
  convert hX₁ (sup_mem_set hX₂ hX₃ v).2 hm
    (a := (μ - ε) / μ) (div_nonneg (by grind) hμ₀.le)
    (div_nonneg hε₀.le hμ₀.le) (by grind) using 1
  have : ε / μ * (μ * (μ - ε) / ε) = μ - ε := by
    rw [mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ hμ₀.ne',
      mul_div_cancel₀ _ hε₀.ne']
  rw [smul_smul, smul_smul, div_mul_cancel₀ _ hμ₀.ne', this, smul_add]

lemma lower_bound : ∃ δ > 0, ∀ (u : E), ‖u‖ < δ → sup X (v + u) ≤ sup X v + ε := by
  have := hε
  have hX := hX₃
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hX
  obtain ⟨α, hα₀, hα⟩ := hX
  let μ := sup X v
  have hμ₀ : 0 < μ := zero_lt_sup hX₁ hX₂ hX₃ hv
  let β : ℝ := (μ + ε) * (2 * μ + ε) * ε⁻¹
  have hβ₀ : 0 < β := by positivity
  obtain ⟨δ, hδ₀, hδ₁, hδ₂⟩ : ∃ δ > 0, δ < ‖v‖ ∧ β * δ ≤ α := by
    refine ⟨min (2⁻¹ * ‖v‖) (β⁻¹ * α), by positivity,
      lt_of_le_of_lt (min_le_left _ _ )
        ((inv_mul_lt_iff₀ (by simp)).2 (lt_two_mul_self (by simpa))),
      le_of_le_of_eq (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ₀.le)
        (mul_inv_cancel_left₀ hβ₀.ne' α)⟩
  refine ⟨δ, hδ₀, fun u hu ↦ ?_⟩
  change _ ≤ μ + ε
  have huv : v + u ≠ 0 := fun huv ↦ by
    rw [add_eq_zero_iff_eq_neg'] at huv
    subst huv
    simp only [norm_neg] at hu
    grind
  by_contra! hu'
  replace hu' : (μ + ε) • (v + u) ∈ X := by
    rw [← le_sup_iff hX₁ hX₂ hX₃ huv _ (by positivity)]
    exact hu'.le
  apply not_imp_not.2 (le_sup_iff hX₁ hX₂ hX₃ hv (μ + 2⁻¹ * ε) (by positivity)).2
    (by simpa [μ])
  let m : E := - β • u
  have hm : m ∈ X := hα (by
    simp only [Metric.mem_ball, dist_zero_right, m, neg_smul, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hβ₀]
    exact lt_of_lt_of_le ((mul_lt_mul_left hβ₀).2 hu) hδ₂)
  convert hX₁ hu' hm (a := (2 * μ + ε) / (2 * (μ + ε))) (b := ε / (2 * (μ + ε)))
    (by positivity) (by positivity) (by grind) using 1
  have : (2 * μ + ε) / (2 * (μ + ε)) * (μ + ε) = μ + 2⁻¹ * ε := by
    apply mul_left_injective₀ (b := 2) (by simp)
    dsimp
    rw [mul_assoc, mul_comm (μ + ε) 2, div_mul_cancel₀ _ (by grind)]
    grind
  have hβ : β / (2 * (μ + ε)) = μ * ε⁻¹ + 2⁻¹ := by
    dsimp [β]
    rw [mul_comm 2 (μ + ε), ← div_div, mul_comm, mul_comm (μ + ε), ← mul_assoc,
      mul_div_cancel_right₀ _ (by grind), mul_add, add_div, inv_mul_cancel₀ hε₀.ne',
      one_div, mul_comm 2, ← mul_assoc, mul_div_cancel_right₀ _ (by grind), mul_comm]
  dsimp [m]
  rw [smul_smul, smul_smul, smul_add, mul_neg, neg_smul,
    add_assoc, ← sub_eq_add_neg, ← sub_smul, this,
    div_mul_comm, left_eq_add, hβ, add_mul, mul_assoc,
    inv_mul_cancel₀ hε₀.ne', mul_one, smul_eq_zero]
  left
  abel

end continuousOn

include hX₁ hX₂ hX₃ in
lemma continuousOn : ContinuousOn (sup X) {0}ᶜ := by
  intro v (hv : v ≠ 0) W hW
  obtain ⟨ε, hε₀, hε, hW⟩ : ∃ ε > 0, ε < sup X v ∧ Metric.closedBall (sup X v) ε ⊆ W := by
    rw [Metric.nhds_basis_closedBall.mem_iff] at hW
    obtain ⟨ε, hε₀, hε⟩ := hW
    refine ⟨min ε (2⁻¹ * sup X v), ?_, ?_, ?_⟩
    · simp only [gt_iff_lt, lt_inf_iff, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact ⟨hε₀, zero_lt_sup hX₁ hX₂ hX₃ hv⟩
    · exact lt_of_le_of_lt (min_le_right _ _) ((inv_mul_lt_iff₀ (by simp)).2
        (lt_two_mul_self (zero_lt_sup hX₁ hX₂ hX₃ hv)))
    · exact subset_trans (Metric.closedBall_subset_closedBall (min_le_left _ _)) hε
  obtain ⟨δ, hδ₀, hδ⟩ := continuousOn.upper_bound hX₁ hX₂ hX₃ hv ε hε₀ hε
  obtain ⟨δ', hδ'₀, hδ'⟩ := continuousOn.lower_bound hX₁ hX₂ hX₃ hv ε hε₀ hε
  rw [Filter.mem_map, Metric.mem_nhdsWithin_iff]
  refine ⟨min δ δ', by simp; grind, fun w ⟨h₁, h₂⟩ ↦ hW ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, w = v + u := ⟨w - v, by simp⟩
  simp only [Metric.mem_ball, dist_self_add_left, lt_inf_iff] at h₁
  simp only [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, Real.abs_le_iff]
  grind

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

section

open homeoClosedBallOfConvexCompact

variable [Nontrivial E] [ProperSpace E]

noncomputable def homeoClosedBallOfConvexCompact :
    X ≃ₜ Metric.closedBall (0 : E) 1 :=
  (isHomeomorph_inducedMap hX₁ hX₂ hX₃).homeomorph.symm

@[simp]
lemma homeoClosedBallOfConvexCompact_apply (x : unitInterval × (Metric.sphere 0 1)) :
    (homeoClosedBallOfConvexCompact hX₁ hX₂ hX₃).symm
      (polarParametrizationClosedBall E x) = map hX₁ hX₂ hX₃ x := by
  simp [homeoClosedBallOfConvexCompact]

@[simp]
lemma sup_homeoClosedBallOfConvexCompact_symm
    (x : Metric.closedBall (0 : E) 1) :
    sup X ((homeoClosedBallOfConvexCompact hX₁ hX₂ hX₃).symm x) = ‖x.1‖⁻¹ := by
  obtain ⟨⟨r, x⟩, rfl⟩ := (isQuotientMap_polarParametrizationClosedBall E).surjective x
  simp only [homeoClosedBallOfConvexCompact_apply, polarParametrizationClosedBall_apply_coe,
    norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one, map_apply_coe]
  rw [sup_smul hX₁ hX₂ hX₃ (mul_nonneg r.2.1 (zero_le_sup hX₂ hX₃ _)), smul_eq_mul]
  by_cases hr : r = 0
  · subst hr
    simp
  · refine (inv_mul_eq_iff_eq_mul₀ ?_).mpr ?_
    · simp only [ne_eq, mul_eq_zero, Set.Icc.coe_eq_zero, not_or]
      exact ⟨hr, sup_ne_zero hX₁ hX₂ hX₃ (by simp)⟩
    · rw [abs_of_nonneg r.2.1, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (by simpa), one_mul]

end

namespace retractionBoundaryOfConvexCompact

open homeoClosedBallOfConvexCompact

variable (X)

def boundary : Set E := sup X ⁻¹' {1}

@[simp]
lemma mem_boundary_iff (x : E) : x ∈ boundary X ↔ sup X x = 1 := Iff.rfl

variable {X}

def boundaryι (x : (boundary X : Type _)) : (({0}ᶜ : Set E) : Type _) :=
  ⟨x.1, by
    obtain ⟨x, hx⟩ := x
    simp only [mem_boundary_iff] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp [sup_zero hX₃] at hx⟩

lemma continuous_boundaryι : Continuous (boundaryι hX₃) :=
  Continuous.subtype_mk continuous_subtype_val _

variable [Nontrivial E] [ProperSpace E]

@[simp]
lemma homeoClosedBallOfConvexCompact_symm_mem_boundary_iff
    (x : Metric.closedBall (0 : E) 1) :
    ((homeoClosedBallOfConvexCompact hX₁ hX₂ hX₃).symm x).1 ∈ boundary X ↔
      ‖x.1‖ = 1 := by
  simp

noncomputable def retraction (x : (({0}ᶜ : Set E) : Type _)) : boundary X :=
  ⟨(homeoClosedBallOfConvexCompact hX₁ hX₂ hX₃).symm ⟨‖x.1‖⁻¹ • x.1, by
      simpa [norm_smul] using inv_mul_le_one⟩, by
    obtain ⟨x, hx⟩ := x
    simp [norm_smul, inv_mul_cancel₀ (a := ‖x‖) (by simpa using hx)]⟩

@[continuity]
lemma continuous_retraction : Continuous (retraction hX₁ hX₂ hX₃) :=
  Continuous.subtype_mk (continuous_subtype_val.comp
    ((Homeomorph.continuous_symm _).comp (Continuous.subtype_mk
      ((Continuous.inv₀ (by continuity) (by simp)).smul continuous_subtype_val) _))) _

@[simp]
lemma retraction_boundaryι_apply (x : boundary X) :
    retraction hX₁ hX₂ hX₃ (boundaryι hX₃ x) = x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨⟨r, x⟩, rfl⟩ := (isQuotientMap_polarParametrization E).surjective x
  ext
  dsimp [retraction, boundaryι, homeoClosedBallOfConvexCompact]
  by_cases hr : r = 0
  · subst hr
    simp
  · have h₁ := inducedMap_apply hX₁ hX₂ hX₃ ⟨1, x⟩
    rw [Subtype.ext_iff] at h₁
    convert h₁
    · simp [norm_smul, smul_smul, inv_mul_cancel₀ (a := (r : ℝ)) (by simpa)]
    · simp only [polarParametrization_apply, mem_boundary_iff] at hx
      rw [sup_smul hX₁ hX₂ hX₃ (by simp), smul_eq_mul,
        inv_mul_eq_one₀ (a := (r : ℝ)) (by simpa)] at hx
      simp [map_apply_coe, hx]

@[simp]
lemma retraction_comp_boundaryι :
    retraction hX₁ hX₂ hX₃ ∘ boundaryι hX₃ = id := by
  aesop

end retractionBoundaryOfConvexCompact

end NormedSpace
