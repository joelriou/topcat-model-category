import Mathlib.Analysis.Normed.Module.Basic

universe u

open Topology NNReal

namespace NormedSpace

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PolarParametrization

@[simps]
def param : C(ℝ≥0 × Metric.sphere (0 : E) 1, E) where
  toFun := fun ⟨t, u⟩ ↦ (t : ℝ) • u

noncomputable def homeo :
    Homeomorph ((Set.Ioi (0 : ℝ)) × Metric.sphere (0 : E) 1) ({0}ᶜ : Set E) where
  toFun := fun ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ ↦ ⟨t • u, by aesop⟩
  invFun := fun ⟨v, hv⟩ ↦ ⟨⟨‖v‖, by aesop⟩, ⟨‖v‖ ⁻¹ • v, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv; simp [hv, norm_smul]⟩⟩
  left_inv := fun ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ ↦ by
    simp only [Set.mem_Ioi] at ht
    simp only [mem_sphere_iff_norm, sub_zero] at hu
    ext
    · dsimp
      rw [norm_smul, hu, mul_one]
      simpa only [Real.norm_eq_abs, abs_eq_self] using ht.le
    · dsimp
      rw [smul_smul, norm_smul, hu, Real.norm_eq_abs, mul_one,
        abs_eq_self.2 ht.le, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  right_inv := fun ⟨v, hv⟩ ↦ by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    aesop
  continuous_toFun := by continuity
  continuous_invFun := by
    apply Continuous.prodMk
    · continuity
    · apply Continuous.subtype_mk
      exact Continuous.smul (Continuous.inv₀ (by continuity) (by simp))
        (continuous_subtype_val)

@[simps]
def param.p₁ : C(ℝ≥0 × Metric.sphere (0 : E) 1, ℝ≥0) where
  toFun := fun ⟨t, u⟩ ↦ t

@[simp]
lemma preimage_param_zero : (param E) ⁻¹' {0} = param.p₁ E ⁻¹' {0}  := by aesop

variable {E} [Nontrivial E]

instance (u : E) (r : ℝ≥0) [Nontrivial E] : Nonempty (Metric.sphere (u : E) r) := by
  wlog hu : u = 0 generalizing u
  · obtain ⟨v, hv⟩ := this _ rfl
    exact ⟨⟨u + v, by simpa using hv⟩⟩
  subst hu
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  exact ⟨⟨(r : ℝ) • (‖v‖ ⁻¹ • v), by simp [hv, norm_smul]⟩⟩

instance (u : E) : Nonempty (Metric.sphere (u : E) 1) :=
  inferInstanceAs (Nonempty (Metric.sphere (u : E) (1 : ℝ≥0)))

lemma param_surjective : Function.Surjective (param E) := fun v ↦ by
  wlog hv : v ≠ 0 generalizing v
  · obtain rfl : v = 0 := by simpa using hv
    exact ⟨⟨0, Classical.arbitrary _⟩, by simp⟩
  exact ⟨⟨⟨‖v‖, by simp⟩, ⟨‖v‖ ⁻¹ • v, by simp [hv, norm_smul]⟩⟩, by simp [hv]⟩

/-lemma param_isQuotientMap_aux
    (U : Set E) (hU₀ : 0 ∈ U) (hU : IsOpen ((param E) ⁻¹' U)) :
    ∃ ε > 0, Metric.ball 0 ε ≤ U := by
  sorry

variable (E)

lemma param_isQuotientMap [ProperSpace E] :
    IsQuotientMap (param E) := by
  rw [isQuotientMap_iff]
  refine ⟨param_surjective,
    fun U ↦ ⟨fun hU ↦ (param E).continuous.isOpen_preimage U hU, fun hU ↦ ?_⟩⟩
  wlog hU₀ : 0 ∉ U generalizing U with h₁; swap
  · -- use `homeo E`
    sorry
  simp only [not_not] at hU₀
  obtain ⟨ε, h₃, h₃⟩ := param_isQuotientMap_aux U hU₀ hU
  replace h₁ := h₁ (U ∩ {0}ᶜ) (by
    simp only [Set.preimage_inter, Set.preimage_compl]
    apply IsOpen.inter hU
    simp only [isOpen_compl_iff, preimage_param_zero]
    exact IsClosed.preimage (param.p₁ E).continuous isClosed_singleton) (by simp)
  convert IsOpen.union h₁ (Metric.isOpen_ball (x := (0 : E)) (ε := ε))
  ext u
  by_cases hu : u = 0
  · subst hu
    simp
    tauto
  · constructor
    · simp
      tauto
    · rintro (hu | hu)
      · exact hu.1
      · exact h₃ hu-/

end PolarParametrization

end NormedSpace
