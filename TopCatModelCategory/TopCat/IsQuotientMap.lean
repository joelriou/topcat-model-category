import Mathlib.Analysis.Normed.Module.FiniteDimension

universe u

open Topology NNReal

lemma Homeomorph.isOpen_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (U : Set Y) :
    IsOpen (e ⁻¹' U) ↔ IsOpen U := by
  simp only [isOpen_preimage]

namespace NormedSpace

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simps]
def polarParametrization : C(ℝ≥0 × Metric.sphere (0 : E) 1, E) where
  toFun := fun ⟨t, u⟩ ↦ (t : ℝ) • u

namespace polarParametrization

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
def p₁ : C(ℝ≥0 × Metric.sphere (0 : E) 1, ℝ≥0) where
  toFun := fun ⟨t, u⟩ ↦ t

@[simp]
lemma preimage_param_zero : (polarParametrization E) ⁻¹' {0} = p₁ E ⁻¹' {0}  := by aesop

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

lemma param_surjective : Function.Surjective (polarParametrization E) := fun v ↦ by
  wlog hv : v ≠ 0 generalizing v
  · obtain rfl : v = 0 := by simpa using hv
    exact ⟨⟨0, Classical.arbitrary _⟩, by simp⟩
  exact ⟨⟨⟨‖v‖, by simp⟩, ⟨‖v‖ ⁻¹ • v, by simp [hv, norm_smul]⟩⟩, by simp [hv]⟩

lemma param_isQuotientMap_aux
    (U : Set E) (hU₀ : 0 ∈ U) (hU : IsOpen ((polarParametrization E) ⁻¹' U)) :
    ∃ ε > 0, Metric.ball 0 ε ⊆ U := by
  sorry

variable (E)

lemma param_isQuotientMap [ProperSpace E] :
    IsQuotientMap (polarParametrization E) := by
  rw [isQuotientMap_iff]
  refine ⟨param_surjective,
    fun U ↦ ⟨fun hU ↦ (polarParametrization E).continuous.isOpen_preimage U hU, fun hU ↦ ?_⟩⟩
  wlog hU₀ : 0 ∉ U generalizing U with h₁; swap
  · let s : Set E := {0}ᶜ
    let j : s → E := Subtype.val
    have hj : IsOpenEmbedding j := isOpen_compl_singleton.isOpenEmbedding_subtypeVal
    refine  (hj.isOpen_iff_preimage_isOpen (s := U) (fun u hu ↦ by
      simp [j, s]
      rintro rfl
      exact hU₀ hu)).2 ?_
    rw [← (homeo E).isOpen_preimage]
    let f : ((Set.Ioi (0 : ℝ)) × Metric.sphere (0 : E) 1) →
      (ℝ≥0 × Metric.sphere (0 : E) 1) := fun ⟨a, b⟩ ↦ ⟨⟨a.1, by grind⟩, b⟩
    have hf : IsOpenEmbedding f := by
      constructor
      · exact Isometry.isEmbedding (by tauto)
      · have : Set.range f = { x | x.1 ≠ 0 } := by
          ext ⟨x, y, hy⟩
          simp only [mem_sphere_iff_norm, sub_zero] at hy
          simp
          constructor
          · rintro ⟨a, ha, b, hb, h⟩ rfl
            rw [Prod.ext_iff, Subtype.ext_iff] at h
            simp [f] at h
            obtain rfl : a = 0 := h.1
            simp at ha
          · intro hx
            exact ⟨x, lt_of_le_of_ne x.2 (Ne.symm (by simpa)), y, hy, rfl⟩
        rw [this]
        apply isOpen_ne_fun
        all_goals continuity
    rwa [hf.isOpen_iff_preimage_isOpen] at hU
    intro x hx
    simp at hx
    refine ⟨⟨⟨x.1, ?_⟩, x.2⟩, rfl⟩
    obtain h | h := x.1.2.lt_or_eq
    · simpa
    · dsimp at h
      rw [← h, zero_smul] at hx
      exact (hU₀ hx).elim
  simp only [not_not] at hU₀
  obtain ⟨ε, h₃, h₃⟩ := param_isQuotientMap_aux U hU₀ hU
  replace h₁ := h₁ (U ∩ {0}ᶜ) (by
    simp only [Set.preimage_inter, Set.preimage_compl]
    apply IsOpen.inter hU
    simp only [isOpen_compl_iff, preimage_param_zero]
    exact IsClosed.preimage (p₁ E).continuous isClosed_singleton) (by simp)
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
      · exact h₃ hu

end polarParametrization

end NormedSpace
