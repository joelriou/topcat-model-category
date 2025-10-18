import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TopCatModelCategory.TopCat.Adj

open Simplicial

namespace SimplexCategory

variable (n : ℕ)

@[simps]
def sumCoordinates : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

noncomputable abbrev hyperplane : Submodule ℝ (Fin (n + 1) → ℝ) :=
  LinearMap.ker (sumCoordinates n)

abbrev Hyperplane : Type _ := hyperplane n

namespace Hyperplane

variable {n} in
@[simp]
lemma sum_eq_zero (x : Hyperplane n) : ∑ i, x.1 i = 0 := by
  simpa only [LinearMap.mem_ker, sumCoordinates_apply] using x.2

noncomputable instance : Unique (Hyperplane 0) where
  uniq x := by
    ext i
    fin_cases i
    simpa using sum_eq_zero x

instance (n : ℕ) : Nontrivial (Hyperplane (n + 1)) where
  exists_pair_ne := ⟨0, ⟨Fin.cases (- (n + 1)) (fun _ ↦ 1), by
    simp [Fin.sum_univ_succ]
    abel⟩, fun h ↦ by
      rw [Subtype.ext_iff] at h
      have : (1 : ℝ) ≤ 0 := le_of_le_of_eq (by simp) (neg_eq_zero.1 (congr_fun h.symm 0))
      grind⟩

def stdSimplex : Set (Hyperplane n) :=
  setOf (fun x ↦ ∀ (i : Fin (n + 1)), 0 ≤ (n + 1) • x.1 i + 1)

variable {n} in
lemma mem_stdSimplex_iff (x : Hyperplane n) :
    x ∈ stdSimplex n ↔ ∀ (i : Fin (n + 1)), 0 ≤ (n + 1) • x.1 i + 1 := Iff.rfl

variable {n} in
@[continuity]
lemma continuous_apply (i : Fin (n + 1)) :
    Continuous (fun (x : Hyperplane n) ↦ x.1 i) :=
  (_root_.continuous_apply _ ).comp continuous_subtype_val

namespace stdSimplex

instance : Unique (stdSimplex 0) where
  default := ⟨0, by simp [mem_stdSimplex_iff]⟩
  uniq := by
    rintro ⟨x, hx⟩
    ext i
    fin_cases i
    simpa using sum_eq_zero x

variable {n}

lemma zero_le (x : stdSimplex n) (i : Fin (n + 1)) :
    0 ≤ (n + 1) • x.1.1 i + 1 :=
  (mem_stdSimplex_iff _).1 x.2 i

@[continuity]
lemma continuous_apply (i : Fin (n + 1)) :
    Continuous (fun (x : stdSimplex n) ↦ x.1.1 i) :=
  (Hyperplane.continuous_apply i).comp continuous_subtype_val

end stdSimplex

noncomputable def stdSimplexHomeo : stdSimplex n ≃ₜ _root_.stdSimplex ℝ (Fin (n + 1)) where
  toFun x := ⟨fun i ↦ x.1.1 i + 1 / (n + 1), fun i ↦ by
    rw [← mul_nonneg_iff_of_pos_left (c := (n + 1 : ℝ)) (by positivity)]
    simpa [mul_add, mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)] using x.2 i, by
    simp [Finset.sum_add_distrib, mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)]⟩
  invFun x := ⟨⟨fun i ↦ x.1 i - 1 / (n + 1), by
    simp [mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)]⟩, fun i ↦ by
    simp [mul_sub, mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)]
    exact mul_nonneg (by positivity) (x.2.1 i)⟩
  left_inv _ := by ext; simp
  right_inv x := by ext; simp; rfl
  continuous_toFun := by continuity
  continuous_invFun := by continuity

instance : CompactSpace (stdSimplex n) := (stdSimplexHomeo n).symm.compactSpace

lemma isCompact_stdSimplex : IsCompact (stdSimplex n) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

lemma convex_stdSimplex : Convex ℝ (stdSimplex n) := by
  intro x hx y hy a b ha hb h
  rw [mem_stdSimplex_iff] at hx hy ⊢
  intro i
  refine le_of_eq_of_le (by simp)
    (le_of_le_of_eq ((add_le_add (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)))) ?_)
  simp only [mul_add, mul_one, nsmul_eq_mul, Submodule.coe_add, SetLike.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
  rw [← mul_comm a, ← mul_comm b, ← h]
  abel

lemma zero_mem_interior_stdSimplex : 0 ∈ interior (stdSimplex n) := by
  let ε : ℝ := 1 / (n + 1)
  have hε : ((n : ℝ) + 1) * ε = 1 := by
    dsimp [ε]
    rw [one_div, mul_inv_cancel₀ (by positivity)]
  have hε₀ : 0 < ε := by
    simp [ε]
    positivity
  rw [mem_interior]
  refine ⟨Metric.ball 0 ε, fun p hp ↦ ?_, Metric.isOpen_ball, by aesop⟩
  simp only [Metric.mem_ball, dist_zero_right, AddSubgroupClass.coe_norm] at hp
  rw [mem_stdSimplex_iff]
  intro i
  have : - ε ≤ p.1 i := by
    simp only [pi_norm_lt_iff hε₀, Real.norm_eq_abs] at hp
    exact (neg_le_neg_iff.2 ((hp i).le)).trans (neg_abs_le (p.1 i))
  rw [← mul_le_mul_iff_of_pos_left (a := (n + 1 : ℝ)) (by positivity),
    ← add_le_add_iff_right 1] at this
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  refine le_trans ?_ this
  simp only [mul_neg, le_neg_add_iff_add_le, add_zero, le_refl, hε]

end Hyperplane

end SimplexCategory
