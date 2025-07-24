import TopCatModelCategory.TopCat.Cosimp
import TopCatModelCategory.TopCat.Monoidal
import Mathlib.AlgebraicTopology.TopologicalSimplex

universe u

open BigOperators NNReal

namespace TopCat

namespace cosimp

section

variable {n : SimplexCategory} (s : SimplexCategory.toTopObj n)

def objOfToTopObj (i : Fin (n.len + 2)) : ℝ :=
  (Finset.univ.filter (fun (j : Fin _) ↦ j.castSucc < i)).sum (fun j ↦ s.1 j)

@[simp]
lemma objOfToTopObj_zero : objOfToTopObj s 0 = 0 := by simp [objOfToTopObj]

@[simp]
lemma objOfToTopObj_last : objOfToTopObj s (Fin.last _) = 1 := by
  obtain ⟨s, hs⟩ := s
  simp only [SimplexCategory.toTopObj, Set.mem_setOf_eq] at hs
  let coeℝ : ℝ≥0 →+ ℝ := AddMonoidHom.mk' (fun (x : ℝ≥0) ↦ x.1) (by aesop)
  have := map_sum coeℝ s Finset.univ
  simp only [hs, val_eq_coe, AddMonoidHom.mk'_apply, coe_one, coeℝ] at this
  simp only [this, objOfToTopObj]
  congr
  ext i
  simpa using i.castSucc_lt_last

@[simp]
lemma objOfToTopObj_succ (i : Fin (n.len + 1)) :
    objOfToTopObj s i.succ = objOfToTopObj s i.castSucc + (s.1 i).1 := by
  simp only [objOfToTopObj]
  simp only [Fin.castSucc_lt_succ_iff, Fin.castSucc_lt_castSucc_iff, val_eq_coe]
  rw [Finset.sum_eq_add_sum_diff_singleton (i := i) (by simp), add_comm]
  congr
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  omega

lemma monotone_objOfToTopObj : Monotone (objOfToTopObj s) := by
  simp [Fin.monotone_iff]

lemma objOfToTopObj_mem_unitInterval (i : Fin (n.len + 2)) :
    objOfToTopObj s i ∈ unitInterval := by
  simp only [Fin.coe_eq_castSucc, Set.mem_Icc]
  constructor
  · rw [← objOfToTopObj_zero s]
    exact monotone_objOfToTopObj _ (Fin.zero_le _)
  · rw [← objOfToTopObj_last s]
    exact monotone_objOfToTopObj _ (Fin.le_last _)

end

def objUnitIntervalHomeomorph (n : SimplexCategory) :
     SimplexCategory.toTopObj n ≃ₜ obj unitInterval n where
  toFun s := ⟨⟨fun i ↦ ⟨objOfToTopObj s i, objOfToTopObj_mem_unitInterval s i⟩,
    monotone_objOfToTopObj s⟩, by aesop⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [OrderHom.continuous_iff]
    intro i
    apply Continuous.subtype_mk
    apply continuous_finset_sum
    intro i hi
    apply Continuous.comp
    · exact continuous_coe
    · exact (_root_.continuous_apply _).comp continuous_subtype_val
  continuous_invFun := sorry

end cosimp

end TopCat
