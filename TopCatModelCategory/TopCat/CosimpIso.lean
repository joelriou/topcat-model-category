import Mathlib.Data.NNReal.Basic
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.Cosimp
import TopCatModelCategory.TopCat.Monoidal
import Mathlib.AlgebraicTopology.TopologicalSimplex

universe u

open NNReal CategoryTheory

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
  rw [Subtype.ext_iff] at hs
  simp only [val_eq_coe, coe_sum, coe_one] at hs
  rw [← hs, objOfToTopObj]
  congr
  ext i
  simpa using i.castSucc_lt_last

@[simp]
lemma objOfToTopObj_succ (i : Fin (n.len + 1)) :
    objOfToTopObj s i.succ = objOfToTopObj s i.castSucc + (s.1 i).1 := by
  simp only [objOfToTopObj, Fin.castSucc_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, val_eq_coe]
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

lemma isHomeomorph_objUnitInterval (n : SimplexCategory) :
  IsHomeomorph (X := SimplexCategory.toTopObj n) (Y := obj unitInterval n)
    (fun s ↦ ⟨⟨fun i ↦ ⟨objOfToTopObj s i, objOfToTopObj_mem_unitInterval s i⟩,
      monotone_objOfToTopObj s⟩, by aesop⟩) := by
  rw [isHomeomorph_iff_continuous_bijective]
  constructor
  · apply Continuous.subtype_mk
    rw [OrderHom.continuous_iff]
    intro i
    apply Continuous.subtype_mk
    apply continuous_finset_sum
    intro i hi
    apply Continuous.comp
    · exact continuous_coe
    · exact (_root_.continuous_apply _).comp continuous_subtype_val
  · constructor
    · intro s t h
      simp only [Subtype.ext_iff, OrderHom.mk.injEq, funext_iff] at h
      ext i
      simpa only [← h, objOfToTopObj_succ s i, add_right_inj] using objOfToTopObj_succ t i
    · intro f
      let s (i : Fin (n.len + 1)) : ℝ := (f.1 i.succ).1 - (f.1 i.castSucc).1
      have hs₀ (i) : 0 ≤ s i := sub_nonneg_of_le (f.1.monotone i.castSucc_le_succ)
      have hs₁ (i : Fin (n.len + 2)) :
          (Finset.univ.filter (fun (j : Fin _) ↦ j.castSucc < i)).sum (fun j ↦ s j) = f.1 i := by
        induction i using Fin.induction with
        | zero => simp [f.2.1]
        | succ l hi =>
          rw [Finset.sum_eq_add_sum_diff_singleton (i := l) (by simp), ← eq_sub_iff_add_eq']
          convert hi using 2
          · ext j
            simp only [Fin.castSucc_lt_succ_iff, Finset.mem_sdiff, Finset.mem_filter,
              Finset.mem_univ, true_and, Finset.mem_singleton, Fin.castSucc_lt_castSucc_iff]
            omega
          · simp [s]
      refine ⟨⟨(fun i ↦ ⟨s i, hs₀ i⟩), ?_⟩, by ext; apply hs₁⟩
      have := hs₁ (Fin.last _)
      simp only [f.2.2] at this
      simp only [SimplexCategory.toTopObj, Set.mem_setOf_eq]
      rw [Subtype.ext_iff]
      simp only [val_eq_coe, coe_sum, coe_mk, coe_one, s]
      convert this using 1
      congr
      ext i
      simpa using i.castSucc_lt_last

noncomputable def objUnitIntervalHomeomorph (n : SimplexCategory) :
     SimplexCategory.toTopObj n ≃ₜ obj unitInterval n :=
  (isHomeomorph_objUnitInterval n).homeomorph

noncomputable def toTopIso : SimplexCategory.toTop ≅ cosimp unitInterval :=
  NatIso.ofComponents (fun n ↦ TopCat.isoOfHomeo (objUnitIntervalHomeomorph _)) (fun {n m} g ↦ by
    ext f
    dsimp [objUnitIntervalHomeomorph] at f ⊢
    ext i
    dsimp [objOfToTopObj]
    simp only [coe_sum]
    rw [← Finset.sum_disjiUnion]; swap
    · intro a ha b hb h i hia hib x hx
      have h₁ := hia hx
      have h₂ := hib hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact (h (by rw [← h₁, h₂])).elim
    congr
    ext j
    simp only [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_eq_right']
    exact (SimplexCategory.II.castSucc_lt_map_apply g i j).symm)

end cosimp

end TopCat
