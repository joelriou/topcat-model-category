import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

universe u

open CategoryTheory Simplicial

namespace CategoryTheory

variable {X : Type*} [Category X]

lemma nerve_δ_obj {n : ℕ} (i : Fin (n + 2)) (x : (nerve X) _⦋n + 1⦌) (j : Fin (n + 1)):
    ((nerve X).δ i x).obj j = x.obj (i.succAbove j) := by
  rfl

lemma nerve_σ_obj {n : ℕ} (i : Fin (n + 1)) (x : (nerve X) _⦋n⦌) (j : Fin (n + 2)):
    ((nerve X).σ i x).obj j = x.obj (i.predAbove j) := by
  rfl

end CategoryTheory

@[ext]
lemma Preorder.nerveExt {X : Type u} [Preorder X]
    {n : SimplexCategoryᵒᵖ} {s t : (nerve X).obj n} (h : s.obj = t.obj) :
    s = t :=
  ComposableArrows.ext (by simp [h]) (fun _ _ ↦ rfl)

namespace PartialOrder

section

variable (X : Type u) [PartialOrder X]

def NonemptyFiniteChains : Type u :=
  { A : Finset X // Nonempty A ∧ ∀ (a b : A), a ≤ b ∨ b ≤ a }

namespace NonemptyFiniteChains

variable {X} (A : NonemptyFiniteChains X)

instance nonempty : Nonempty A.1 := A.2.1

instance : PartialOrder (NonemptyFiniteChains X) := Subtype.partialOrder _

@[simp]
lemma le_iff (A B : NonemptyFiniteChains X) : A ≤ B ↔ A.1 ⊆ B.1 := Iff.rfl

noncomputable instance [DecidableLE X] : LinearOrder A.1 where
  le_total := A.2.2
  decidableLE a b := by infer_instance

variable [DecidableLE X]

noncomputable def max : A.1 := Finset.max' (α := A.1) .univ (by
  simpa [Finset.nonempty_coe_sort] using A.nonempty)

lemma le_max (x : A.1) : x ≤ A.max :=
  Finset.le_max' (α := A.1) .univ x (by simp)

@[simps]
noncomputable def orderHomMax : NonemptyFiniteChains X →o X where
  toFun A := A.max.1
  monotone' A B h := B.le_max ⟨A.max, h A.max.2⟩

end NonemptyFiniteChains

variable {X}

lemma mem_nonDegenerate_iff {n : ℕ} (s : (nerve X) _⦋n⦌) :
    s ∈ (nerve X).nonDegenerate n ↔ StrictMono s.obj := by
  obtain _ | n := n
  · simp only [nerve_obj, SimplexCategory.len_mk, SSet.nondegenerate_zero, Set.top_eq_univ,
      Set.mem_univ, Nat.reduceAdd, true_iff]
    intro a b h
    fin_cases a
    fin_cases b
    simp at h
  · refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      obtain h | h := (s.monotone i.castSucc_le_succ).lt_or_eq
      · exact h
      · exfalso
        apply hs
        simp only [SSet.degenerate_eq_iUnion_range_σ,
          Set.mem_iUnion, Set.mem_range]
        refine ⟨i, (nerve X).δ i.castSucc s, ?_⟩
        ext j
        dsimp [nerve_σ_obj, nerve_δ_obj]
        by_cases h' : j ≤ i.castSucc
        · rw [Fin.predAbove_of_le_castSucc _ _ h']
          obtain ⟨j, rfl⟩ :=
            Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt (Fin.le_castSucc_iff.1 h'))
          simp only [SimplexCategory.len_mk, Fin.castSucc_le_castSucc_iff] at h'
          simp only [Fin.castPred_castSucc]
          obtain h' | rfl := h'.lt_or_eq
          · rw [Fin.succAbove_castSucc_of_lt _ _ h']
          · rw [h, Fin.succAbove_castSucc_of_le _ _ h']
        · simp only [not_le] at h'
          rw [Fin.predAbove_of_castSucc_lt _ _ h']
          obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h')
          rw [Fin.pred_succ, Fin.succAbove_of_lt_succ _ _ h']
    · simp only [SSet.mem_nonDegenerate_iff_not_mem_degenerate,
        SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range, not_exists]
      rintro i x rfl
      exact (hs i.castSucc_lt_succ).ne (by simp [nerve_σ_obj])

lemma mem_nonDegenerate_δ {n : ℕ} (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 2))
    (hs : s ∈ (nerve X).nonDegenerate (n + 1)) :
    (nerve X).δ i s ∈ (nerve X).nonDegenerate n := by
  rw [mem_nonDegenerate_iff] at hs ⊢
  exact hs.comp (Fin.succAboveOrderEmb i).strictMono

end

namespace NonemptyFiniteChains

variable {X : Type u} [LinearOrder X] [Fintype X]

instance [Nonempty X] : OrderTop (NonemptyFiniteChains X) where
  top := ⟨.univ, ⟨Classical.arbitrary _, by simp⟩, le_total⟩
  le_top _ := by simp

@[simp]
lemma coe_top [Nonempty X] : (⊤ : NonemptyFiniteChains X).1 = ⊤ := rfl

variable (x₀ : X) [Nontrivial X]

@[simps]
def complSingleton : NonemptyFiniteChains X :=
  ⟨{x₀}ᶜ, ⟨(exists_ne x₀).choose, by simpa using (exists_ne x₀).choose_spec⟩,
    le_total⟩

def horn : (nerve (NonemptyFiniteChains X)).Subcomplex where
  obj n := setOf (fun s ↦ ∀ (i : ToType n.unop), s.obj i ≠ ⊤ ∧ s.obj i ≠ complSingleton x₀)
  map _ _ hs _ := hs _

lemma mem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    s ∈ (horn x₀).obj _ ↔
      ∀ (i : Fin (n + 1)), s.obj i ≠ ⊤ ∧ s.obj i ≠ complSingleton x₀ := by
  rfl

lemma not_mem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    s ∉ (horn x₀).obj _ ↔
      ∃ (i : Fin (n + 1)), s.obj i = ⊤ ∨ s.obj i = complSingleton x₀ := by
  simp only [mem_horn_iff, not_forall,
    Classical.not_and_iff_or_not_not, not_not]

end NonemptyFiniteChains

end PartialOrder
