import TopCatModelCategory.SSet.Pairing
import TopCatModelCategory.SSet.Subdivision

universe u

open CategoryTheory Simplicial

namespace PartialOrder

namespace NonemptyFiniteChains

variable {X : Type u} [LinearOrder X] [Fintype X] [Nontrivial X] (x₀ : X)

namespace horn

namespace pairing

variable {x₀}

def IsIndexI (s : (horn x₀).N) (i : Fin (s.1.1 + 1)) : Prop :=
  match i with
  | ⟨0, _⟩ => (s.1.2.1.obj 0).1 = {x₀}
  | ⟨k + 1, hk⟩ => (s.1.2.1.obj ⟨k + 1, hk⟩).1 =
      (s.1.2.1.obj ⟨k, (lt_add_one k).trans hk⟩).1 ∪ {x₀}

def I : Set (horn x₀).N := setOf (fun s ↦ ∃ (i : Fin (s.1.1 + 1)), IsIndexI s i)

def II : Set (horn x₀).N := Iᶜ

lemma dim_ne_zero (s : I (x₀ := x₀)) : s.1.1.1 ≠ 0 := by
  obtain ⟨⟨⟨n, s, hs⟩, hs'⟩, ⟨j, hj⟩⟩ := s
  rintro rfl
  simp only [not_mem_horn_iff] at hs'
  obtain ⟨i, hi⟩ := hs'
  fin_cases i
  fin_cases j
  dsimp [IsIndexI] at hj hi
  obtain hi | hi := hi
  · obtain ⟨y, hy⟩ := exists_ne x₀
    have := Finset.mem_univ y
    simp only [hi, coe_top, Finset.top_eq_univ] at hj
    exact hy (by simpa [hj] using this)
  · simp [hi] at hj

section

variable (s : I (x₀ := x₀)) {d : ℕ} (hd : s.1.1.1 = d + 1)

def cast : I (x₀ := x₀) :=
  ⟨⟨⟨d + 1, ⟨by rw [← hd]; exact s.1.1.2.1, by
    obtain ⟨⟨⟨n, h⟩, _⟩, _⟩ := s
    obtain rfl : n = _ := hd
    exact h.2⟩⟩, by
    obtain ⟨⟨⟨n, _⟩, h⟩, _⟩ := s
    obtain rfl : n = _ := hd
    exact h⟩, by
    obtain ⟨⟨⟨n, _⟩, _⟩, h⟩ := s
    obtain rfl : n = _ := hd
    exact h⟩

lemma cast_eq_self : cast s hd = s := by
  obtain ⟨⟨⟨n, _⟩, _⟩, _⟩ := s
  obtain rfl : n = _ := hd
  rfl

noncomputable def index : Fin (d + 2) :=
  ⟨s.2.choose.1, lt_of_lt_of_le s.2.choose.2 (by omega)⟩

namespace toII

noncomputable def simplex : (nerve (NonemptyFiniteChains X)) _⦋d⦌ :=
  (nerve (NonemptyFiniteChains X)).δ (index s hd) ((cast s hd).1.1.2.1)

lemma simplex_mem_nonDegenerate : simplex s hd ∈ SSet.nonDegenerate _ _ :=
  PartialOrder.mem_nonDegenerate_δ _ _ (cast s hd).1.1.2.2

lemma simplex_not_mem_horn : simplex s hd ∉ (horn x₀).obj _ := by
  sorry

end toII

open toII in
noncomputable def toII : II (x₀ := x₀) :=
  ⟨⟨⟨d, simplex s hd, simplex_mem_nonDegenerate s hd⟩,
    simplex_not_mem_horn s hd⟩, by
      sorry⟩

end

noncomputable def q (s : I (x₀ := x₀)) : II (x₀ := x₀) :=
  toII s (Nat.succ_pred_eq_of_ne_zero (dim_ne_zero s)).symm

lemma q_eq (s : I (x₀ := x₀)) {d : ℕ} (hd : s.1.1.1 = d + 1) :
    q s = toII s hd := by
  dsimp only [q]
  congr
  have := Nat.succ_pred_eq_of_ne_zero (dim_ne_zero s)
  omega

variable (x₀) in
lemma bijective_q : Function.Bijective (q (x₀ := x₀)) := sorry

noncomputable def p : II (x₀ := x₀) ≃ I (x₀ := x₀) :=
  (Equiv.ofBijective _ (bijective_q x₀)).symm

@[simp]
lemma p_symm (s : I (x₀ := x₀)) :
    p.symm s = q s := rfl

end pairing

open pairing in
noncomputable def pairing : (horn x₀).Pairing where
  I := I
  II := II
  inter := by simp [I, II]
  union := by simp [I, II]
  p := p

instance : (pairing x₀).IsProper where
  isUniquelyCodimOneFace := sorry

instance : (pairing x₀).IsRegular where
  wf := sorry

end horn

end NonemptyFiniteChains

end PartialOrder
