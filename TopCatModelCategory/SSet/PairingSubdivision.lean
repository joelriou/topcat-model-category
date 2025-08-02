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

@[simps coe_coe_fst]
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

lemma cast_obj (i : Fin (d + 2)) :
      (cast s hd).1.1.2.1.obj i =
        s.1.1.2.1.obj ⟨i.1, lt_of_lt_of_le i.2 (by dsimp; omega)⟩ := by
  obtain ⟨⟨⟨n, _⟩, _⟩, _⟩ := s
  obtain rfl : n = _ := hd
  rfl

noncomputable def index : Fin (d + 2) :=
  ⟨s.2.choose.1, lt_of_lt_of_le s.2.choose.2 (by omega)⟩

lemma isIndex :
    IsIndexI s.1 ⟨(index s hd).1, lt_of_lt_of_le (index s hd).2 (by omega)⟩ :=
  s.2.choose_spec

namespace toII

noncomputable def simplex : (nerve (NonemptyFiniteChains X)) _⦋d⦌ :=
  (nerve (NonemptyFiniteChains X)).δ (index s hd) ((cast s hd).1.1.2.1)

lemma simplex_mem_nonDegenerate : simplex s hd ∈ SSet.nonDegenerate _ _ :=
  PartialOrder.mem_nonDegenerate_δ _ _ (cast s hd).1.1.2.2

lemma eq_top_of_index_eq_last (h : index s hd = Fin.last _) :
    (cast s hd).1.1.2.1.obj (Fin.last _) = ⊤ := by
  have h₁ := (cast s hd).1.2
  rw [not_mem_horn_iff'] at h₁
  obtain h₁ | h₁ := h₁
  · exact h₁
  · exfalso
    rw [cast_obj] at h₁
    have h₂ := isIndex s hd
    rw [h] at h₂
    dsimp [IsIndexI] at h₁ h₂
    rw [h₁] at h₂
    have := h₂.symm.le (show x₀ ∈ _ by aesop)
    simp at this

lemma eq_complSingleton_of_index_eq_last (h : index s hd = Fin.last _) :
    (cast s hd).1.1.2.1.obj (Fin.last d).castSucc = complSingleton x₀ := by
  rw [cast_obj]
  have h₁ := isIndex s hd
  simp only [IsIndexI, nerve_obj, SimplexCategory.len_mk, h, Fin.val_last] at h₁
  dsimp
  have h₂ := eq_top_of_index_eq_last s hd h
  rw [cast_obj] at h₂
  dsimp at h₂
  simp only [eq_complSingleton_iff, ← h₁, h₂, coe_top, Finset.top_eq_univ,
    and_true]
  rw [← h₂]
  exact (mem_nonDegenerate_iff _ ).1 s.1.1.2.2 (by simp)

lemma simplex_not_mem_horn : simplex s hd ∉ (horn x₀).obj _ := by
  have h := (cast s hd).1.2
  rw [not_mem_horn_iff''] at h ⊢
  dsimp [simplex, nerve_δ_obj]
  obtain ⟨i, hi⟩ | h := (index s hd).eq_castSucc_or_eq_last
  · rwa [hi, Fin.succAbove_of_lt_succ _ _ (i.castSucc_lt_last), Fin.succ_last]
  · simp only [h, Fin.succAbove_last]
    rwa [eq_complSingleton_of_index_eq_last]

end toII

open toII in
noncomputable def toII : II (x₀ := x₀) :=
  ⟨⟨⟨d, simplex s hd, simplex_mem_nonDegenerate s hd⟩,
    simplex_not_mem_horn s hd⟩, by
      simp only [II, I, nerve_obj, SimplexCategory.len_mk, Set.mem_compl_iff,
        Set.mem_setOf_eq, not_exists]
      rintro ⟨(_ | i), hi⟩ h <;>
        simp only [IsIndexI, nerve_obj, SimplexCategory.len_mk, simplex, cast_coe_coe_fst,
          nerve_δ_obj] at h
      · by_cases h' : index s hd = 0
        · rw [h', Fin.succAbove_of_le_castSucc _ _ (by simp),
            Fin.succ_zero_eq_one] at h
          have := (mem_nonDegenerate_iff _ ).1 (cast s hd).1.1.2.2
            Fin.zero_lt_one
          rw [← Subtype.coe_lt_coe, h] at this
          simp only [nerve_obj, SimplexCategory.len_mk, cast_coe_coe_fst, Finset.lt_eq_subset,
            Finset.ssubset_singleton_iff] at this
          obtain ⟨x, hx⟩ := ((cast s hd).1.1.2.1.obj 0).2.1
          simp [this] at hx
        · rw [Fin.succAbove_of_castSucc_lt, Fin.castSucc_zero] at h
          sorry
          sorry
      · sorry⟩

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
