import TopCatModelCategory.SSet.Pairing
import TopCatModelCategory.SSet.Subdivision

universe u

open CategoryTheory Simplicial

lemma Finset.false_of_lt_of_lt_union_singleton
    {X : Type u} [DecidableEq X] {s t : Finset X} {x₀ : X}
    (h₁ : s < t) (h₂ : t < s ∪ {x₀}) : False := by
  replace h₁ := Finset.card_lt_card h₁
  replace h₂ := lt_of_lt_of_le (Finset.card_lt_card h₂)
    (Finset.card_union_le s {x₀})
  rw [card_singleton] at h₂
  omega

namespace Fin

@[simp]
lemma finsetCard_univ_filter_lt {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (fun j ↦ j < i)).card = i.1 :=
  Finset.card_eq_of_bijective
    (fun a _ ↦ ⟨a, by omega⟩)
    (fun a ha ↦ ⟨a, by simpa using ha, rfl⟩)
    (fun _ _ ↦ by simpa)
    (fun _ _ _ _ h ↦ by rwa [Fin.ext_iff] at h)

@[simp]
lemma finsetCard_univ_filter_le {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (fun j ↦ j ≤ i)).card = i.1 + 1 := by
  obtain _ | n := n
  · fin_cases i
  · obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp [Fin.le_castSucc_iff]
    · simp [Fin.le_last]

@[simp]
lemma finsetCard_univ_filter_castSucc_lt {n : ℕ} (i : Fin (n + 1)) :
    (Finset.univ.filter (fun j ↦ Fin.castSucc j < i)).card = i.1 :=
  Finset.card_eq_of_bijective
    (fun a _ ↦ ⟨a, by omega⟩)
    (fun a ha ↦ ⟨a, by simpa using ha, rfl⟩)
    (fun _ _ ↦ by simpa)
    (fun _ _ _ _ h ↦ by rwa [Fin.ext_iff] at h)

end Fin

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

@[simp]
lemma isIndexI_zero (s : (horn x₀).N) :
    IsIndexI s 0 ↔ (s.1.2.1.obj 0).1 = {x₀} := Iff.rfl

@[simp]
lemma isIndexI_succ (s : (horn x₀).N) (i : Fin s.1.1):
    IsIndexI s i.succ ↔
      (s.1.2.1.obj i.succ).1 = (s.1.2.1.obj i.castSucc).1 ∪ {x₀} := Iff.rfl

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

lemma isUniquelyCodimOneFace_cast_iff {n : ℕ}
    (x : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    SSet.IsUniquelyCodimOneFace x (cast s hd).1.1.2.1 ↔
      SSet.IsUniquelyCodimOneFace x s.1.1.2.1 := by
  obtain ⟨⟨⟨n, _⟩, _⟩, _⟩ := s
  obtain rfl : n = _ := hd
  rfl

lemma isFace_cast_iff {n : ℕ}
    (x : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    SSet.IsFace x (cast s hd).1.1.2.1 ↔
    SSet.IsFace x s.1.1.2.1 := by
  obtain ⟨⟨⟨n, _⟩, _⟩, _⟩ := s
  obtain rfl : n = _ := hd
  rfl

noncomputable def index : Fin (d + 2) :=
  ⟨s.2.choose.1, lt_of_lt_of_le s.2.choose.2 (by omega)⟩

lemma isIndex :
    IsIndexI s.1 ⟨(index s hd).1, lt_of_lt_of_le (index s hd).2 (by omega)⟩ :=
  s.2.choose_spec

lemma isIndex' :
    IsIndexI (cast s hd).1 (index s hd) := by
  obtain ⟨⟨⟨n, _⟩, _⟩, _⟩ := s
  obtain rfl : n = _ := hd
  exact isIndex _ rfl

variable {s hd} in
lemma not_mem_cast_obj_iff_of_isIndex {l : Fin (d + 2)}
    (hl' : IsIndexI (cast s hd).1 l) (i : Fin (d + 2)) :
    x₀ ∉ ((cast s hd).1.1.2.1.obj i).1 ↔ i < l := by
  obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ
  · rw [isIndexI_zero] at hl'
    simp only [nerve_obj, SimplexCategory.len_mk, cast_coe_coe_fst, Fin.not_lt_zero, iff_false,
      Decidable.not_not]
    exact (cast s hd).1.1.2.1.monotone i.zero_le (by simp [hl'])
  · rw [isIndexI_succ] at hl'
    have : x₀ ∉ ((cast s hd).1.1.2.1.obj l.castSucc).1 := fun h ↦ by
      apply ((mem_nonDegenerate_iff _).1 (cast s hd).1.1.2.2 l.castSucc_lt_succ).ne
      rw [Subtype.ext_iff]
      simpa [hl']
    rw [← not_iff_not, Decidable.not_not, ← Fin.le_castSucc_iff]
    constructor
    · intro h hi
      exact this ((cast s hd).1.1.2.1.monotone hi h)
    · intro hi
      rw [not_le, Fin.castSucc_lt_iff_succ_le] at hi
      exact (cast s hd).1.1.2.1.monotone hi (by simp [hl'])

lemma not_mem_cast_obj_iff (i : Fin (d + 2)) :
    x₀ ∉ ((cast s hd).1.1.2.1.obj i).1 ↔ i < index s hd :=
  not_mem_cast_obj_iff_of_isIndex (isIndex' s hd) i

variable {s hd} in
lemma index_eq_of_isIndex {i : Fin (d + 2)}
    (h : IsIndexI (cast s hd).1 i) :
    index s hd = i := by
  have := not_mem_cast_obj_iff_of_isIndex h
  simp only [not_mem_cast_obj_iff] at this
  obtain h | rfl | h := lt_trichotomy (index s hd) i
  · replace this := (this _).2 h
    simp at this
  · rfl
  · replace this := (this _).1 h
    simp at this

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

lemma not_mem_simplex_obj_iff (i : Fin (d + 1)) :
    x₀ ∉ ((simplex s hd).1.obj i).1 ↔ i.castSucc < index s hd := by
  generalize hl : index s hd = l
  simp [simplex, hl, nerve_δ_obj, not_mem_cast_obj_iff,
    Fin.succAbove_lt_iff_castSucc_lt]

end toII

open toII in
noncomputable def toII : II (x₀ := x₀) :=
  ⟨⟨⟨d, simplex s hd, simplex_mem_nonDegenerate s hd⟩,
    simplex_not_mem_horn s hd⟩, by
      simp only [II, I, nerve_obj, SimplexCategory.len_mk, Set.mem_compl_iff,
        Set.mem_setOf_eq, not_exists]
      generalize hl : index s hd = l
      intro i h
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · simp only [simplex, nerve_obj, SimplexCategory.len_mk,
          cast_coe_coe_fst, isIndexI_zero, hl, nerve_δ_obj] at h
        obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ
        · rw [Fin.succAbove_of_le_castSucc _ _ (by simp),
            Fin.succ_zero_eq_one] at h
          have := (mem_nonDegenerate_iff _ ).1 (cast s hd).1.1.2.2
            Fin.zero_lt_one
          rw [← Subtype.coe_lt_coe, h] at this
          simp only [nerve_obj, SimplexCategory.len_mk, cast_coe_coe_fst,
            Finset.lt_eq_subset, Finset.ssubset_singleton_iff] at this
          obtain ⟨x, hx⟩ := ((cast s hd).1.1.2.1.obj 0).2.1
          simp [this] at hx
        · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp),
            Fin.castSucc_zero] at h
          have : 0 < index s hd := by simp [hl]
          rw [← not_mem_cast_obj_iff] at this
          exact this (by simp [h])
      · simp only [simplex, nerve_obj, SimplexCategory.len_mk,
          cast_coe_coe_fst, isIndexI_succ, hl, nerve_δ_obj] at h
        apply l.succAbove_ne i.succ
        by_cases hl' : l ≤ i.succ.castSucc
        · rw [Fin.succAbove_of_le_castSucc _ _ hl'] at h
          rw [← Fin.succ_castSucc] at hl'
          obtain hl' | rfl := hl'.lt_or_eq
          · rw [Fin.succAbove_of_lt_succ _ _ hl', Fin.succ_castSucc,
              ← isIndexI_succ] at h
            rwa [Fin.succAbove_of_le_castSucc _ _ hl'.le,
              ← index_eq_of_isIndex h]
          · exfalso
            simp only [Fin.succAbove_succ_self] at h
            have := (mem_nonDegenerate_iff _).1 (cast s hd).1.1.2.2
            exact Finset.false_of_lt_of_lt_union_singleton (x₀ := x₀)
              (this i.castSucc.castSucc_lt_succ) (by
                have := this i.succ.castSucc_lt_succ
                rw [← Subtype.coe_lt_coe] at this
                exact lt_of_lt_of_le this h.le)
        · simp only [not_le] at hl'
          rw [Fin.succAbove_of_castSucc_lt _ _ hl',
            Fin.succAbove_of_castSucc_lt _ _ (lt_trans (by simp) hl'),
            ← Fin.succ_castSucc, ← isIndexI_succ] at h
          rwa [Fin.succAbove_of_castSucc_lt _ _ hl', ← Fin.succ_castSucc,
            ← index_eq_of_isIndex h]⟩

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
def finset {n : ℕ} (s : nerve (NonemptyFiniteChains X) _⦋n⦌) :
    Finset (Fin (n + 1)) :=
  { i : _ | x₀ ∉ (s.obj i).1 }

omit [Fintype X] [Nontrivial X] in
lemma mem_finset_iff {n : ℕ} (s : nerve (NonemptyFiniteChains X) _⦋n⦌)
    (i : Fin (n + 1)) :
    i ∈ finset x₀ s ↔ x₀ ∉ (s.obj i).1 := by
  simp [finset]

lemma toII.index_eq_card
    (s : I (x₀ := x₀)) {d : ℕ} (hd : s.1.1.1 = d + 1) :
      (index s hd).1 = (finset x₀ (toII.simplex s hd)).card := by
  have : finset x₀ (toII.simplex s hd) =
      Finset.univ.filter (fun i ↦ i.castSucc < index s hd) := by
    ext i
    simp [mem_finset_iff, not_mem_simplex_obj_iff]
  simp [this]

lemma injective_q : Function.Injective (q (x₀ := x₀)) := by
  intro s s' h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one_of_ne_zero (dim_ne_zero s)
  obtain ⟨d', hd'⟩ := Nat.exists_eq_add_one_of_ne_zero (dim_ne_zero s')
  rw [q_eq s hd, q_eq s' hd', Subtype.ext_iff, Subtype.ext_iff] at h
  obtain rfl : d = d' := congr_arg Sigma.fst h
  rw [Sigma.ext_iff] at h
  simp only [nerve_obj, SimplexCategory.len_mk, toII, heq_eq_eq, Subtype.mk.injEq, true_and] at h
  have : index s hd = index s' hd' := by
    rw [Fin.ext_iff, toII.index_eq_card, toII.index_eq_card, h]
  generalize hl : index s hd = l
  rw [← cast_eq_self s hd, ← cast_eq_self s' hd',
    Subtype.ext_iff, Subtype.ext_iff, Sigma.ext_iff]
  simp only [nerve_obj, SimplexCategory.len_mk, cast_coe_coe_fst,
    heq_eq_eq, true_and, Subtype.ext_iff]
  refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ rfl)
  simp only [toII.simplex, hl, nerve_obj, ← this] at h
  replace h := Functor.congr_obj h
  simp only [SimplexCategory.len_mk, nerve_δ_obj] at h
  by_cases hi : l = i
  · subst hi
    rw [Subtype.ext_iff]
    have h₁ := isIndex' s hd
    have h₂ := isIndex' s' hd'
    simp only [hl, ← this] at h₁ h₂
    obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ
    · rw [isIndexI_zero] at h₁ h₂
      rw [h₁, h₂]
    · rw [isIndexI_succ] at h₁ h₂
      have := h l
      simp only [Fin.succAbove_succ_self] at this
      rw [h₁, h₂, this]
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
    apply h

lemma surjective_q : Function.Surjective (q (x₀ := x₀)) := by
  sorry

variable (x₀) in
lemma bijective_q : Function.Bijective (q (x₀ := x₀)) :=
  ⟨injective_q, surjective_q⟩

noncomputable def p : II (x₀ := x₀) ≃ I (x₀ := x₀) :=
  (Equiv.ofBijective _ (bijective_q x₀)).symm

@[simp]
lemma p_symm (s : I (x₀ := x₀)) :
    p.symm s = q s := rfl

@[simp]
lemma q_p (s : II (x₀ := x₀)) : q (p s) = s :=
  p.symm_apply_apply s

@[simp]
lemma p_q (s : I (x₀ := x₀)) : p (q s) = s :=
  p.apply_symm_apply s

lemma isUniquelyCodimOneFace (s : I (x₀ := x₀)) :
    SSet.IsUniquelyCodimOneFace (q s).1.1.2.1 s.1.1.2.1 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one_of_ne_zero (dim_ne_zero s)
  rw [← isUniquelyCodimOneFace_cast_iff _ hd, q_eq s hd]
  exact .mk (existsUnique_of_exists_of_unique ⟨_, rfl⟩ (fun i j hi hj ↦
    δ_injective_of_mem_nonDegenerate _
    ((cast s hd).1.1.2.2) (hi.trans hj.symm)))

def φ (s : II (x₀ := x₀)) : ℕ :=
  (finset x₀ s.1.1.2.1).card

end pairing

open pairing

@[simps]
noncomputable def pairing : (horn x₀).Pairing where
  I := I
  II := II
  inter := by simp [II]
  union := by simp [II]
  p := p

instance : (pairing x₀).IsProper where
  isUniquelyCodimOneFace y := by
    obtain ⟨s, rfl⟩ := (pairing x₀).p.symm.surjective y
    dsimp
    rw [p_q]
    exact isUniquelyCodimOneFace s

instance : (pairing x₀).IsRegular := by
  rw [SSet.Subcomplex.Pairing.isRegular_iff]
  refine ⟨φ, fun x y h₁ ⟨h₂, h₃⟩ ↦ ?_⟩
  dsimp [SSet.Subcomplex.Pairing.AncestralRel] at h₃
  obtain ⟨s, hs⟩ := (pairing x₀).p.symm.surjective y
  dsimp at hs
  rw [← hs, p_q s] at h₃
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one_of_ne_zero (dim_ne_zero s)
  rw [q_eq _ hd] at hs
  rw [← isFace_cast_iff _ hd] at h₃
  obtain ⟨⟨⟨dx, x, hx₁⟩, hx₂⟩, hx₃⟩ := x
  obtain ⟨⟨⟨dy, y, _⟩, _⟩, _⟩ := y
  obtain rfl : d = dy := by
    rw [Subtype.ext_iff, Subtype.ext_iff] at hs
    exact congr_arg Sigma.fst hs
  obtain rfl : d = dx := h₁.symm
  obtain rfl : toII.simplex s hd = y := by
    rw [Subtype.ext_iff, Subtype.ext_iff, Sigma.ext_iff] at hs
    simpa [toII] using hs
  dsimp at hx₁ hx₂ hx₃ h₂ h₃
  obtain ⟨ι, _, _, eq⟩ := h₃
  obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono ι
  obtain rfl : (nerve _).δ i _ = x := eq
  let σ := (cast s hd).1.1.2.1
  replace h₂ : (nerve _).δ i σ ≠ (nerve _).δ (index s hd) σ := fun h ↦ h₂ (by
    rw [Subtype.ext_iff, Subtype.ext_iff, Sigma.ext_iff]
    simpa)
  generalize hl : index s hd = l
  obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ
  · have hi : i = 0 := by
      by_contra!
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero this
      have := isIndex s hd
      rw [hl] at this
      change (s.1.1.2.1.obj 0).1 = {x₀} at this
      simp only [II, Set.mem_compl_iff] at hx₃
      apply hx₃
      simp only [I, nerve_obj, SimplexCategory.len_mk, Set.mem_setOf_eq]
      refine ⟨0, ?_⟩
      rw [isIndexI_zero]
      dsimp [nerve_δ_obj]
      rwa [cast_obj, Fin.succAbove_of_castSucc_lt _ _ (by simp)]
    simp [hi, hl] at h₂
  · have := isIndex' s hd
    rw [hl, isIndexI_succ] at this
    simp only [II, Set.mem_compl_iff] at hx₃
    have hi₁ : l.castSucc ≤ i := by
      rw [← Fin.not_lt]
      intro hi₁
      obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by
        rintro rfl
        simp at hi₁)
      refine hx₃ ⟨l.succ, ?_⟩
      rw [isIndexI_succ]
      dsimp [nerve_δ_obj]
      rw [Fin.succAbove_of_le_castSucc _ _ hi₁.le,
        Fin.succAbove_of_le_castSucc, this, Fin.succ_castSucc]
      rwa [Fin.le_castSucc_iff, Fin.succ_castSucc]
    have hi₂ : i ≤ l.succ := by
      rw [← Fin.not_lt]
      intro hi₁
      obtain ⟨l, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := l)
        (fun h ↦ not_le.2 hi₁ (by simpa [h] using i.le_last))
      refine hx₃ ⟨l.succ, ?_⟩
      simp only [isIndexI_succ, nerve_obj, SimplexCategory.len_mk, nerve_δ_obj]
      rwa [Fin.succAbove_of_castSucc_lt _ _ hi₁,
        Fin.succAbove_of_castSucc_lt _ _ (lt_trans (by simp) hi₁)]
    obtain hi₂ | rfl := hi₂.lt_or_eq
    · obtain rfl : l.castSucc = i := by
        apply le_antisymm
        · exact hi₁
        · rwa [Fin.le_castSucc_iff]
      dsimp [toII.simplex]
      simp only [hl]
      let A := finset x₀ ((nerve _).δ l.castSucc σ)
      let B := finset x₀ ((nerve _).δ l.succ σ)
      change A.card < B.card
      have hA : A = Finset.univ.filter (fun i ↦ i < l) := by
        ext i
        simp only [mem_finset_iff, SimplexCategory.len_mk, nerve_δ_obj, Finset.mem_filter,
          Finset.mem_univ, true_and, A]
        rw [not_mem_cast_obj_iff, hl]
        constructor
        · intro h
          by_contra!
          rw [Fin.succAbove_of_le_castSucc _ _ (by simpa),
            Fin.succ_lt_succ_iff] at h
          exact h.not_le this
        · intro h
          rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa)]
          exact (Fin.castSucc_lt_castSucc_iff.2 h).trans (by simp)
      have hB : B = Finset.univ.filter (fun i ↦ i ≤ l) := by
        ext i
        simp only [mem_finset_iff, SimplexCategory.len_mk, nerve_δ_obj, Finset.mem_filter,
          Finset.mem_univ, true_and, B, A]
        rw [not_mem_cast_obj_iff, hl]
        constructor
        · intro h
          by_contra!
          rw [Fin.succAbove_of_le_castSucc _ _ (by simpa),
            Fin.succ_lt_succ_iff] at h
          omega
        · intro h
          simpa [Fin.succAbove_of_castSucc_lt l.succ i (by simpa)]
      simp [hA, hB]
    · exact (h₂ (by rw [hl])).elim

end horn

end NonemptyFiniteChains

end PartialOrder
