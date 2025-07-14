import Mathlib.AlgebraicTopology.SimplicialObject.Basic

open CategoryTheory Simplicial Opposite

lemma Fin.castSucc_ne_last {n : ℕ} (x : Fin n) : x.castSucc ≠ Fin.last _ :=
  x.castSucc_lt_last.ne

namespace SimplexCategory

namespace II

variable {n m : ℕ}

def finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i ↦ i = Fin.last _ ∨
    ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc)

lemma mem_finset_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2)) :
    i ∈ finset f x ↔ i = Fin.last _ ∨
      ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc := by
  simp [finset]

@[simp]
lemma last_mem_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    Fin.last _ ∈ finset f x := by
  simp [mem_finset_iff]

@[simp]
lemma castSucc_mem_finset_iff
    (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 1)) :
    i.castSucc ∈ finset f x ↔ x ≤ (f i).castSucc := by
  have := i.castSucc_ne_last
  simp only [mem_finset_iff, Fin.castPred_castSucc]
  tauto

lemma nonempty_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (finset f x).Nonempty :=
  ⟨Fin.last _, by simp [mem_finset_iff]⟩

def map' (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Fin (n + 2) :=
  (finset f x).min' (nonempty_finset f x)

lemma map'_eq_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 2)) :
    map' f x = y ↔ y ∈ finset f x ∧ ∀ (z : Fin (n + 2)), z ∈ finset f x → y ≤ z := by
  dsimp [map']
  constructor
  · rintro rfl
    exact ⟨Finset.min'_mem _ _, Finset.min'_le _⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (Finset.min'_le _ _ h₁) (by rwa [Finset.le_min'_iff])

lemma map'_eq_last_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    map' f x = Fin.last _ ↔ ∀ (i : Fin (n + 1)), (f i).castSucc < x := by
  simp only [map'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_lt (h i)

lemma map'_eq_castSucc_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)) :
    map' f x = y.castSucc ↔ x ≤ (f y).castSucc ∧
      ∀ (i : Fin (n + 1)) (_ : i < y), (f i).castSucc < x := by
  simp only [map'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_le (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_le (by simpa using hi)
    · apply Fin.le_last

@[simp]
lemma map'_last (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f (Fin.last _) = Fin.last _ := by
  rw [map'_eq_last_iff]
  intro i
  apply Fin.castSucc_lt_last

@[simp]
lemma map'_id (x : Fin (n + 2)) : map' OrderHom.id x = x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    aesop
  · simp

lemma map'_map' {p : ℕ} (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (m + 1) →o Fin (p + 1)) (x : Fin (p + 2)) :
    map' f (map' g x) = map' (g.comp f) x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · symm
        rw [hz]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · symm
        rw [hz]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · symm
      rw [hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simps]
def map (f : Fin (n + 1) →o Fin (m + 1)) : Fin (m + 2) →o Fin (n + 2) where
  toFun := map' f
  monotone' x y hxy :=
    Finset.min'_subset _ (fun z hz ↦ by
      obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
      · simp only [castSucc_mem_finset_iff] at hz ⊢
        exact hxy.trans hz
      · simp)

end II

def II : SimplexCategory ⥤ SimplexCategoryᵒᵖ where
  obj n := op ⦋n.len + 1⦌
  map f := op (Hom.mk (II.map f.toOrderHom))
  map_id n := Quiver.Hom.unop_inj (by
    induction' n using SimplexCategory.rec with n
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    induction' m using SimplexCategory.rec with m
    induction' n using SimplexCategory.rec with n
    induction' p using SimplexCategory.rec with p
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

end SimplexCategory
