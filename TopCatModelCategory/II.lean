/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# A construction by Gabriel and Zisman

In this file, we construct a cosimplicial object `SimplexCategory.II`
in `SimplexCategoryᵒᵖ`, i.e. a functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ`.
If we identify `SimplexCategory` with the category of finite nonempty
linearly ordered types, this functor could be interpreted as the
contravariant functor which sends a finite nonempty linearly ordered type `T`
to `T →o Fin 2`; in particular, it sends `Fin (n + 1)` to a linearly
ordered type which is isomorphic to `Fin (n + 2)`. As a result, we define
`SimplexCategory.II` as a functor which sends `⦋n⦌` to `⦋n + 1⦌`: on morphisms,
it sends faces to degeneracies and vice versa.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

namespace II

variable {n m : ℕ}

/-- Auxiliary definition for `map'`. Given `f : Fin (n + 1) →o Fin (m + 1)` and
`x : Fin (m + 2)`, `map' f x` shall be the smallest element in
this `finset f x : Finset (Fin (n + 2))`. -/
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

/-- Auxiliary definition for the definition of the action of the
functor `SimplexCategory.II` on morphisms. -/
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

lemma map'_le_castSucc_iff (f : Fin (n + 1) →o Fin (m + 1))
    (x : Fin (m + 2)) (i : Fin (n + 1)) :
    map' f x ≤ i.castSucc ↔ x ≤ (f i).castSucc := by
  refine ⟨fun h ↦ ?_, fun h ↦ Finset.min'_le _ _ (by simpa)⟩
  have : map' f x ∈ _ := Finset.min'_mem _ (nonempty_finset f x)
  simp only [mem_finset_iff] at this
  obtain h' | ⟨_, h'⟩ := this
  · simp only [h', Fin.last_le_iff] at h
    exact (Fin.castSucc_ne_last _ h).elim
  · refine h'.trans (Fin.castSucc_le_castSucc_iff.2 (f.2 (by simpa)))

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
    exact hi.not_gt (h i)

lemma map'_eq_castSucc_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)) :
    map' f x = y.castSucc ↔ x ≤ (f y).castSucc ∧
      ∀ (i : Fin (n + 1)) (_ : i < y), (f i).castSucc < x := by
  simp only [map'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]
lemma map'_last (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f (Fin.last _) = Fin.last _ := by
  rw [map'_eq_last_iff]
  intro i
  apply Fin.castSucc_lt_last

@[simp]
lemma map'_zero (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f 0 = 0 := by
  change _ = Fin.castSucc 0
  simp only [map'_eq_castSucc_iff, Fin.zero_le, Fin.not_lt_zero,
    imp_self, implies_true, and_self]

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

@[simp]
lemma map'_succAboveOrderEmb {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 3)):
    map' i.succAboveOrderEmb.toOrderHom x = i.predAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases hx : x ≤ i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        rw [map'_eq_last_iff]
        intro j
        simp [j.castSucc_lt_last]
    · simp only [not_le] at hx
      obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · simp only [not_lt] at h
        rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]
lemma map'_predAbove {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 2)) :
    map' { toFun := i.predAbove, monotone' := Fin.predAbove_right_monotone i } x =
      i.succ.castSucc.succAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases hi : i.succ ≤ x.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.succ_le_castSucc_iff] at hi
        rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · simp only [not_lt] at h
          rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · simp only [Fin.succ_le_castSucc_iff, not_lt] at hi
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · simp only [not_lt] at h
          rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · rw [map'_last, Fin.succAbove_of_lt_succ, Fin.succ_last]
    apply Fin.castSucc_lt_last

lemma monotone_map' (f : Fin (n + 1) →o Fin (m + 1)) :
    Monotone (map' f) := by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz ↦ by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

lemma strictMono_map' (f : Fin (n + 1) →o Fin (m + 1)) (hf : Function.Surjective f) :
    StrictMono (map' f) := by
  intro x y hxy
  obtain h | h := (monotone_map' f hxy.le).lt_or_eq
  · exact h
  · exfalso
    generalize hj : map' f y = j
    rw [hj] at h
    obtain ⟨x, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hxy)
    obtain ⟨i, rfl⟩ := hf x
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · rw [map'_eq_castSucc_iff] at h hj
      by_cases hij : i < j
      · exact (lt_self_iff_false _).1 (h.2 _ hij)
      · simp only [not_lt] at hij
        exact (lt_self_iff_false y).1 (lt_of_le_of_lt
          (hj.1.trans (Fin.castSucc_le_castSucc_iff.2 (f.2 hij))) hxy)
    · rw [map'_eq_last_iff] at h
      exact (lt_self_iff_false _).1 (h i)

def injective_map' {f g : Fin (n + 1) →o Fin (m + 1)}
     (h : map' f = map' g) : f = g := by
  ext i : 2
  wlog h' : g i ≤ f i generalizing f g
  · rw [this h.symm (not_le.1 h').le]
  refine le_antisymm ?_ h'
  rw [← Fin.castSucc_le_castSucc_iff, ← map'_le_castSucc_iff, ← h, map'_le_castSucc_iff]

end II

/-- The functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ` (i.e. a cosimplicial
object in `SimplexCategoryᵒᵖ`) which sends `⦋n⦌` to the object in `SimplexCategoryᵒᵖ`
that is associated to the linearly ordered type `⦋n + 1⦌` (identified as the ordered
type `⦋n⦌ →o ⦋1⦌`). -/
@[simps obj]
def II : CosimplicialObject SimplexCategoryᵒᵖ where
  obj n := op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]
lemma II'_δ {n : ℕ} (i : Fin (n + 2)) :
    II.δ i = (σ i).op :=
  Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]
lemma II'_σ {n : ℕ} (i : Fin (n + 1)) :
    II.σ i = (δ i.succ.castSucc).op :=
  Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

lemma II.castSucc_lt_map_apply {n m : SimplexCategory} (f : n ⟶ m)
    (i : Fin (m.len + 2)) (j : Fin (n.len + 1)) :
    j.castSucc < (II.map f).unop i ↔ (f j).castSucc < i := by
  generalize h : (II.map f).unop i = k
  change II.map' _ _ = _ at h
  obtain ⟨k, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
  · simp only [II_obj, len_mk, map'_eq_castSucc_iff] at h
    constructor
    · intro hj
      exact h.2 _ (by simpa using hj)
    · intro hj
      by_contra!
      simp only [Fin.castSucc_le_castSucc_iff] at this
      refine hj.not_ge (h.1.trans ?_)
      simpa only [Fin.castSucc_le_castSucc_iff] using f.toOrderHom.monotone this
  · refine ⟨fun _ ↦ ?_, fun _ ↦ j.castSucc_lt_last⟩
    simp only [II_obj, len_mk, map'_eq_last_iff] at h
    apply h

lemma II.strictMono_map_unop {n m : SimplexCategory} (f : n ⟶ m) [Epi f] :
    StrictMono (II.map f).unop :=
  fun _ _ h ↦ strictMono_map' _ (by rwa [← SimplexCategory.epi_iff_surjective]) h

instance II.faithful : SimplexCategory.II.Faithful where
  map_injective h := by
    ext : 1
    apply II.injective_map'
    ext i : 1
    exact DFunLike.congr_fun (congr_arg Hom.toOrderHom (congr_arg Quiver.Hom.unop h)) i

end SimplexCategory
