import TopCatModelCategory.TopCat.Cosimp
import TopCatModelCategory.TopCat.Monoidal
import Mathlib.Topology.Piecewise

open Simplicial

namespace Real

variable (x₀ x₁ y₀ y₁ : ℝ)

noncomputable def affineMap : ℝ → ℝ :=
  fun t ↦ y₀ + (t - x₀) / (x₁ - x₀) * (y₁ - y₀)

lemma affineMap_exists :
    ∃ (a b : ℝ), ∀ (x : ℝ), affineMap x₀ x₁ y₀ y₁ x = a + x * b := by
  generalize h : (y₁ - y₀) / (x₁ - x₀) = b
  refine ⟨y₀ - x₀ * b, b, fun x ↦ ?_⟩
  simp only [affineMap, mul_comm_div, h]
  ring

lemma affineMap_unique (a b a' b' : ℝ) (x₀ x₁ : ℝ) (hx : x₀ ≠ x₁)
    (hx₀ : a + x₀ * b = a' + x₀ * b')
    (hx₁ : a + x₁ * b = a' + x₁ * b') :
    a = a' ∧ b = b' := by
  have hx₀₁ : x₀ - x₁ ≠ 0 := fun h ↦ hx (by rwa [sub_eq_zero] at h)
  obtain rfl : b = b' := by
    rw [← sub_eq_zero, ← mul_eq_zero_iff_left hx₀₁]
    linarith
  obtain rfl : a = a' := by simpa using hx₀
  simp

lemma affineMap_comp_affineMap_exists (x₀' x₁' y₀' y₁' : ℝ) :
    ∃ (a b : ℝ), ∀ (x : ℝ), affineMap x₀' x₁' y₀' y₁' (affineMap x₀ x₁ y₀ y₁ x) = a + x * b := by
  obtain ⟨a, b, h⟩ := affineMap_exists x₀ x₁ y₀ y₁
  obtain ⟨a', b', h'⟩ := affineMap_exists x₀' x₁' y₀' y₁'
  refine ⟨a * b' + a', b * b', fun x ↦ ?_⟩
  simp only [h, h']
  ring

@[simp]
lemma affineMap_apply₀ : affineMap x₀ x₁ y₀ y₁ x₀ = y₀ := by
  simp [affineMap]

lemma affineMap_apply₁ (h : x₀ ≠ x₁) :
    affineMap x₀ x₁ y₀ y₁ x₁ = y₁ := by
  have h : x₁ - x₀ ≠ 0 := fun h' ↦ by
    rw [sub_eq_zero] at h'
    tauto
  simp [affineMap, div_self h]

variable (hx₀₁ : x₀ < x₁) (hy₀₁ : y₀ < y₁)

include hx₀₁ hy₀₁

lemma le_affineMap (x : ℝ) (hx : x₀ ≤ x) : y₀ ≤ affineMap x₀ x₁ y₀ y₁ x := by
  simp only [affineMap, le_add_iff_nonneg_right]
  refine Left.mul_nonneg (div_nonneg ?_ ?_) ?_
  · simpa only [sub_nonneg]
  · simpa only [sub_nonneg] using hx₀₁.le
  · simpa only [sub_nonneg] using hy₀₁.le

lemma affineMap_le (x : ℝ) (hx : x ≤ x₁) : affineMap x₀ x₁ y₀ y₁ x ≤ y₁ := by
  simp only [affineMap, ← le_sub_iff_add_le']
  refine mul_le_of_le_one_left ?_ (div_le_one_of_le₀ ?_ ?_)
  · simpa only [sub_nonneg] using hy₀₁.le
  · simpa
  · simpa only [sub_nonneg] using hx₀₁.le

lemma strictMono_affineMap : StrictMono (affineMap x₀ x₁ y₀ y₁) := by
  intro a b h
  dsimp only [affineMap]
  rwa [add_lt_add_iff_left, mul_lt_mul_iff_of_pos_right (by simpa),
    div_lt_div_iff_of_pos_right (by simpa), sub_lt_sub_iff_right]

lemma affineMap_lt (x : ℝ) (hx : x < x₁) : affineMap x₀ x₁ y₀ y₁ x < y₁ := by
  conv_rhs => rw [← affineMap_apply₁ x₀ x₁ y₀ y₁ hx₀₁.ne]
  exact strictMono_affineMap _ _ _ _ hx₀₁ hy₀₁ hx

lemma affineMap_surjective_on (y : ℝ) (hy₀ : y₀ ≤ y) (hy₁ : y ≤ y₁) :
    ∃ (x : ℝ),x₀ ≤ x ∧ x ≤ x₁ ∧ affineMap x₀ x₁ y₀ y₁ x = y :=
  ⟨affineMap y₀ y₁ x₀ x₁ y, le_affineMap y₀ y₁ x₀ x₁ hy₀₁ hx₀₁ y hy₀,
    affineMap_le y₀ y₁ x₀ x₁ hy₀₁ hx₀₁ y hy₁, by
      obtain ⟨a, b, h⟩ := affineMap_comp_affineMap_exists y₀ y₁ x₀ x₁ x₀ x₁ y₀ y₁
      have h₀ := h y₀
      have h₁ := h y₁
      rw [affineMap_apply₀, affineMap_apply₀] at h₀
      rw [affineMap_apply₁ _ _ _ _ hy₀₁.ne, affineMap_apply₁ _ _ _ _ hx₀₁.ne] at h₁
      obtain ⟨rfl, rfl⟩ := affineMap_unique 0 1 a b y₀ y₁ hy₀₁.ne (by simpa) (by simpa)
      simp [h]⟩

end Real

namespace TopCat.cosimp

namespace unitInterval

variable {n : ℕ} (f g : cosimp unitInterval ^⦋n⦌) (hf : StrictMono f.1) (hg : StrictMono g.1)

namespace exists_orderIso

variable (x : unitInterval)

noncomputable def finset : Finset (Fin (n + 1)) :=
  {i | f.1 i.castSucc ≤ x}

@[simp]
lemma mem_finset_iff (i : Fin (n + 1)) : i ∈ finset f x ↔ f.1 i.castSucc ≤ x := by simp [finset]

lemma nonempty_finset : (finset f x).Nonempty :=
  ⟨0, by
    have := f.2.1
    dsimp at this
    simp [this]⟩

noncomputable def index : Fin (n + 1) := (finset f x).max' (nonempty_finset f x)

lemma monotone_index : Monotone (index f) := by
  intro x y h
  dsimp only [index]
  rw [Finset.max'_le_iff]
  intro i hi
  apply Finset.le_max'
  simp only [mem_finset_iff] at hi ⊢
  exact hi.trans h

lemma apply_index_castSucc_le : f.1 (index f x).castSucc ≤ x := by
  simpa using (finset f x).max'_mem (nonempty_finset f x)

lemma le_apply_index_succ : x ≤ f.1 (index f x).succ := by
  obtain ⟨j, hj⟩ | h := (index f x).eq_castSucc_or_eq_last
  · by_contra!
    have : _ ≤ index f x :=
      (finset f x).le_max' j.succ (by
        rw [hj] at this
        simpa using this.le)
    simp [hj] at this
  · have := f.2.2
    dsimp at this
    simp [h, this]

lemma le_index_iff (i : Fin (n + 1)) :
    i ≤ index f x ↔ f.1 i.castSucc ≤ x := by
  refine ⟨fun h ↦ ?_, fun _ ↦ (finset f x).le_max' i (by simpa [finset])⟩
  have := (finset f x).max'_mem (nonempty_finset f x)
  simp only [mem_finset_iff] at this
  exact le_trans (f.1.monotone (by simpa)) this

lemma index_le_castSucc_iff (i : Fin n) :
    index f x ≤ i.castSucc ↔ x < f.1 i.succ.castSucc := by
  rw [← not_iff_not, not_lt, not_le, Fin.castSucc_lt_iff_succ_le,
    le_index_iff]

include hf in
lemma index_apply_castSucc (i : Fin (n + 1)) :
    index f (f.1 i.castSucc) = i := by
  apply le_antisymm
  · obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [index_le_castSucc_iff]
      exact hf (by simp)
    · apply Fin.le_last
  · rw [le_index_iff]

lemma index_apply_last :
    index f (f.1 (Fin.last _)) = Fin.last _ := by
  by_contra!
  obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last this
  replace hi := hi.symm.le
  rw [index_le_castSucc_iff, ← not_le] at hi
  exact hi (f.1.monotone (Fin.le_last _))

noncomputable def α (i : Fin (n + 1)) (x : unitInterval) : ℝ :=
  Real.affineMap (f.1 i.castSucc) ((f.1 i.succ))
    (g.1 i.castSucc) (g.1 i.succ) x

include hf hg in
lemma α_lt (i : Fin (n + 1)) (x : unitInterval) (hx : x < f.1 i.succ) :
    α f g i x < g.1 i.succ :=
  Real.affineMap_lt _ _ _ _ (hf (i.castSucc_lt_succ)) (hg (i.castSucc_lt_succ)) x hx

include hf hg in
lemma le_α (i : Fin (n + 1)) (x : unitInterval) (hx : f.1 i.castSucc ≤ x) :
    g.1 i.castSucc ≤ α f g i x :=
  Real.le_affineMap _ _ _ _ (hf (i.castSucc_lt_succ)) (hg (i.castSucc_lt_succ)) x hx

include hf hg in
lemma α_surjective_on (i : Fin (n + 1)) (y : ℝ) (hy₀ : g.1 i.castSucc ≤ y) (hy₁ : y ≤ g.1 i.succ) :
    ∃ (x : unitInterval), f.1 i.castSucc ≤ x ∧ x ≤ f.1 i.succ ∧ α f g i x = y := by
  obtain ⟨x, hx₀, hx₁, h⟩ := Real.affineMap_surjective_on _ _ _ _
    (hf (i.castSucc_lt_succ)) (hg (i.castSucc_lt_succ)) y hy₀ hy₁
  exact ⟨⟨x, (f.1 i.castSucc).2.1.trans hx₀, hx₁.trans (f.1 i.succ).2.2⟩, hx₀, hx₁, h⟩

noncomputable def φ (x : unitInterval) : ℝ :=
  α f g  (index f x) x

include hf

lemma φ_apply (i : Fin (n + 2)) :
    φ f g (f.1 i) = g.1 i := by
  dsimp [φ]
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · have := index_apply_castSucc f hf
    dsimp at this
    rw [this]
    simp [α]
  · have := index_apply_last f
    dsimp at this
    simp only [this, α, SimplexCategory.len_mk, Fin.succ_last]
    rw [Real.affineMap_apply₁]
    intro h
    rw [← Subtype.ext_iff] at h
    exact (hf (Fin.castSucc_lt_succ (Fin.last n))).ne h

lemma φ_zero : φ f g 0 = 0 := by
  simpa only [f.2.1, g.2.1] using φ_apply f g hf 0

lemma φ_one : φ f g 1 = 1 := by
  have h₁ := f.2.2
  have h₂ := g.2.2
  simp only [SimplexCategory.len_mk] at h₁ h₂
  simpa [h₁, h₂] using φ_apply f g hf (Fin.last _)

include hg

lemma strictMono_φ : StrictMono (φ f g) := by
  have := hf
  have := hg
  intro x y h
  dsimp only [φ]
  generalize hi : index f x = i
  generalize hj : index f y = j
  have hij := monotone_index f h.le
  rw [hi, hj] at hij
  obtain hij | rfl := hij.lt_or_eq
  · refine lt_of_lt_of_le (α_lt f g hf hg i x ?_)
      (le_trans (g.1.monotone (by simpa)) (le_α f g hf hg j y ?_))
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hij)
      rw [Fin.succ_castSucc, ← index_le_castSucc_iff, hi]
    · rw [← le_index_iff, hj]
  · exact Real.strictMono_affineMap _ _ _ _
      (hf i.castSucc_lt_succ) (hg i.castSucc_lt_succ) h

noncomputable def ψ (x : unitInterval) : unitInterval :=
  ⟨φ f g x,
    ⟨by simpa only [φ_zero f g hf] using
      (strictMono_φ f g hf hg).monotone (show 0 ≤ x from x.2.1),
    by simpa only [φ_one f g hf] using
      (strictMono_φ f g hf hg).monotone (show x ≤ 1 from x.2.2)⟩⟩

lemma strictMono_ψ : StrictMono (ψ f g hf hg) :=
  fun _ _ h ↦ strictMono_φ f g hf hg h

lemma surjective_ψ : Function.Surjective (ψ f g hf hg) := by
  intro y
  generalize hi : index g y = i
  obtain ⟨x, hx₀, hx₁, h⟩ := α_surjective_on f g hf hg i y.1
    (by rw [← hi, Subtype.coe_le_coe, ← le_index_iff]) (by
      rw [Subtype.coe_le_coe]
      obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · apply le_of_lt
        rw [Fin.succ_castSucc, ← index_le_castSucc_iff, hi]
      · have := g.2.2
        dsimp at this
        simpa only [Fin.succ_last, SimplexCategory.len_mk, Nat.succ_eq_add_one, this] using y.2.2)
  have hi' : index f x = i := by
    apply le_antisymm
    · obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · rw [index_le_castSucc_iff]
        obtain hx₁ | rfl := hx₁.lt_or_eq
        · exact hx₁
        · exfalso
          dsimp [α] at h
          rw [Real.affineMap_apply₁, ← Subtype.ext_iff, Fin.succ_castSucc] at h; swap
          · intro h
            rw [← Subtype.ext_iff] at h
            exact (hf (Fin.castSucc_lt_succ i.castSucc)).ne h
          subst h
          have := index_apply_castSucc g hg i.succ
          dsimp at this
          simp [this, Fin.ext_iff] at hi
      · apply Fin.le_last
    · rwa [le_index_iff]
  exact ⟨x, by simpa [Subtype.ext_iff, ψ, φ, hi']⟩

noncomputable def orderIso : unitInterval ≃o unitInterval :=
  StrictMono.orderIsoOfSurjective _ (strictMono_ψ f g hf hg)
    (surjective_ψ f g hf hg)

end exists_orderIso

include hf hg in
lemma exists_orderIso :
    ∃ (φ : unitInterval ≃o unitInterval),
      (action φ.toOrderEmbedding.toOrderHom φ.continuous (by simp) (by simp)).app _ f = g :=
  ⟨exists_orderIso.orderIso f g hf hg, by
    dsimp
    ext i : 4
    exact exists_orderIso.φ_apply f g hf i⟩

end unitInterval

end TopCat.cosimp
