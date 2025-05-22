import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.SmallObject

universe u

open HomotopicalAlgebra CategoryTheory Simplicial
  SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

section

variable {F : SSet.{0}} {p : F ⟶ Δ[0]} (hp : I.rlp p)

include hp
lemma nonempty_of_rlp_I : Nonempty (F _⦋0⦌) := by
  have sq : CommSq (boundary.isInitial.to F) (boundary 0).ι p (𝟙 _) :=
    ⟨boundary.isInitial.hom_ext _ _⟩
  have := hp _ ⟨0⟩
  exact ⟨yonedaEquiv sq.lift⟩

lemma subsingleton_π₀_of_rlp_I : Subsingleton (π₀ F) where
  allEq x₀ x₁ := by
    obtain ⟨x₀, rfl⟩ := x₀.mk_surjective
    obtain ⟨x₁, rfl⟩ := x₁.mk_surjective
    have sq :
      CommSq (boundary₁.desc x₀ x₁) (boundary 1).ι p
        (stdSimplex.isTerminalObj₀.from _) :=
      ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have := hp _ ⟨1⟩
    apply π₀.sound (yonedaEquiv sq.lift)
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₀_desc x₀ x₁, ← boundary₁.ι₀ ≫= sq.fac_left,
        boundary₁.ι₀_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₁_desc x₀ x₁, ← boundary₁.ι₁ ≫= sq.fac_left,
        boundary₁.ι₁_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]

lemma subsingleton_π_of_rlp_I (n : ℕ) (x : F _⦋0⦌) :
    Subsingleton (π n F x) := by
  have : Fibration p := by
    rw [fibration_iff]
    exact rlp_I_le_rlp_J _ hp
  have : IsFibrant F := by
    rwa [isFibrant_iff_of_isTerminal p stdSimplex.isTerminalObj₀]
  obtain _ | n := n
  · rw [← (π₀EquivπZero x).subsingleton_congr]
    exact subsingleton_π₀_of_rlp_I hp
  suffices ∀ (s : π (n + 1) F x), s = 1 from
    ⟨fun _ _ ↦ by simp [this]⟩
  intro s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  change _ = π.mk _
  rw [π.mk_eq_mk_iff]
  obtain ⟨φ, hφ₀, hφ⟩ : ∃ (φ : (boundary (n + 2) : SSet) ⟶ F), boundary.ι 0 ≫ φ = s.map ∧
      ∀ (i : Fin (n + 3)) (hi : i ≠ 0), boundary.ι i ≫ φ = const x := by
    let α (i : Fin (n + 3)) : Δ[n + 1] ⟶ F := if i = 0 then s.map else const x
    obtain ⟨φ, hφ⟩ := boundary.exists_desc α (by aesop)
    refine ⟨φ, ?_, fun i hi ↦ ?_⟩
    · simp only [hφ, α, if_pos rfl]
    · simp only [hφ, α, if_neg hi]
  have sq : CommSq φ (boundary (n + 2)).ι p (stdSimplex.isTerminalObj₀.from _) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have := hp _ ⟨n + 2⟩
  have (i : Fin (n + 3)) : stdSimplex.δ i ≫ sq.lift = boundary.ι i ≫ φ := by
    rw [← boundary.ι_ι_assoc, sq.fac_left]
  exact ⟨{
    map := sq.lift
    δ_map_of_gt j hj := by rw [this, hφ _ (by rintro rfl; simp at hj)]
    δ_map_of_lt j hj := by simp at hj
    δ_succ_map := by rw [this, hφ _ (by simp), Subcomplex.RelativeMorphism.const_map]
    δ_castSucc_map := by rw [this, Fin.castSucc_zero, hφ₀]
  }⟩

end

section

variable {E B : SSet.{0}} {p : E ⟶ B} (hp : I.rlp p)

namespace W.of_rlp_I

include hp

lemma fiber_rlp_I (b : B _⦋0⦌) :
    I.rlp (stdSimplex.isTerminalObj₀.from (Subcomplex.fiber p b)) :=
  MorphismProperty.of_isPullback (Subcomplex.fiber_isPullback p b) hp

variable [IsFibrant E] [IsFibrant B]
/-
    obtain ⟨x₀, rfl⟩ := x₀.mk_surjective
    obtain ⟨x₁, rfl⟩ := x₁.mk_surjective
    have sq :
      CommSq (boundary₁.desc x₀ x₁) (boundary 1).ι p
        (stdSimplex.isTerminalObj₀.from _) :=
      ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have := hp _ ⟨1⟩
    apply π₀.sound (yonedaEquiv sq.lift)
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₀_desc x₀ x₁, ← boundary₁.ι₀ ≫= sq.fac_left,
        boundary₁.ι₀_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₁_desc x₀ x₁, ← boundary₁.ι₁ ≫= sq.fac_left,
        boundary₁.ι₁_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]

-/

omit [IsFibrant E] in
lemma bijective_mapπ₀ : Function.Bijective (mapπ₀ p) := by
  constructor
  · intro e₀ e₁ h
    obtain ⟨e₀, rfl⟩ := e₀.mk_surjective
    obtain ⟨e₁, rfl⟩ := e₁.mk_surjective
    simp only [mapπ₀_mk, π₀_mk_eq_π₀_mk_iff] at h
    obtain ⟨edge⟩ := h
    have sq : CommSq (boundary₁.desc e₀ e₁) (boundary 1).ι p edge.map := ⟨by aesop⟩
    have := hp _ ⟨1⟩
    apply π₀.sound (yonedaEquiv sq.lift)
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₀_desc e₀ e₁, ← boundary₁.ι₀ ≫= sq.fac_left,
        boundary₁.ι₀_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₁_desc e₀ e₁, ← boundary₁.ι₁ ≫= sq.fac_left,
        boundary₁.ι₁_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
  · intro b
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have sq : CommSq (boundary.isInitial.to E) (boundary 0).ι p
      (yonedaEquiv.symm b) := ⟨boundary.isInitial.hom_ext _ _⟩
    have := hp _ ⟨0⟩
    refine ⟨π₀.mk (yonedaEquiv sq.lift), ?_⟩
    simp only [mapπ₀_mk]
    congr
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_comp]
    simp

lemma bijective_mapπ_succ (n : ℕ) (e : E _⦋0⦌) (b : B _⦋0⦌) (h : p.app _ e = b) :
    Function.Bijective (mapπ p (n + 1) e b h) := by
  have : Fibration p := by
    rw [fibration_iff]
    exact rlp_I_le_rlp_J _ hp
  constructor
  · suffices ∀ (y : π (n + 1) E e), mapπ p (n + 1) e b h y = 1 → y = 1 by
      intro y₁ y₂ hy
      rw [← mul_inv_eq_one]
      apply this
      rw [mapπ_mul, mapπ_inv, hy, mul_inv_cancel]
    intro y hy
    obtain ⟨x, rfl⟩ := HomotopySequence.exists_of_map₂_eq_one hy
    obtain rfl := (subsingleton_π_of_rlp_I (fiber_rlp_I hp b) _ _).elim x 1
    simp [HomotopySequence.map₁]
  · intro y
    apply HomotopySequence.exists_of_δ'_eq_one (i := 0)
    apply (subsingleton_π_of_rlp_I (fiber_rlp_I hp b) n _).elim

end W.of_rlp_I

include hp in
open W.of_rlp_I in
lemma W.of_rlp_I [IsFibrant E] [IsFibrant B] : KanComplex.W p := by
  rw [W_iff]
  exact ⟨of_rlp_I.bijective_mapπ₀ hp, bijective_mapπ_succ hp⟩

end

lemma weakEquivalence_iff_of_fibration {E B : SSet.{0}} (p : E ⟶ B)
    [IsFibrant E] [IsFibrant B] [Fibration p] :
    I.rlp p ↔ KanComplex.W p := by
  refine ⟨fun hp ↦ W.of_rlp_I hp, ?_⟩
  sorry

end KanComplex

end SSet
