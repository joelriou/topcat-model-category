import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
import TopCatModelCategory.SSet.SmallObject

universe u

open HomotopicalAlgebra CategoryTheory Simplicial
  SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

section

variable {X : SSet.{0}} {p : X ⟶ Δ[0]} (hp : I.rlp p)

include hp
lemma nonempty_of_rlp_I : Nonempty (X _⦋0⦌) := by
  have sq : CommSq (boundary.isInitial.to X) (boundary 0).ι p (𝟙 _) :=
    ⟨boundary.isInitial.hom_ext _ _⟩
  have := hp _ ⟨0⟩
  exact ⟨yonedaEquiv sq.lift⟩

lemma subsingleton_π₀_of_rlp_I : Subsingleton (π₀ X) where
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

lemma subsingleton_π_of_rlp_I {n : ℕ} (x : X _⦋0⦌) :
    Subsingleton (π n X x) := by
  have : Fibration p := by
    rw [fibration_iff]
    exact rlp_I_le_rlp_J _ hp
  have : IsFibrant X := by
    rwa [isFibrant_iff_of_isTerminal p stdSimplex.isTerminalObj₀]
  obtain _ | n := n
  · rw [← (π₀EquivπZero x).subsingleton_congr]
    exact subsingleton_π₀_of_rlp_I hp
  suffices ∀ (s : π (n + 1) X x), s = 1 from
    ⟨fun _ _ ↦ by simp [this]⟩
  intro s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  change _ = π.mk _
  rw [π.mk_eq_mk_iff]
  obtain ⟨φ, hφ₀, hφ⟩ : ∃ (φ : (boundary (n + 2) : SSet) ⟶ X), boundary.ι 0 ≫ φ = s.map ∧
      ∀ (i : Fin (n + 3)) (hi : i ≠ 0), boundary.ι i ≫ φ = const x := by
    let α (i : Fin (n + 3)) : Δ[n + 1] ⟶ X := if i = 0 then s.map else const x
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

lemma weakEquivalence_iff_of_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [IsFibrant X] [IsFibrant Y] [Fibration p] :
    I.rlp p ↔ KanComplex.W p :=
  sorry

end KanComplex

end SSet
