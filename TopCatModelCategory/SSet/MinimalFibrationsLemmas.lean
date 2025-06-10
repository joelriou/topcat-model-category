import TopCatModelCategory.SSet.MinimalFibrations
import TopCatModelCategory.SSet.FiberwiseHomotopy

universe u

open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen ChosenFiniteProducts Limits

namespace SSet

namespace FiberwiseHomotopy
variable {E B : SSet.{u}} {p : E ⟶ B} [MinimalFibration p]
  {u : E ⟶ E} (hu : FiberwiseHomotopy p p u (𝟙 _))

include hu

lemma injective_app_of_minimalFibration (n : SimplexCategoryᵒᵖ) :
    Function.Injective (u.app n) := by
  have : MinimalFibration p := inferInstance
  have := hu
  obtain ⟨n⟩ := n
  induction' n using SimplexCategory.rec with n
  induction' n using Nat.strong_induction_on with n hn
  intro s₁ s₂ hs
  obtain ⟨t, ht₁, ht₂⟩ : ∃ (t : B _⦋n⦌), p.app _ s₁ = t ∧ p.app _ s₂ = t := ⟨_, rfl, by
    convert congr_arg (p.app _ ) hs.symm using 1
    all_goals
    · conv_lhs => rw [← hu.fac₀]; dsimp⟩
  have : ∃ (w : (∂Δ[n] : SSet) ⟶ E), ∂Δ[n].ι ≫ yonedaEquiv.symm s₁ = w ∧
      ∂Δ[n].ι ≫ yonedaEquiv.symm s₂ = w := ⟨_, rfl, by
    obtain _ | n := n
    · ext
    · refine boundary.hom_ext (fun j ↦ ?_)
      simp only [boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      exact hn _ (by simp) (by simp only [SSet.δ_naturality_apply, hs])⟩
  sorry

lemma surjective_app_of_minimalFibration (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (u.app n) := by
  have := hu.injective_app_of_minimalFibration n
  sorry

lemma isIso_of_minimalFibration : IsIso u := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  exact ⟨hu.injective_app_of_minimalFibration n,
    hu.surjective_app_of_minimalFibration n⟩

end FiberwiseHomotopy

namespace MinimalFibration

lemma isIso_of_fiberwiseHomotopyEquiv {E E' B : SSet.{u}} (p : E ⟶ B) (p' : E' ⟶ B)
    [MinimalFibration p] [MinimalFibration p']
    (u : E ⟶ E') (v : E' ⟶ E) (huv : FiberwiseHomotopy p p (u ≫ v) (𝟙 E))
    (hvu : FiberwiseHomotopy p' p' (v ≫ u) (𝟙 E')) : IsIso u := by
  have := huv.isIso_of_minimalFibration
  have := hvu.isIso_of_minimalFibration
  have := mono_of_mono u v
  have := epi_of_epi v u
  exact isIso_of_mono_of_epi u

end MinimalFibration

end SSet
