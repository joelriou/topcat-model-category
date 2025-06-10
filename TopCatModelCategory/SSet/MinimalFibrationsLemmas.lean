import TopCatModelCategory.SSet.MinimalFibrations
import TopCatModelCategory.SSet.FiberwiseHomotopy

universe u

open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen ChosenFiniteProducts

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
  have := (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u}
    (boundary n) _ (anodyneExtensions.face 0)).hasLeftLiftingProperty p
  let t : B _⦋n⦌  := p.app _ s₁
  have sq : CommSq sorry ((∂Δ[n]).unionProd (stdSimplex.face {(0 : Fin 2)})).ι p
      (fst _ _ ≫ yonedaEquiv.symm t) := sorry
  let ρ : SimplexOverRelStruct p s₁ s₂ :=
    { h := sq.lift
      h₀ := sorry
      h₁ := sorry
      π := sorry
      d := sorry
      hπ := sorry
      hd := sorry }
  exact ρ.eq

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
