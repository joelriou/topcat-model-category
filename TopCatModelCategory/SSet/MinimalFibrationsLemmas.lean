import TopCatModelCategory.SSet.MinimalFibrations
import TopCatModelCategory.SSet.FiberwiseHomotopy

universe u

open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen ChosenFiniteProducts Limits MonoidalClosed

namespace SSet

namespace MinimalFibration

variable {E B : SSet.{u}} (p : E ⟶ B) [MinimalFibration p]

lemma congr_ι₁_comp {n : ℕ} (h₁ h₂ : Δ[n] ⊗ Δ[1] ⟶ E) (b : B _⦋n⦌)
    (h₁b : h₁ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (h₂b : h₂ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (hι : ∂Δ[n].ι ▷ _ ≫ h₁ = ∂Δ[n].ι ▷ _ ≫ h₂)
    (eq : ι₀ ≫ h₁ = ι₀ ≫ h₂) :
    ι₁ ≫ h₁ = ι₁ ≫ h₂ := by
  obtain ⟨φ, α, eq₁, eq₂, eq₃⟩ := exists_path_composition₀_above_of_fibration' (ihomToPullback ∂Δ[n].ι p)
    (curry h₁) (curry h₂) (by
      apply uncurry_injective
      simp only [← cancel_epi (stdSimplex.rightUnitor _).inv, uncurry_natural_left,
        stdSimplex.rightUnitor_inv_map_δ_one_assoc, uncurry_curry, eq]) (by
      ext : 1
      · simp [curry_pre_app, hι]
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          ← curry_natural_right, h₁b, h₂b])
  obtain ⟨δ, π, sq, rfl⟩ := ihomToPullbackTgt₀Mk_surjective α
  have str : SimplexOverRelStruct p (yonedaEquiv (ι₁ ≫ h₁)) (yonedaEquiv (ι₁ ≫ h₂)) :=
    { h := uncurry φ
      h₀ := by
        rw [Equiv.symm_apply_apply,
          ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
          ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
          Iso.cancel_iso_inv_left, ← uncurry_natural_left, eq₁,
          uncurry_natural_left, uncurry_curry]
      h₁ := by
        rw [Equiv.symm_apply_apply,
          ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
          ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
          Iso.cancel_iso_inv_left, ← uncurry_natural_left, eq₂,
          uncurry_natural_left, uncurry_curry]
      π := π
      d := δ
      hπ := by
        have := eq₃ =≫ pullback.snd _ _
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          const_comp, pullback_snd_app_ihomToPullbackTgt₀Mk] at this
        rw [← uncurry_natural_right, this]
        rfl
      hd := by
        have := eq₃ =≫ pullback.fst _ _
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          const_comp, pullback_fst_app_ihomToPullbackTgt₀Mk] at this
        rw [← uncurry_pre_app, this]
        rfl
      }
  exact yonedaEquiv.injective str.eq

end MinimalFibration

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
  simpa using MinimalFibration.congr_ι₁_comp p (yonedaEquiv.symm s₁ ▷ _ ≫ hu.h)
    (yonedaEquiv.symm s₂ ▷ _ ≫ hu.h) t (by simp [ht₁]) (by simp [ht₂]) (by
      simp only [← comp_whiskerRight_assoc]
      congr 2
      obtain _ | n := n
      · ext
      · refine boundary.hom_ext (fun j ↦ ?_)
        simp only [boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
        congr 1
        exact hn _ (by simp) (by simp only [SSet.δ_naturality_apply, hs])) (by simpa)

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
