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

lemma congr_ι₀_comp {n : ℕ} (h₁ h₂ : Δ[n] ⊗ Δ[1] ⟶ E) (b : B _⦋n⦌)
    (h₁b : h₁ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (h₂b : h₂ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (hι : ∂Δ[n].ι ▷ _ ≫ h₁ = ∂Δ[n].ι ▷ _ ≫ h₂)
    (eq : ι₁ ≫ h₁ = ι₁ ≫ h₂) :
    ι₀ ≫ h₁ = ι₀ ≫ h₂ := by
  obtain ⟨φ, α, eq₁, eq₂, eq₃⟩ := exists_path_composition₂_above_of_fibration' (ihomToPullback ∂Δ[n].ι p)
    (curry h₁) (curry h₂) (by
      apply uncurry_injective
      simp only [← cancel_epi (stdSimplex.rightUnitor _).inv, uncurry_natural_left,
        stdSimplex.rightUnitor_inv_map_δ_zero_assoc, uncurry_curry, eq]) (by
      ext : 1
      · simp [curry_pre_app, hι]
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          ← curry_natural_right, h₁b, h₂b]
        )
  obtain ⟨δ, π, sq, rfl⟩ := ihomToPullbackTgt₀Mk_surjective α
  have str : SimplexOverRelStruct p (yonedaEquiv (ι₀ ≫ h₁)) (yonedaEquiv (ι₀ ≫ h₂)) :=
    { h := uncurry φ
      h₀ := by
        rw [Equiv.symm_apply_apply,
          ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
          ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
          Iso.cancel_iso_inv_left, ← uncurry_natural_left, eq₁,
          uncurry_natural_left, uncurry_curry]
      h₁ := by
        rw [Equiv.symm_apply_apply,
          ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
          ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
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
  obtain ⟨n⟩ := n
  induction' n using SimplexCategory.rec with n
  induction' n using Nat.strong_induction_on with n hn
  intro x
  obtain ⟨y, hy⟩ :
      ∃ (y : (∂Δ[n] : SSet) ⟶ E), y ≫ u = ∂Δ[n].ι ≫ yonedaEquiv.symm x := by
    obtain _ | n := n
    · exact ⟨boundary.isInitial.to _, by ext⟩
    · let s (i : Fin (n + 2)) : E _⦋n⦌ := (hn n (by simp) (E.δ i x)).choose
      have hs (i : Fin (n + 2)) : u.app _ (s i) = E.δ i x :=
        (hn n (by simp) (E.δ i x)).choose_spec
      obtain _ | n := n
      · refine ⟨boundary₁.desc (s 1) (s 0), ?_⟩
        apply boundary₁.hom_ext <;> simp [hs, stdSimplex.δ_comp_yonedaEquiv_symm]
      · obtain ⟨φ, hφ⟩ := boundary.exists_desc (fun i ↦ yonedaEquiv.symm (s i)) (by
          intro j k hjk
          dsimp
          obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
          obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
          simp only [Fin.pred_succ, Fin.castPred_castSucc,
            stdSimplex.δ_comp_yonedaEquiv_symm]
          congr 1
          apply hu.injective_app_of_minimalFibration
          simp only [δ_naturality_apply, hs]
          rw [← Fin.le_castSucc_iff, Fin.castSucc_le_castSucc_iff] at hjk
          exact (E.δ_comp_δ_apply hjk _).symm)
        refine ⟨φ, boundary.hom_ext (fun i ↦ ?_)⟩
        rw [reassoc_of% hφ, boundary.ι_ι_assoc]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_symm_comp, Equiv.apply_symm_apply, hs,
          stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦ₃⟩ :
      ∃ (Φ : Δ[n] ⊗ Δ[1] ⟶ E), ι₀ ≫ Φ = yonedaEquiv.symm x ∧
        ∂Δ[n].ι ▷ _ ≫ Φ = y ▷ _ ≫ hu.h ∧ Φ ≫ p = fst _ _ ≫ yonedaEquiv.symm x ≫ p := by
    let i : pushout ∂Δ[n].ι ι₀ ⟶ Δ[n] ⊗ Δ[1] :=
      pushout.desc (ι₀.{u}) (∂Δ[n].ι ▷ Δ[1]) (by simp)
    have sq : CommSq (pushout.desc (yonedaEquiv.symm x) (y ▷ _ ≫ hu.h) (by aesop)) i
        p (fst _ _ ≫ yonedaEquiv.symm x ≫ p) := ⟨by
      ext : 1
      · simp [i]
      · simp only [colimit.ι_desc_assoc, span_right,
          Subcomplex.RelativeMorphism.botEquiv_symm_apply_map, PushoutCocone.mk_pt,
          PushoutCocone.mk_ι_app, Category.assoc, fac, whiskerRight_fst_assoc,
          yonedaEquiv_symm_comp, i]
        conv_lhs => rw [← hu.fac₀, reassoc_of% hy, yonedaEquiv_symm_comp]⟩
    have := anodyneExtensions.pushout_desc_ι₀_whiskerRight_mono ∂Δ[n].ι p Fibration.mem
    refine ⟨sq.lift, ?_, ?_, by simp⟩
    · have := pushout.inl _ _ ≫= sq.fac_left
      dsimp [i] at this
      rwa [pushout.inl_desc_assoc, pushout.inl_desc] at this
    · have := pushout.inr _ _ ≫= sq.fac_left
      dsimp [i] at this
      rwa [pushout.inr_desc_assoc, pushout.inr_desc] at this
  obtain ⟨z, hz⟩ := yonedaEquiv.symm.surjective (ι₁ ≫ Φ)
  refine ⟨z, ?_⟩
  have := MinimalFibration.congr_ι₀_comp p Φ
    (yonedaEquiv.symm z ▷ _ ≫ hu.h) (p.app _ x) (by aesop) (by
    simp only [Category.assoc, fac, whiskerRight_fst_assoc, yonedaEquiv_symm_comp]
    congr 1
    simp only [← yonedaEquiv_symm_comp, hz, Category.assoc, hΦ₃, ι₁_fst_assoc]) (by
    rw [hz, hΦ₂]
    rw [← comp_whiskerRight_assoc]
    rw [← ι₁_comp_assoc, hΦ₂, ι₁_comp_assoc, hu.h₁,
      Subcomplex.RelativeMorphism.botEquiv_symm_apply_map, Category.comp_id]) (by simp [hz])
  apply yonedaEquiv.symm.injective
  simp [← hΦ₁, this]

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
