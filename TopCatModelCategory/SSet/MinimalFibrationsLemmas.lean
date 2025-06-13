import TopCatModelCategory.SSet.MinimalFibrations
import TopCatModelCategory.SSet.FiberwiseHomotopy
import TopCatModelCategory.TrivialBundle
import TopCatModelCategory.CommSq

universe u

open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen ChosenFiniteProducts Limits MonoidalClosed

namespace SSet

lemma exists_retraction_of_homotopy_of_fibration {E A B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] (j : A ⟶ B) (r : B ⟶ A) (retract : j ≫ r = 𝟙 A)
    (h : Homotopy (𝟙 B) (r ≫ j)) (hj : j ▷ _ ≫ h.h = fst _ _ ≫ j)
    {E' : SSet.{u}} {i : E' ⟶ E} {p' : E' ⟶ A} (sq : IsPullback i p' p j) :
    ∃ (r' : E ⟶ E') (_ : i ≫ r' = 𝟙 E') (h' : Homotopy (𝟙 E) (r' ≫ i)),
      h'.h ≫ p = p ▷ _ ≫ h.h ∧ i ▷ _ ≫ h'.h = fst _ _ ≫ i ∧ r' ≫ p' = p ≫ r := by
  have : Mono i :=
    MorphismProperty.of_isPullback (P := .monomorphisms _) sq.flip
      (mono_of_mono_fac retract)
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
    homotopy_extension_property₀ i p (fst _ _ ≫ i) (𝟙 E) (by simp)
      (p ▷ _ ≫ h.h) (by simp) (by
        rw [← comp_whiskerRight_assoc, sq.w, comp_whiskerRight_assoc, hj,
          whiskerRight_fst_assoc, Category.assoc, sq.w])
  obtain ⟨l, hl₁, hl₂⟩ := sq.exists_lift (ι₁ ≫ φ) (p ≫ r) (by
    rw [Category.assoc, hφ₃, ι₁_comp_assoc, h.h₁, Category.assoc])
  refine ⟨l, ?_, { h := φ }, hφ₃, by simpa, hl₂⟩
  · rw [← cancel_mono i, Category.assoc, hl₁, ← ι₁_comp_assoc, hφ₂,
      ι₁_fst_assoc, Category.id_comp]

lemma exists_retraction_of_homotopy_of_fibration' {E A B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] (j : A ⟶ B) (r : B ⟶ A) (retract : j ≫ r = 𝟙 A)
    (h : Homotopy (r ≫ j) (𝟙 B)) (hj : j ▷ _ ≫ h.h = fst _ _ ≫ j)
    {E' : SSet.{u}} {i : E' ⟶ E} {p' : E' ⟶ A} (sq : IsPullback i p' p j) :
    ∃ (r' : E ⟶ E') (_ : i ≫ r' = 𝟙 E') (h' : Homotopy (r' ≫ i) (𝟙 E)),
      h'.h ≫ p = p ▷ _ ≫ h.h ∧ i ▷ _ ≫ h'.h = fst _ _ ≫ i ∧ r' ≫ p' = p ≫ r := by
  have : Mono i :=
    MorphismProperty.of_isPullback (P := .monomorphisms _) sq.flip
      (mono_of_mono_fac retract)
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
    homotopy_extension_property₁ i p (fst _ _ ≫ i) (𝟙 E) (by simp)
      (p ▷ _ ≫ h.h) (by simp) (by
        rw [← comp_whiskerRight_assoc, sq.w, comp_whiskerRight_assoc, hj,
          whiskerRight_fst_assoc, Category.assoc, sq.w])
  obtain ⟨l, hl₁, hl₂⟩ := sq.exists_lift (ι₀ ≫ φ) (p ≫ r) (by
    rw [Category.assoc, hφ₃, ι₀_comp_assoc, h.h₀, Category.assoc])
  refine ⟨l, ?_, { h := φ }, hφ₃, by simpa, hl₂⟩
  · rw [← cancel_mono i, Category.assoc, hl₁, ← ι₀_comp_assoc, hφ₂,
      ι₀_fst_assoc, Category.id_comp]

namespace stdSimplex

lemma isPullback_whiskerLeft_snd (X : SSet.{u}) {A B : SSet.{u}} (i : A ⟶ B) :
    IsPullback (X ◁ i) (snd _ _) (snd _ _) i where
  w := by simp
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ lift (s.fst ≫ fst _ _) s.snd)
      (fun s ↦ by ext : 1 <;> simp [s.condition])
      (fun s ↦ by simp)
      (fun s m hm₁ hm₂ ↦ by
        ext : 1
        · simp [← hm₁]
        · simp [← hm₂])⟩

lemma isPullback_ι₀ (X : SSet.{u}) :
    IsPullback ι₀ (isTerminalObj₀.from X) (snd X Δ[1]) (stdSimplex.δ 1) :=
  (isPullback_whiskerLeft_snd X (stdSimplex.δ (1 : Fin 2))).of_iso
    (rightUnitor _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (isTerminalObj₀.hom_ext _ _) (by simp) (by simp)

lemma isPullback_ι₁ (X : SSet.{u}) :
    IsPullback ι₁ (isTerminalObj₀.from X) (snd X Δ[1]) (stdSimplex.δ 0) :=
  (isPullback_whiskerLeft_snd X (stdSimplex.δ (0 : Fin 2))).of_iso
    (rightUnitor _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (isTerminalObj₀.hom_ext _ _) (by simp) (by simp)

lemma isPullback_ι₀_whiskerRight {X Y : SSet.{u}} (p : X ⟶ Y) :
    IsPullback ι₀ p (p ▷ Δ[1]) ι₀ :=
  IsPullback.of_bot  (by simpa using isPullback_ι₀ X)
    (by simp) (isPullback_ι₀ Y)

lemma isPullback_ι₁_whiskerRight {X Y : SSet.{u}} (p : X ⟶ Y) :
    IsPullback ι₁ p (p ▷ Δ[1]) ι₁ :=
  IsPullback.of_bot  (by simpa using isPullback_ι₁ X)
    (by simp) (isPullback_ι₁ Y)

open anodyneExtensions.retractArrowHornCastSuccι in
noncomputable def deformationRetract :
    ∀ (n : ℕ), DeformationRetract Δ[0] Δ[n]
  | 0 =>
    { toRetract := .refl _
      h := fst _ _ }
  | n + 1 =>
    { i := SSet.const (obj₀Equiv.symm 0)
      r := SSet.const (obj₀Equiv.symm 0)
      retract := isTerminalObj₀.hom_ext _ _
      h := r (n := n) (0)
      hi := by
        rw [← cancel_epi (stdSimplex.leftUnitor _).inv]
        apply yonedaEquiv.injective
        ext i : 1
        fin_cases i <;> rfl }

@[simp]
lemma deformationRetract_i (n : ℕ) :
    (deformationRetract.{u} n).i = SSet.const (obj₀Equiv.symm 0) := by
  obtain _ | n := n
  · apply isTerminalObj₀.hom_ext
  · rfl

@[simp]
lemma deformationRetract_r (n : ℕ) :
    (deformationRetract.{u} n).r = SSet.const (obj₀Equiv.symm 0) := by
  obtain _ | n := n
  · apply isTerminalObj₀.hom_ext
  · rfl

@[reassoc]
lemma ι₀_β_hom_deformationRetract_h :
    ι₀ ≫ (β_ _ _).hom ≫ (stdSimplex.deformationRetract.{u} 1).h =
      SSet.const (obj₀Equiv.symm 0) :=
  yonedaEquiv.injective (by
    ext i : 1
    fin_cases i <;> rfl)

open anodyneExtensions.retractArrowHornSuccι in
noncomputable def homotopyIdConstLast :
    ∀ (n : ℕ), Homotopy.{u} (𝟙 Δ[n]) (SSet.const (obj₀Equiv.symm (Fin.last n)))
  | 0 => { h := fst _ _ }
  | n + 1 => { h := r (Fin.last n) }

@[reassoc]
lemma ι₁_β_hom_homotopyIdConstLast_h :
    ι₁ ≫ (β_ _ _).hom ≫ (stdSimplex.homotopyIdConstLast.{u} 1).h =
      SSet.const (obj₀Equiv.symm 1) :=
  yonedaEquiv.injective (by
    ext i : 1
    fin_cases i <;> rfl)

end stdSimplex

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

lemma congr_pullback_stdSimplex_one {E B : SSet.{u}} (p : E ⟶ B ⊗ Δ[1])
    [MinimalFibration p]
    {E₀ : SSet.{u}} {j₀ : E₀ ⟶ E} {p₀ : E₀ ⟶ B} (sq₀ : IsPullback j₀ p₀ p ι₀)
    {E₁ : SSet.{u}} {j₁ : E₁ ⟶ E} {p₁ : E₁ ⟶ B} (sq₁ : IsPullback j₁ p₁ p ι₁) :
    ∃ (e : E₀ ≅ E₁), e.hom ≫ p₁ = p₀ := by
  have : MinimalFibration p₀ :=
    MorphismProperty.of_isPullback (P := minimalFibrations) sq₀ (by assumption)
  have : MinimalFibration p₁ :=
    MorphismProperty.of_isPullback (P := minimalFibrations) sq₁ (by assumption)
  obtain ⟨r₀, hr₀, k₀, h₁, h₂, h₃⟩ :=
    exists_retraction_of_homotopy_of_fibration' p ι₀ (fst _ _) (by simp)
      ((stdSimplex.deformationRetract 1).homotopy.whiskerLeft B) (by
        change B ◁ (ι₀ ≫ (β_ _ _).hom ≫ (stdSimplex.deformationRetract.{u} 1).h) = _
        rw [stdSimplex.ι₀_β_hom_deformationRetract_h]
        rfl) sq₀
  obtain ⟨r₁, hr₁, k₁, h₄, h₅, h₆⟩ :=
    exists_retraction_of_homotopy_of_fibration p ι₁ (fst _ _) (by simp)
      ((stdSimplex.homotopyIdConstLast.{u} 1).whiskerLeft B) (by
      change B ◁ (ι₁ ≫ (β_ _ _).hom ≫ (stdSimplex.homotopyIdConstLast.{u} 1).h) = _
      rw [stdSimplex.ι₁_β_hom_homotopyIdConstLast_h]
      rfl) sq₁
  dsimp at h₁ h₄
  have : IsIso (j₀ ≫ r₁) :=
    isIso_of_fiberwiseHomotopyEquiv p₀ p₁ (j₀ ≫ r₁) (j₁ ≫ r₀)
      (FiberwiseHomotopy.symm
        { h := j₀ ▷ _ ≫ k₁.h ≫ r₀
          fac := by
            rw [Category.assoc, Category.assoc, h₃, reassoc_of% h₄,
              whiskerLeft_fst, associator_hom_fst, whiskerRight_fst_assoc,
              whiskerRight_fst_assoc, ← reassoc_of% h₂, reassoc_of% h₁,
              whiskerLeft_fst, associator_hom_fst, whiskerRight_fst_assoc,
              whiskerRight_fst_assoc, sq₀.w_assoc, ι₀_fst, Category.comp_id] })
      { h := j₁ ▷ _ ≫ k₀.h ≫ r₁
        fac := by
          rw [Category.assoc, Category.assoc, h₆, reassoc_of% h₁,
            whiskerLeft_fst, associator_hom_fst, whiskerRight_fst_assoc,
            whiskerRight_fst_assoc, ← reassoc_of% h₅, reassoc_of% h₄,
            whiskerLeft_fst, associator_hom_fst, whiskerRight_fst_assoc,
            whiskerRight_fst_assoc, sq₁.w_assoc, ι₁_fst, Category.comp_id] }
  refine ⟨asIso (j₀ ≫ r₁), ?_⟩
  dsimp
  rw [← cancel_mono ι₁, Category.assoc, Category.assoc, ← sq₁.w, ← reassoc_of% k₁.h₁,
    h₄, ι₁_comp_assoc, sq₀.w_assoc]
  rfl

lemma congr_pullback_of_homotopy
    {E A B E₀ E₁ : SSet.{u}} (p : E ⟶ B) [MinimalFibration p]
    {f₀ f₁ : A ⟶ B} (h : Homotopy f₀ f₁)
    {p₀ : E₀ ⟶ A} {g₀ : E₀ ⟶ E} (sq₀ : IsPullback g₀ p₀ p f₀)
    {p₁ : E₁ ⟶ A} {g₁ : E₁ ⟶ E} (sq₁ : IsPullback g₁ p₁ p f₁) :
    ∃ (e : E₀ ≅ E₁), e.hom ≫ p₁ = p₀ := by
  refine congr_pullback_stdSimplex_one (p := pullback.snd p h.h)
    (j₀ := pullback.lift g₀ (p₀ ≫ ι₀) (by simp [sq₀.w])) ?_
    (j₁ := pullback.lift g₁ (p₁ ≫ ι₁) (by simp [sq₁.w])) ?_
  all_goals
  · exact IsPullback.of_right (by simpa) (by simp) (IsPullback.of_hasPullback p h.h)

open MorphismProperty in
lemma isTrivialBundle_of_stdSimplex
    {E : SSet.{u}} {n : ℕ} (p : E ⟶ Δ[n]) [MinimalFibration p] :
    trivialBundles p := by
  let f := (stdSimplex.deformationRetract.{u} n).r ≫
    (stdSimplex.deformationRetract n).i
  have fac : stdSimplex.isTerminalObj₀.from _ ≫
      SSet.const (stdSimplex.obj₀Equiv.symm 0) = f := by
    simp [f]
  obtain ⟨e, he⟩ := congr_pullback_of_homotopy p
    (stdSimplex.deformationRetract n).homotopy
    (IsPullback.of_hasPullback p f) (IsPullback.id_horiz p)
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk e (Iso.refl _))).1
    (trivialBundles.of_isPullback_of_fac (IsPullback.of_hasPullback p f)
      stdSimplex.isTerminalObj₀ _ _ fac)

end MinimalFibration

end SSet
