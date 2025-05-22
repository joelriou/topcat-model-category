import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.HomotopySequenceAction

universe u

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  MonoidalCategory MonoidalClosed Simplicial Limits

namespace SSet

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}

namespace ihomToPullback

lemma hasLift_iff_fiber_neq_bot {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    sq.HasLift ↔ Subcomplex.fiber (ihomToPullback i p) (ihomToPullbackTgt₀Mk sq) ≠ ⊥ := by
  rw [Subcomplex.neq_bot_iff]
  constructor
  · intro
    use ihom₀Equiv.symm sq.lift
    simp [ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff]
  · intro ⟨f, h⟩
    obtain ⟨f, rfl⟩ := ihom₀Equiv.symm.surjective f
    simp only [ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff] at h
    exact ⟨⟨{ l := f }⟩⟩

end ihomToPullback

section
variable
  {t : A ⊗ Δ[1] ⟶ X} {b : B ⊗ Δ[1] ⟶ Y} (sq : CommSq t (i ▷ Δ[1]) p b)
    {t₀ t₁ : A ⟶ X} (ht₀ : ι₀ ≫ t = t₀) (ht₁ : ι₁ ≫ t = t₁)
    {b₀ b₁ : B ⟶ Y} (hb₀ : ι₀ ≫ b = b₀) (hb₁ : ι₁ ≫ b = b₁)

include sq ht₀ hb₀ in
lemma commSq₀_of_deformation : CommSq t₀ i p b₀ :=
  ⟨by rw [← ht₀, ← hb₀, Category.assoc, sq.w, ι₀_comp_assoc]⟩

include sq ht₁ hb₁ in
lemma commSq₁_of_deformation : CommSq t₁ i p b₁ :=
  ⟨by rw [← ht₁, ← hb₁, Category.assoc, sq.w, ι₁_comp_assoc]⟩

lemma hasLift_iff_of_deformation [Mono i] [Fibration p]
    {t : A ⊗ Δ[1] ⟶ X} {b : B ⊗ Δ[1] ⟶ Y} (sq : CommSq t (i ▷ Δ[1]) p b)
    {t₀ t₁ : A ⟶ X} (ht₀ : ι₀ ≫ t = t₀) (ht₁ : ι₁ ≫ t = t₁)
    {b₀ b₁ : B ⟶ Y} (hb₀ : ι₀ ≫ b = b₀) (hb₁ : ι₁ ≫ b = b₁) :
    (commSq₀_of_deformation sq ht₀ hb₀).HasLift ↔
      (commSq₁_of_deformation sq ht₁ hb₁).HasLift := by
  simp only [ihomToPullback.hasLift_iff_fiber_neq_bot]
  apply Subcomplex.fiber_neq_bot_iff_of_edge
  let e : Δ[1] ⟶ pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) :=
    pullback.lift (curry t) (curry b) (by
      rw [← curry_natural_right, curry_pre_app, sq.w])
  refine .mk (pullback.lift (curry t) (curry b) (by
      rw [← curry_natural_right, curry_pre_app, sq.w])) ?_ ?_
  · ext : 1
    · dsimp
      rw [Category.assoc, pullback.lift_fst,
        const_comp, pullback_fst_app_ihomToPullbackTgt₀Mk,
        ← curry_natural_left, const_ihom₀Equiv_symm_apply, ← ht₀,
        ← stdSimplex.rightUnitor_inv_map_δ_one, Category.assoc,
        stdSimplex.fst_rightUnitor_inv_assoc]
    · dsimp
      rw [Category.assoc, pullback.lift_snd,
        const_comp, pullback_snd_app_ihomToPullbackTgt₀Mk,
        ← curry_natural_left, const_ihom₀Equiv_symm_apply, ← hb₀,
        ← stdSimplex.rightUnitor_inv_map_δ_one, Category.assoc,
        stdSimplex.fst_rightUnitor_inv_assoc]
  · ext : 1
    · dsimp
      rw [Category.assoc, pullback.lift_fst,
        const_comp, pullback_fst_app_ihomToPullbackTgt₀Mk,
        ← curry_natural_left, const_ihom₀Equiv_symm_apply, ← ht₁,
        ← stdSimplex.rightUnitor_inv_map_δ_zero, Category.assoc,
        stdSimplex.fst_rightUnitor_inv_assoc]
    · dsimp
      rw [Category.assoc, pullback.lift_snd,
        const_comp, pullback_snd_app_ihomToPullbackTgt₀Mk,
        ← curry_natural_left, const_ihom₀Equiv_symm_apply, ← hb₁,
        ← stdSimplex.rightUnitor_inv_map_δ_zero, Category.assoc,
        stdSimplex.fst_rightUnitor_inv_assoc]

end

end SSet
