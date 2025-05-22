import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.HomotopySequenceAction
import TopCatModelCategory.LiftingProperties

universe u

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  MonoidalCategory MonoidalClosed Simplicial Limits ChosenFiniteProducts

namespace SSet

namespace ihomToPullback

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}

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

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
  {t : A ⊗ Δ[1] ⟶ X} {b : B ⊗ Δ[1] ⟶ Y} (sq : CommSq t (i ▷ Δ[1]) p b)
  {t₀ t₁ : A ⟶ X} (ht₀ : ι₀ ≫ t = t₀) (ht₁ : ι₁ ≫ t = t₁)
  {b₀ b₁ : B ⟶ Y} (hb₀ : ι₀ ≫ b = b₀) (hb₁ : ι₁ ≫ b = b₁)

include sq ht₀ hb₀ in
lemma commSq₀_of_deformation : CommSq t₀ i p b₀ :=
  ⟨by rw [← ht₀, ← hb₀, Category.assoc, sq.w, ι₀_comp_assoc]⟩

include sq ht₁ hb₁ in
lemma commSq₁_of_deformation : CommSq t₁ i p b₁ :=
  ⟨by rw [← ht₁, ← hb₁, Category.assoc, sq.w, ι₁_comp_assoc]⟩

lemma hasLift_iff_of_deformation [Mono i] [Fibration p] :
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

section

variable {B X Y : SSet.{u}} {A : B.Subcomplex} {p : X ⟶ Y}
variable (t : (A : SSet) ⊗ Δ[1] ⟶ X) {t₀ t₁ : (A : SSet) ⟶ X}
  (ht₀ : ι₀ ≫ t = t₀) (ht₁ : ι₁ ≫ t = t₁)

include t ht₀ ht₁ in
lemma hasLiftingPropertyFixedTop_iff_of_deformation [IsFibrant Y] [Fibration p] :
    HasLiftingPropertyFixedTop A.ι p t₀ ↔
      HasLiftingPropertyFixedTop A.ι p t₁ := by
  constructor
  · intro h₀ b₁ sq₁
    obtain ⟨φ, hφ₁, hφ₂⟩ := (Subcomplex.unionProd.isPushout A (horn 1 1)).exists_desc
      (B ◁ (horn₁.iso 1).inv ≫ (stdSimplex.rightUnitor _).hom ≫ b₁) (t ≫ p) (by
        rw [horn₁.whiskerLeft_iso₁_inv_comp_rightUnitor_hom_assoc,
          whiskerRight_fst_assoc, ← sq₁.w, ← ht₁, Category.assoc,
          ← cancel_epi (_ ◁ (horn₁.iso 1).hom), whiskerLeft_fst_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          horn₁.iso₁_hom_ι, ← stdSimplex.rightUnitor_hom_ι₁, Category.assoc,
          stdSimplex.rightUnitor])
    obtain ⟨b, hb⟩ := anodyneExtensions.exists_lift_of_isFibrant φ
      (anodyneExtensions.subcomplex_unionProd_mem_of_right A _ (.horn_ι_mem 0 1))
    have sq : CommSq t (A.ι ▷ Δ[1]) p b := ⟨by aesop⟩
    rw [← hasLift_iff_of_deformation sq ht₀ ht₁ (b₁ := b₁) rfl (by
      rw [← cancel_epi (B ◁ (horn₁.iso 1).inv ≫ (stdSimplex.rightUnitor B).hom),
        Category.assoc, Category.assoc, ← hφ₁, ← hb,
        stdSimplex.rightUnitor_hom_ι₁_assoc,
        Subcomplex.unionProd.ι₁_ι_assoc,
        ← horn₁.iso₁_hom_ι, ← MonoidalCategory.whiskerLeft_comp_assoc,
        Iso.inv_hom_id_assoc])]
    apply h₀
  · intro h₁ b₀ sq₀
    obtain ⟨φ, hφ₁, hφ₂⟩ := (Subcomplex.unionProd.isPushout A (horn 1 0)).exists_desc
      (B ◁ (horn₁.iso 0).inv ≫ (stdSimplex.rightUnitor _).hom ≫ b₀) (t ≫ p) (by
        rw [horn₁.whiskerLeft_iso₀_inv_comp_rightUnitor_hom_assoc,
          whiskerRight_fst_assoc, ← sq₀.w, ← ht₀, Category.assoc,
          ← cancel_epi (_ ◁ (horn₁.iso 0).hom), whiskerLeft_fst_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          horn₁.iso₀_hom_ι, ← stdSimplex.rightUnitor_hom_ι₀, Category.assoc,
          stdSimplex.rightUnitor])
    obtain ⟨b, hb⟩ := anodyneExtensions.exists_lift_of_isFibrant φ
      (anodyneExtensions.subcomplex_unionProd_mem_of_right A _ (.horn_ι_mem 0 0))
    have sq : CommSq t (A.ι ▷ Δ[1]) p b := ⟨by aesop⟩
    rw [hasLift_iff_of_deformation sq ht₀ ht₁ (b₀ := b₀) (by
      rw [← cancel_epi (B ◁ (horn₁.iso 0).inv ≫ (stdSimplex.rightUnitor B).hom),
        Category.assoc, Category.assoc, ← hφ₁, ← hb,
        stdSimplex.rightUnitor_hom_ι₀_assoc,
        Subcomplex.unionProd.ι₁_ι_assoc,
        ← horn₁.iso₀_hom_ι, ← MonoidalCategory.whiskerLeft_comp_assoc,
        Iso.inv_hom_id_assoc]) rfl]
    apply h₁

end

end SSet
