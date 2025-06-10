import TopCatModelCategory.SSet.CategoryWithWeakEquivalences
import TopCatModelCategory.SSet.SingularConnected

open CategoryTheory HomotopicalAlgebra Simplicial Opposite Limits

namespace SSet.modelCategoryQuillen

namespace rlp_I

variable {E B : SSet.{0}} {p : E ⟶ B} (hp : I.rlp p)

include hp

lemma surjective_app_0 : Function.Surjective (p.app (op ⦋0⦌)) := by
  intro y
  have := hp _ ⟨0⟩
  have sq : CommSq (boundary.isInitial.to _) ∂Δ[0].ι p (yonedaEquiv.symm y) := ⟨by ext⟩
  exact ⟨yonedaEquiv sq.lift,
    by rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]⟩

noncomputable def lift (b : B _⦋0⦌) : E _⦋0⦌ :=
  (surjective_app_0 hp b).choose

@[simp]
noncomputable def lift_spec (b : B _⦋0⦌) : p.app _ (lift hp b) = b :=
  (surjective_app_0 hp b).choose_spec

lemma congr_π₀_mk (e₀ e₁ : E _⦋0⦌) (s : B _⦋1⦌) (hs₀ : B.δ 1 s = p.app _ e₀)
    (hs₁ : B.δ 0 s = p.app _ e₁) :
    π₀.mk e₀ = π₀.mk e₁ := by
  have := hp _ ⟨1⟩
  have sq : CommSq (boundary₁.desc e₀ e₁) ∂Δ[1].ι p (yonedaEquiv.symm s) := ⟨by
    ext : 1
    · simp [← hs₀, stdSimplex.δ_comp_yonedaEquiv_symm]
    · simp [← hs₁, stdSimplex.δ_comp_yonedaEquiv_symm]⟩
  refine π₀.sound (yonedaEquiv sq.lift) ?_ ?_
  · apply yonedaEquiv.symm.injective
    have := boundary₁.ι₀ ≫= sq.fac_left
    rw [boundary₁.ι₀_ι_assoc, boundary₁.ι₀_desc] at this
    rwa [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  · apply yonedaEquiv.symm.injective
    have := boundary₁.ι₁ ≫= sq.fac_left
    rw [boundary₁.ι₁_ι_assoc, boundary₁.ι₁_desc] at this
    rwa [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]

noncomputable def π₀Inv : π₀ B ⟶ π₀ E :=
  Quot.lift (fun b ↦ π₀.mk (lift hp b)) (by
    rintro b₀ b₁ ⟨s, h₀, h₁⟩
    exact congr_π₀_mk hp (lift hp b₀) (lift hp b₁) s (by simpa) (by simpa))

@[simp]
lemma π₀Inv_mk (b : B _⦋0⦌) : π₀Inv hp (π₀.mk b) = π₀.mk (lift hp b) := rfl

noncomputable def π₀Equiv : π₀ E ≃ π₀ B where
  toFun := mapπ₀ p
  invFun := π₀Inv hp
  left_inv e := by
    obtain ⟨e, rfl⟩ := e.mk_surjective
    simp only [mapπ₀_mk, π₀Inv_mk]
    refine congr_π₀_mk hp (lift hp (p.app _ e)) e (B.σ 0 (p.app _ e)) ?_ ?_
    · have := B.δ_comp_σ_succ_apply (n := 0) (i := 0)
      dsimp at this
      simp [this]
    · have := B.δ_comp_σ_self_apply (n := 0) (i := 0)
      dsimp at this
      simp [this]
  right_inv b := by
    obtain ⟨b, rfl⟩ := b.mk_surjective
    simp

lemma bijective_mapπ₀ : Function.Bijective (mapπ₀ p) := (π₀Equiv hp).bijective

lemma bijective_mapπ₀_toSSet_map_toTop_map :
    Function.Bijective (mapπ₀ (TopCat.toSSet.map (SSet.toTop.map p))) := by
  rw [← Function.Bijective.of_comp_iff (hg := bijective_mapπ₀_sSetTopAdj_unit_app E)]
  convert (bijective_mapπ₀_sSetTopAdj_unit_app B).comp (bijective_mapπ₀ hp)
  ext
  dsimp
  rw [← mapπ₀_comp_apply, ← mapπ₀_comp_apply, Adjunction.unit_naturality]

lemma weakEquivalence : WeakEquivalence p := by
  rw [weakEquivalence_iff, TopCat.modelCategory.weakEquivalence_iff, KanComplex.W_iff]
  refine ⟨bijective_mapπ₀_toSSet_map_toTop_map hp, fun n ↦ ?_⟩
  sorry

end rlp_I

lemma weakEquivalence_iff_of_fibration
    {E B : SSet.{0}} (p : E ⟶ B) [Fibration p] :
    I.rlp p ↔ WeakEquivalence p :=
  ⟨rlp_I.weakEquivalence, sorry⟩

end SSet.modelCategoryQuillen
