import TopCatModelCategory.ModelCategory
import TopCatModelCategory.ModelCategoryTopCat

open HomotopicalAlgebra CategoryTheory Limits

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

open TopCat.modelCategory

namespace modelCategoryQuillen

open MorphismProperty SmallObject

instance (K : Type u) [LinearOrder K] : HasIterationOfShape K SSet.{u} where

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

instance : CategoryWithWeakEquivalences SSet.{0} where
  weakEquivalences :=
    (weakEquivalences TopCat).inverseImage SSet.toTop

lemma weakEquivalences_eq :
    weakEquivalences SSet.{0} =
      (weakEquivalences TopCat).inverseImage SSet.toTop := rfl

lemma weakEquivalence_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (toTop.map f) := by
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

instance : (weakEquivalences SSet).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (weakEquivalences SSet).IsStableUnderRetracts := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (cofibrations SSet).IsStableUnderRetracts := by
  rw [cofibrations_eq]
  infer_instance

instance : (fibrations SSet).IsStableUnderRetracts := by
  rw [fibrations_eq]
  infer_instance

instance : toTop.IsLeftAdjoint := ⟨_, ⟨sSetTopAdj⟩⟩

instance (K : Type) [LinearOrder K] : PreservesWellOrderContinuousOfShape K toTop where

lemma J_inverseImage_trivialCofibrations :
    J ≤ (trivialCofibrations TopCat).inverseImage toTop := by
  intro _ _ f hf
  simp only [J, iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  rw [TopCat.modelCategory.trivialCofibrations_eq_llp_rlp]
  apply le_llp_rlp
  simp only [iSup_iff]
  exact ⟨n, ⟨i⟩⟩

instance : HasFunctorialFactorization (trivialCofibrations SSet) (fibrations SSet) := by
  refine MorphismProperty.hasFunctorialFactorization_of_le (W₁ := J.rlp.llp)
    (W₂ := J.rlp) ?_ (by rfl)
  rw [trivialCofibrations, le_inf_iff,
    llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0]
  constructor
  · simpa [cofibrations_eq] using J_le_monomorphisms
  · trans (trivialCofibrations TopCat).inverseImage SSet.toTop
    · simp only [retracts_le_iff]
      rintro _ _ f hf
      rw [transfiniteCompositions_iff] at hf
      obtain ⟨K, _, _, _, _, ⟨hf⟩⟩ := hf
      have : (coproducts.{0} J.{0}).pushouts ≤
          (trivialCofibrations TopCat).inverseImage toTop := by
        rintro _ _ r ⟨_, _, l, t, b, hl, sq⟩
        simp only [inverseImage_iff]
        apply MorphismProperty.of_isPushout (sq.map toTop)
        apply coproducts_le.{0}
        rw [coproducts_iff] at hl ⊢
        obtain ⟨K, X₁, X₂, c₁, c₂, hc₁, hc₂, g, hg⟩ := hl
        let c₁' := toTop.mapCocone c₁
        let c₂' := toTop.mapCocone c₂
        let hc₁' : IsColimit c₁' := isColimitOfPreserves toTop hc₁
        let hc₂' : IsColimit c₂' := isColimitOfPreserves toTop hc₂
        have : hc₁'.desc { ι := whiskerRight g toTop ≫ c₂'.ι } =
          toTop.map (hc₁.desc { ι := g ≫ c₂.ι }) := by
            apply hc₁'.hom_ext
            rintro ⟨j⟩
            rw [IsColimit.fac]
            dsimp [c₁']
            rw [← Functor.map_comp, IsColimit.fac]
            dsimp
            rw [Functor.map_comp]
            rfl
        rw [← this]
        exact ⟨K, _, _, _, _, hc₁', hc₂', _,
          fun ⟨j⟩ ↦ J_inverseImage_trivialCofibrations _ (hg ⟨j⟩)⟩
      simp only [inverseImage_iff]
      exact transfiniteCompositionsOfShape_le _ _ _ ((hf.ofLE this).map.mem)
    · rintro _ _ f ⟨_, hf⟩
      exact hf

end modelCategoryQuillen

end SSet
