import TopCatModelCategory.SSet.KeyLemma

open HomotopicalAlgebra CategoryTheory Limits

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

open TopCat.modelCategory

namespace modelCategoryQuillen

open MorphismProperty SmallObject

lemma rlp_I_eq_trivialFibrations :
    I.rlp = trivialFibrations SSet := by
  ext X Y f
  rw [mem_trivialFibrations_iff]
  constructor
  · intro hf
    obtain : Fibration f := by simpa only [fibration_iff] using rlp_I_le_rlp_J _ hf
    exact ⟨inferInstance, by rwa [← weakEquivalence_iff_of_fibration]⟩
  · rintro ⟨_, _⟩
    rwa [weakEquivalence_iff_of_fibration]

instance : HasFunctorialFactorization (cofibrations SSet) (trivialFibrations SSet) := by
  refine MorphismProperty.hasFunctorialFactorization_of_le (W₁ := I.rlp.llp) (W₂ := I.rlp) ?_
    (by rw [rlp_I_eq_trivialFibrations])
  rw [llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0, cofibrations_eq,
    transfiniteCompositions_pushouts_coproducts]
  apply retracts_le

instance {A B X Y : SSet.{0}} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [hp : WeakEquivalence p] :
    HasLiftingProperty i p := by
  have : I.rlp p := by
    rw [rlp_I_eq_trivialFibrations]
    exact mem_trivialFibrations p
  rw [I_rlp_eq_monomorphisms_rlp] at this
  exact this _ (.infer_property _)

end modelCategoryQuillen

open modelCategoryQuillen

instance : ModelCategory SSet.{0} where
  cm4a i p _ _ _ := ModelCategory.joyal_trick_dual
    (by intros; infer_instance) _ _

end SSet
