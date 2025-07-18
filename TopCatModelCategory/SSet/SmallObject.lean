import TopCatModelCategory.MorphismProperty
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.Presentable
import TopCatModelCategory.SSet.Skeleton
import Mathlib.CategoryTheory.SmallObject.Basic

open HomotopicalAlgebra CategoryTheory Limits

universe v' u' u

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace modelCategoryQuillen

open MorphismProperty SmallObject

instance (K : Type u) [LinearOrder K] : HasIterationOfShape K SSet.{u} where

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

instance (J : Type u) [SmallCategory J] [IsFiltered J] (X : SSet.{u}) [X.IsFinite] :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X)) := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := by
    rwa [isCardinalFiltered_aleph0_iff]
  exact preservesColimitsOfShape_of_isCardinalPresentable _ (Cardinal.aleph0.{u}) _

instance (J : Type u') [Category.{v'} J] [IsFiltered J]
    [Small.{u} J] [LocallySmall.{u} J] (X : SSet.{u}) [X.IsFinite] :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X)) := by
  have e := (Shrink.equivalence.{u} J).trans (ShrinkHoms.equivalence.{u} (Shrink.{u} J))
  have := IsFiltered.of_equivalence e
  exact preservesColimitsOfShape_of_equiv e.symm _

instance isCardinalForSmallObjectArgument_I :
    I.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    obtain ⟨n⟩ := hi
    infer_instance
  isSmall := by
    dsimp [I]
    infer_instance

instance isCardinalForSmallObjectArgument_J :
    J.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    simp only [J, iSup_iff] at hi
    obtain ⟨n, ⟨i⟩⟩ := hi
    infer_instance
  isSmall := by
    dsimp [J]
    infer_instance

instance : HasSmallObjectArgument.{u} I.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{u} J.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

lemma rlp_I_le_rlp_J : I.{u}.rlp ≤ J.{u}.rlp := by
  rw [← le_llp_iff_le_rlp, llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0,
    transfiniteCompositions_pushouts_coproducts]
  exact J_le_monomorphisms.trans (le_retracts _)

lemma llp_rlp_I : I.rlp.llp = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [llp_rlp_of_isCardinalForSmallObjectArgument _ .aleph0]
    simpa using I_le_monomorphisms
  · rw [I_rlp_eq_monomorphisms_rlp]
    apply le_llp_rlp

instance : HasFunctorialFactorization (monomorphisms (SSet.{u})) I.rlp where
  nonempty_functorialFactorizationData := ⟨
    (functorialFactorizationData I.{u}.rlp.llp I.rlp).ofLE (by rw [llp_rlp_I]) (by rfl)⟩

end modelCategoryQuillen

end SSet
