import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.ULift
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

universe w v u

open CategoryTheory MorphismProperty Limits HomotopicalAlgebra

namespace CategoryTheory

namespace Types

instance : IsStableUnderCoproducts.{v} (monomorphisms (Type u)) where
  isStableUnderCoproductsOfShape J  := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    simp only [monomorphisms.iff, mono_iff_injective] at hf ⊢
    intro x y h
    obtain ⟨⟨i⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit (coproductIsCoproduct X₁) x
    obtain ⟨⟨j⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit (coproductIsCoproduct X₁) y
    dsimp at x y h ⊢
    change (Sigma.ι X₁ i ≫ Limits.Sigma.map f) x =
      (Sigma.ι X₁ j ≫ Limits.Sigma.map f) y at h
    simp only [ι_colimMap] at h
    dsimp at h
    obtain rfl := Types.eq_cofanInj_apply_eq_of_isColimit (coproductIsCoproduct X₂) _ _ h
    obtain rfl := hf _ (Types.cofanInj_injective_of_isColimit (coproductIsCoproduct X₂) _ h)
    rfl

instance [HasCoproducts.{v} (Type u)] (J : Type*) [Category J] :
    IsStableUnderCoproducts.{v} (monomorphisms (J ⥤ Type u)) where
  isStableUnderCoproductsOfShape J := by
    rw [← functorCategory_monomorphisms]
    apply IsStableUnderColimitsOfShape.functorCategory
    apply isStableUnderCoproductsOfShape_of_isStableUnderCoproducts

end Types

end CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

@[simp]
lemma rlp_transfiniteCompositions (W : MorphismProperty C) :
    (transfiniteCompositions.{w} W).rlp = W.rlp := by
  apply le_antisymm
  · exact antitone_rlp W.le_transfiniteCompositions
  · rw [← le_llp_iff_le_rlp]
    exact transfiniteCompositions_le_llp_rlp W

instance [(monomorphisms C).IsStableUnderCobaseChange] [HasPushouts C]
    [HasPullbacks C] (J : Type*) [Category J] :
    (monomorphisms (J ⥤ C)).IsStableUnderCobaseChange := by
  rw [← functorCategory_monomorphisms]
  infer_instance

end CategoryTheory.MorphismProperty

namespace SSet

instance : IsStableUnderTransfiniteComposition.{u} (monomorphisms (SSet.{u})) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderTransfiniteCompositionOfShape _
    infer_instance

instance : IsStableUnderCobaseChange (monomorphisms (SSet.{u})) :=
  inferInstanceAs (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange

instance : IsStableUnderCoproducts.{u} (monomorphisms (SSet.{u})) :=
  inferInstanceAs (IsStableUnderCoproducts.{u} (monomorphisms (_ ⥤ _)))

namespace modelCategoryQuillen

def relativeCellComplexOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{u} (basicCell := fun (n : ℕ) (_ : Unit) ↦ (boundary n).ι) i := by
  sorry

def transfiniteCompositionOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    (coproducts.{u} I).pushouts.TransfiniteCompositionOfShape ℕ i where
  toTransfiniteCompositionOfShape :=
    (relativeCellComplexOfMono i).toTransfiniteCompositionOfShape
  map_mem d hd := by
    apply pushouts_monotone _ _
      ((relativeCellComplexOfMono i).attachCells d hd).pushouts_coproducts
    apply coproducts_monotone
    rintro _ _ _ ⟨⟩
    exact boundary_ι_mem_I d

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} (coproducts.{u} I).pushouts = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · intro _ _ i (_ : Mono i)
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions _ (ULift ℕ)
    exact ⟨(transfiniteCompositionOfMono i).ofOrderIso (orderIsoULift.{u} ℕ).symm⟩

lemma I_rlp_eq_monomorphisms_rlp : I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by
  apply le_antisymm
  · simp only [← transfiniteCompositions_pushouts_coproducts,
      rlp_transfiniteCompositions, rlp_pushouts, rlp_coproducts, le_refl]
  · exact MorphismProperty.antitone_rlp I_le_monomorphisms

end modelCategoryQuillen

end SSet
