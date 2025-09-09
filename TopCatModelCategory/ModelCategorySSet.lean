import TopCatModelCategory.SSet.KeyLemma
import TopCatModelCategory.QuillenAdjunction

universe u

open HomotopicalAlgebra CategoryTheory Limits

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

open TopCat.modelCategory

namespace modelCategoryQuillen

open MorphismProperty SmallObject

lemma rlp_I_eq_trivialFibrations :
    I.rlp = trivialFibrations SSet.{u} := by
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

instance {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [hp : WeakEquivalence p] :
    HasLiftingProperty i p := by
  have : I.rlp p := by
    rw [rlp_I_eq_trivialFibrations]
    exact mem_trivialFibrations p
  rw [I_rlp_eq_monomorphisms_rlp] at this
  exact this _ (.infer_property _)

end modelCategoryQuillen

open modelCategoryQuillen

instance : ModelCategory SSet.{u} where
  cm4a i p _ _ _ := ModelCategory.joyal_trick_dual
    (by intros; infer_instance) _ _

instance (X : SSet.{u}) : IsCofibrant X := by
  rw [isCofibrant_iff_of_isInitial (Subcomplex.ι _) (Subcomplex.isInitialBot X),
    cofibration_iff]
  infer_instance

lemma weakEquivalence_toSSet_map_toTop_map_iff {X Y : SSet.{u}}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    KanComplex.W (TopCat.toSSet.map (toTop.map f)) ↔ KanComplex.W f := by
  have := sSetTopAdj.unit.naturality f
  dsimp at this
  rw [← KanComplex.W.postcomp_iff _ _ (KanComplex.W.sSetTopAdj_unit_app Y), this,
    KanComplex.W.precomp_iff _ _ (KanComplex.W.sSetTopAdj_unit_app X)]

lemma weakEquivalence_iff_kanComplexW {X Y : SSet.{u}}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔ KanComplex.W f := by
  rw [← weakEquivalence_toSSet_map_toTop_map_iff, modelCategoryQuillen.weakEquivalence_iff,
    TopCat.modelCategory.weakEquivalence_iff]

lemma _root_.TopCat.weakEquivalence_toSSet_map_iff {E B : TopCat} (p : E ⟶ B) :
    WeakEquivalence (TopCat.toSSet.map p) ↔ WeakEquivalence p := by
  simp only [modelCategoryQuillen.weakEquivalence_iff,
    TopCat.modelCategory.weakEquivalence_iff,
    weakEquivalence_toSSet_map_toTop_map_iff]

instance {X Y : TopCat.{u}} (p : X ⟶ Y) [WeakEquivalence p] :
    WeakEquivalence (TopCat.toSSet.map p) := by
  rwa [TopCat.weakEquivalence_toSSet_map_iff]

instance : sSetTopAdj.{u}.IsQuillenAdjunction where
  toPreservesCofibrations := by
    rw [← sSetTopAdj.preservesTrivialFibrations_iff_preservesCofibrations]
    constructor
    intro X Y p hp
    simp only [MorphismProperty.inverseImage_iff, mem_trivialFibrations_iff] at hp ⊢
    obtain ⟨_, _⟩ := hp
    constructor <;> infer_instance

instance (X : SSet.{u}) [IsFibrant X] : WeakEquivalence (sSetTopAdj.unit.app X) := by
  rw [weakEquivalence_iff_kanComplexW]
  apply KanComplex.W.sSetTopAdj_unit_app

instance (X : TopCat.{u}) : WeakEquivalence (sSetTopAdj.counit.app X) := by
  rw [← TopCat.weakEquivalence_toSSet_map_iff,
    ← weakEquivalence_precomp_iff (sSetTopAdj.unit.app (TopCat.toSSet.obj X)),
    sSetTopAdj.right_triangle_components X]
  dsimp
  infer_instance

instance (X : SSet.{u}) : WeakEquivalence (sSetTopAdj.unit.app X) := by
  rw [modelCategoryQuillen.weakEquivalence_iff,
    ← weakEquivalence_postcomp_iff _ (sSetTopAdj.counit.app (toTop.obj X)),
    sSetTopAdj.left_triangle_components X]
  dsimp
  infer_instance

end SSet
