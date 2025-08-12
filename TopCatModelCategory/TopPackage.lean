import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import TopCatModelCategory.AlephZero
import TopCatModelCategory.JoyalTrickDual
import TopCatModelCategory.Factorization
import TopCatModelCategory.ModelCategoryCopy
import TopCatModelCategory.CellComplex

open CategoryTheory Limits MorphismProperty

universe w v u

namespace HomotopicalAlgebra

variable (T : Type u) [Category.{v} T]

variable [CategoryWithWeakEquivalences T]

structure TopPackage where
  /-- generation cofibrations -/
  I' : MorphismProperty T
  /-- generation trivial cofibrations -/
  J' : MorphismProperty T
  /-- "finite cell complexes" -/
  S' : Set T
  -- basic instances
  hasFiniteLimits : HasFiniteLimits T := by infer_instance
  hasColimitsOfSize : HasColimitsOfSize.{w, w} T := by infer_instance
  locallySmall : LocallySmall.{w} T := by infer_instance
  isSmall_I' : IsSmall.{w} I' := by infer_instance
  isSmall_J' : IsSmall.{w} J' := by infer_instance
  -- axioms
  hasTwoOutOfThreeProperty : (weakEquivalences T).HasTwoOutOfThreeProperty := by infer_instance
  isStableUnderRetracts : (weakEquivalences T).IsStableUnderRetracts := by infer_instance
  rlp_I'_le_rlp_J' : I'.rlp ≤ J'.rlp
  fibration_is_trivial_iff' {X Y : T} (p : X ⟶ Y) (hp : J'.rlp p) :
    I'.rlp p ↔ WeakEquivalence p
  src_I_le_S' {A B : T} (i : A ⟶ B) (hi : I' i) : A ∈ S'
  src_J_le_S' {A B : T} (i : A ⟶ B) (hj : J' i) : A ∈ S'
  infiniteCompositions_le_W' :
    (coproducts.{w} J').pushouts.transfiniteCompositionsOfShape ℕ ≤ weakEquivalences T
  preservesColimit' (X : T) (hX : X ∈ S') {A B : T} (f : A ⟶ B)
    (hf : RelativeCellComplex.{w} (fun (_ : ℕ) ↦ (I' ⊔ J').homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op X))

namespace TopPackage

variable {T}

def Cat (_ : TopPackage.{w} T) : Type u := T

variable (π : TopPackage.{w} T)

instance : Category π.Cat := inferInstanceAs (Category T)

def I : MorphismProperty π.Cat := π.I'
def J : MorphismProperty π.Cat := π.J'

instance : LocallySmall.{w} π.Cat := π.locallySmall

instance : HasFiniteLimits π.Cat := π.hasFiniteLimits

instance : HasColimitsOfSize.{w, w} π.Cat := π.hasColimitsOfSize

instance (J : Type w) [LinearOrder J] : HasIterationOfShape J π.Cat where

instance : HasFiniteColimits π.Cat :=
  hasFiniteColimits_of_hasColimitsOfSize π.Cat

instance : CategoryWithWeakEquivalences π.Cat :=
  inferInstanceAs (CategoryWithWeakEquivalences T)

instance : CategoryWithFibrations π.Cat where
  fibrations := π.J.rlp

instance : CategoryWithCofibrations π.Cat where
  cofibrations := π.I.rlp.llp

lemma fibrations_eq : fibrations π.Cat = π.J.rlp := rfl
lemma cofibrations_eq : cofibrations π.Cat = π.I.rlp.llp := rfl

instance : (weakEquivalences π.Cat).HasTwoOutOfThreeProperty :=
  π.hasTwoOutOfThreeProperty

instance : (weakEquivalences π.Cat).IsStableUnderRetracts :=
  π.isStableUnderRetracts

instance : (fibrations π.Cat).IsStableUnderRetracts := by
  apply rlp_isStableUnderRetracts

instance : (cofibrations π.Cat).IsStableUnderRetracts := by
  apply llp_isStableUnderRetracts

instance : IsSmall.{w} π.I := π.isSmall_I'
instance : IsSmall.{w} π.J := π.isSmall_J'

def S : Set π.Cat := π.S'

lemma src_I_le_S {A B : T} (i : A ⟶ B) (hi : π.I i) : A ∈ π.S :=
  π.src_I_le_S' i hi

lemma src_J_le_S {A B : T} (j : A ⟶ B) (hj : π.J j) : A ∈ π.S :=
  π.src_J_le_S' j hj

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

lemma preservesColimit (X : π.Cat) (hX : X ∈ π.S) {A B : T} (f : A ⟶ B)
    (hf : RelativeCellComplex.{w}
      (fun (_ : Cardinal.aleph0.{w}.ord.toType) ↦ (π.I ⊔ π.J).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op X)) := by
  let hf' := hf.ofOrderIso Cardinal.aleph0OrdToTypeOrderIso.{w}.symm
  have := π.preservesColimit' X hX f hf'
  let e := Cardinal.aleph0OrdToTypeOrderIso.{w}.equivalence
  have : hf.F ≅ e.functor ⋙ hf'.F :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso hf.F ≪≫
      Functor.associator _ _ _
  apply preservesColimit_of_iso_diagram _ this.symm

instance isCardinalForSmallObjectArgument_I :
    π.I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w} where
  hasIterationOfShape := by infer_instance
  preservesColimit {X _ A B} _ h f hf :=
    π.preservesColimit X (π.src_I_le_S _ h) f
        { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
          attachCells j hj := (hf.attachCells j hj).reindexCellTypes _
              (fun ⟨x, hx⟩ ↦ ⟨x, Or.inl hx⟩) (fun _ ↦ Iso.refl _) }

instance isCardinalForSmallObjectArgument_J :
    π.J.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w} where
  hasIterationOfShape := by infer_instance
  preservesColimit {X _ A B} _ h f hf :=
    π.preservesColimit X (π.src_J_le_S _ h) f
        { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
          attachCells j hj := (hf.attachCells j hj).reindexCellTypes _
              (fun ⟨x, hx⟩ ↦ ⟨x, Or.inr hx⟩) (fun _ ↦ Iso.refl _) }

instance : HasSmallObjectArgument.{w} π.I where
  exists_cardinal := ⟨Cardinal.aleph0.{w}, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{w} π.J where
  exists_cardinal := ⟨Cardinal.aleph0.{w}, inferInstance, inferInstance, inferInstance⟩

lemma rlp_I_le_rlp_J : π.I.rlp ≤ π.J.rlp :=
  π.rlp_I'_le_rlp_J'

lemma J_rlp_llp_le_cofibrations : π.J.rlp.llp ≤ cofibrations π.Cat :=
  antitone_llp π.rlp_I_le_rlp_J

lemma infiniteCompositions_le_weakEquivalences :
    (coproducts.{w} π.J).pushouts.transfiniteCompositionsOfShape ℕ ≤
      weakEquivalences π.Cat := π.infiniteCompositions_le_W'

lemma transfiniteCompositionsOfShape_aleph0_le_weakEquivalences :
    (coproducts.{w} π.J).pushouts.transfiniteCompositionsOfShape
      Cardinal.aleph0.{w}.ord.toType ≤ weakEquivalences π.Cat := by
  rw [transfiniteCompositionsOfShape_eq_of_orderIso _
    Cardinal.aleph0OrdToTypeOrderIso.{w}]
  exact π.infiniteCompositions_le_weakEquivalences

lemma J_rlp_llp_le_weakEquivalences : π.J.rlp.llp ≤ weakEquivalences π.Cat := by
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' π.J Cardinal.aleph0.{w}]
  exact (retracts_monotone π.transfiniteCompositionsOfShape_aleph0_le_weakEquivalences).trans
    (MorphismProperty.retracts_le _)

lemma J_rlp_llp_le_trivialCofibrations : π.J.rlp.llp ≤ trivialCofibrations π.Cat := by
  simp only [trivialCofibrations, le_inf_iff]
  constructor
  · apply J_rlp_llp_le_cofibrations
  · apply J_rlp_llp_le_weakEquivalences

instance : (trivialCofibrations π.Cat).HasFunctorialFactorization (fibrations π.Cat) :=
  MorphismProperty.hasFunctorialFactorization_of_le (W₂ := π.J.rlp)
    (π.J_rlp_llp_le_trivialCofibrations) (by rfl)

lemma I_rlp_iff_weakEquivalence_of_fibration {X Y : π.Cat} (p : X ⟶ Y) [hp : Fibration p] :
    π.I.rlp p ↔ WeakEquivalence p := by
  rw [fibration_iff] at hp
  exact π.fibration_is_trivial_iff' p hp

lemma I_rlp_eq_trivialFibrations : π.I.rlp = trivialFibrations π.Cat := by
  ext X Y p
  rw [mem_trivialFibrations_iff]
  constructor
  · intro hp
    have hp' := π.rlp_I_le_rlp_J _ hp
    rw [← fibrations_eq, ← fibration_iff] at hp'
    rw [π.I_rlp_iff_weakEquivalence_of_fibration] at hp
    exact ⟨hp', hp⟩
  · rintro ⟨hp', hp⟩
    rwa [π.I_rlp_iff_weakEquivalence_of_fibration]

instance : (cofibrations π.Cat).HasFunctorialFactorization (trivialFibrations π.Cat) :=
  MorphismProperty.hasFunctorialFactorization_of_le (W₁ := π.I.rlp.llp) (W₂ := π.I.rlp)
    (by rfl) (by rw [I_rlp_eq_trivialFibrations])

instance {A B X Y : π.Cat} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence p] [Fibration p] : HasLiftingProperty i p := by
  have hi := mem_cofibrations i
  have hp := mem_trivialFibrations p
  rw [cofibrations_eq] at hi
  rw [← π.I_rlp_eq_trivialFibrations] at hp
  exact hi p hp

instance : (fibrations π.Cat).IsStableUnderComposition := by
  rw [fibrations_eq]
  infer_instance

instance : (fibrations π.Cat).IsStableUnderBaseChange := by
  rw [fibrations_eq]
  infer_instance

instance {A B X Y : π.Cat} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] : HasLiftingProperty i p := by
  apply ModelCategory.joyal_trick_dual
  intros
  infer_instance

instance modelCategoryCat : ModelCategory π.Cat where

lemma cofibrations_eq_llp_rlp_I :
    cofibrations π.Cat = π.I.rlp.llp := by
  rw [I_rlp_eq_trivialFibrations, trivialFibrations_llp]

lemma trivialCofibrations_eq_llp_rlp_J :
    trivialCofibrations π.Cat = π.J.rlp.llp := by
  rw [← fibrations_eq, fibrations_llp π.Cat]

def modelCategory
    [CategoryWithCofibrations T] [CategoryWithFibrations T]
    (h₁ : cofibrations T = π.I.rlp.llp)
    (h₂ : fibrations T = π.J.rlp) : ModelCategory T :=
  ModelCategory.copy π.modelCategoryCat h₁ h₂ rfl

end TopPackage

end HomotopicalAlgebra
