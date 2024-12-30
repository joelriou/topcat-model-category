import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import TopcatModelCategory.Factorization
import TopcatModelCategory.MorphismProperty

open CategoryTheory Limits MorphismProperty

universe w v u

namespace HomotopicalAlgebra

variable (T : Type u) [Category.{v} T]

structure TopPackage where
  -- data
  W : MorphismProperty T
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
  hasTwoOutOfThreeProperty : W.HasTwoOutOfThreeProperty := by infer_instance
  isStableUnderRetracts : W.IsStableUnderRetracts := by infer_instance
  J_le_I' : J' ≤ I'
  fibration_is_trivial_iff' {X Y : T} (p : X ⟶ Y) (hp : J'.rlp p) :
    I'.rlp p ↔ W p
  src_I_le_S' {A B : T} (i : A ⟶ B) (hi : I' i) : A ∈ S'
  preservesColimit' (X : T) (hX : X ∈ S') (F : ℕ ⥤ T)
    (hF : ∀ (n : ℕ), (coproducts.{w} I').pushouts (F.map (homOfLE n.le_succ))) :
    PreservesColimit F (coyoneda.obj (Opposite.op X))
  infiniteCompositions_le_W' :
    (coproducts.{w} J').pushouts.transfiniteCompositionsOfShape ℕ ≤ W'

namespace TopPackage

variable {T}

def Cat (_ : TopPackage.{w} T) : Type u := T

variable (π : TopPackage.{w} T)

instance : Category π.Cat := inferInstanceAs (Category T)

def I : MorphismProperty π.Cat := π.I'
def J : MorphismProperty π.Cat := π.J'

lemma J_le_I : π.J ≤ π.I := π.J_le_I'

instance : LocallySmall.{w} π.Cat := π.locallySmall

instance : HasFiniteLimits π.Cat := π.hasFiniteLimits

instance : HasColimitsOfSize.{w, w} π.Cat := π.hasColimitsOfSize

instance (J : Type w) [Preorder J] : SmallObject.HasIterationOfShape π.Cat J where

instance : HasFiniteColimits π.Cat :=
  hasFiniteColimits_of_hasColimitsOfSize π.Cat

instance : CategoryWithWeakEquivalences π.Cat where
  weakEquivalences := π.W

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
  π.src_I_le_S j (π.J_le_I j hj)

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

lemma preservesColimit (X : π.Cat) (hX : X ∈ π.S) {A B : π.Cat} (i : A ⟶ B) (hi : π.I i)
    (F : Cardinal.aleph0.{w}.ord.toType ⥤ π.Cat)
    (hF : ∀ j (hj : ¬IsMax j), (coproducts.{w} π.I).pushouts (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op X)) := by
  sorry

instance isCardinalForSmallObjectArgument_I :
    π.I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w} where
  hasIterationOfShape := by infer_instance
  preservesColimit {A B} i hi F _ hF :=
    π.preservesColimit A (π.src_I_le_S i hi) i hi F hF

instance isCardinalForSmallObjectArgument_J :
    π.J.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w} where
  hasIterationOfShape := by infer_instance
  preservesColimit {A B} j hj F _ hF :=
    π.preservesColimit A (π.src_J_le_S j hj) j (π.J_le_I j hj) F
      (fun j hj ↦ monotone_pushouts (monotone_coproducts (J_le_I π)) _ (hF j hj))

instance : HasSmallObjectArgument.{w} π.I where
  exists_cardinal := ⟨Cardinal.aleph0.{w}, inferInstance, inferInstance, inferInstance⟩

instance : HasSmallObjectArgument.{w} π.J where
  exists_cardinal := ⟨Cardinal.aleph0.{w}, inferInstance, inferInstance, inferInstance⟩

lemma J_rlp_llp_le_cofibrations : π.J.rlp.llp ≤ cofibrations π.Cat :=
  antitone_llp (antitone_rlp π.J_le_I)

lemma infiniteCompositions_le_weakEquivalences :
    (coproducts.{w} π.J).pushouts.transfiniteCompositionsOfShape ℕ ≤
      weakEquivalences π.Cat := π.infiniteCompositions_le_W'

lemma transfiniteCompositionsOfShape_aleph0_le_weakEquivalences :
    (coproducts.{w} π.J).pushouts.transfiniteCompositionsOfShape
      Cardinal.aleph0.{w}.ord.toType ≤ weakEquivalences π.Cat := by
  refine le_trans ?_ π.infiniteCompositions_le_weakEquivalences
  rw [transfiniteCompositionsOfShape_aleph0]

lemma J_rlp_llp_le_weakEquivalences : π.J.rlp.llp ≤ weakEquivalences π.Cat := by
  rw [SmallObject.rlp_llp_of_isCardinalForSmallObjectArgument' π.J Cardinal.aleph0.{w}]
  exact (monotone_retracts π.transfiniteCompositionsOfShape_aleph0_le_weakEquivalences).trans
    (MorphismProperty.retracts_le _)

lemma J_rlp_llp_le_trivialCofibrations : π.J.rlp.llp ≤ trivialCofibrations π.Cat := by
  simp only [trivialCofibrations, le_inf_iff]
  constructor
  · apply J_rlp_llp_le_cofibrations
  · apply J_rlp_llp_le_weakEquivalences

instance : (trivialCofibrations π.Cat).HasFunctorialFactorization (fibrations π.Cat) :=
  MorphismProperty.hasFunctorialFactorization_of_le (W₂ := π.J.rlp)
    (π.J_rlp_llp_le_trivialCofibrations) (by rfl)

lemma fibration_is_trivial_iff {X Y : π.Cat} (p : X ⟶ Y) (hp : π.J.rlp p) :
    π.I.rlp p ↔ weakEquivalences π.Cat p := π.fibration_is_trivial_iff' p hp

lemma I_rlp_eq_trivialFibrations : π.I.rlp = trivialFibrations π.Cat := by
  ext X Y p
  simp only [trivialFibrations, fibrations_eq, min_iff]
  constructor
  · intro hp
    have hp' := antitone_rlp π.J_le_I _ hp
    rw [π.fibration_is_trivial_iff p hp'] at hp
    exact ⟨hp', hp⟩
  · rintro ⟨hp', hp⟩
    rwa [π.fibration_is_trivial_iff p hp']

instance : (cofibrations π.Cat).HasFunctorialFactorization (trivialFibrations π.Cat) :=
  MorphismProperty.hasFunctorialFactorization_of_le (W₁ := π.I.rlp.llp) (W₂ := π.I.rlp)
    (by rfl) (by rw [I_rlp_eq_trivialFibrations])

instance {A B X Y : π.Cat} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] : HasLiftingProperty i p := by
  sorry

instance {A B X Y : π.Cat} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] : HasLiftingProperty i p := by
  have hi := mem_cofibrations i
  have hp := mem_trivialFibrations p
  rw [cofibrations_eq] at hi
  rw [← π.I_rlp_eq_trivialFibrations] at hp
  exact hi p hp

instance : ModelCategory π.Cat where

end TopPackage

end HomotopicalAlgebra