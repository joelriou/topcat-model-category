import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.AlgebraicTopology.SingularSet
import TopCatModelCategory.ModelCategoryTopCat

open CategoryTheory Opposite Simplicial HomotopicalAlgebra

universe u

namespace TopCat

open DeltaGenerated

def deltaCoreflection : TopCat.{u} ⥤ TopCat.{u} :=
  topToDeltaGenerated ⋙ DeltaGenerated.deltaGeneratedToTop

def fromDeltaCoreflection : deltaCoreflection ⟶ 𝟭 TopCat.{u} :=
  coreflectorAdjunction.counit

instance (Z : TopCat.{u}) : DeltaGeneratedSpace (deltaCoreflection.obj Z) := by
  dsimp [deltaCoreflection]
  infer_instance

instance (Z : DeltaGenerated.{u}) :
    IsIso (fromDeltaCoreflection.app (deltaGeneratedToTop.obj Z)) := by
  dsimp only [fromDeltaCoreflection]
  infer_instance

instance {X : TopCat.{u}} [DeltaGeneratedSpace X] :
    IsIso (fromDeltaCoreflection.app X) :=
  inferInstanceAs (IsIso (fromDeltaCoreflection.app (deltaGeneratedToTop.obj (.of X))))

lemma deltaGeneratedSpace_iff_isIso_fromDeltaCoreflection_app (X : TopCat.{u}) :
    DeltaGeneratedSpace X ↔ IsIso (fromDeltaCoreflection.app X) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦
    (homeoOfIso (asIso (fromDeltaCoreflection.app X))).isQuotientMap.deltaGeneratedSpace⟩

namespace DeltaGenerated

variable {X Y : TopCat.{u}}

variable [DeltaGeneratedSpace X]

noncomputable def homEquiv : (X ⟶ deltaCoreflection.obj Y) ≃ (X ⟶ Y) where
  toFun f := f ≫ fromDeltaCoreflection.app Y
  invFun g := inv (fromDeltaCoreflection.app X) ≫ deltaCoreflection.map g
  left_inv f := by aesop
  right_inv g := by simp

end DeltaGenerated

variable {X Y : TopCat.{u}}

instance (n : SimplexCategory) :
    DeltaGeneratedSpace n.toTopObj := by
  sorry

instance (n : SimplexCategory) :
    DeltaGeneratedSpace (SimplexCategory.toTop.{u}.obj n) := by
  dsimp [uliftFunctor]
  exact Homeomorph.ulift.symm.isQuotientMap.deltaGeneratedSpace

variable (Y) in
lemma bijective_toSSet_map_fromDeltaCoreflection_app_app (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((toSSet.map (fromDeltaCoreflection.app Y)).app n) := by
  obtain ⟨n⟩ := n
  exact (Equiv.ulift.trans
    ((DeltaGenerated.homEquiv (X := SimplexCategory.toTop.{u}.obj n)).trans
      Equiv.ulift.symm)).bijective

instance (n : SimplexCategoryᵒᵖ) :
    IsIso ((toSSet.map (fromDeltaCoreflection.app Y)).app n) := by
  rw [isIso_iff_bijective]
  apply bijective_toSSet_map_fromDeltaCoreflection_app_app

instance : IsIso (toSSet.map (fromDeltaCoreflection.app Y)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  infer_instance

instance : IsIso (Functor.whiskerRight fromDeltaCoreflection.{u} toSSet) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  dsimp
  infer_instance

noncomputable def deltaCoreflectionToSSetArrowIso (f : X ⟶ Y) :
    Arrow.mk (toSSet.map (deltaCoreflection.map f)) ≅ Arrow.mk (toSSet.map f) :=
  Arrow.isoMk (asIso (toSSet.map (fromDeltaCoreflection.app _)))
    (asIso (toSSet.map (fromDeltaCoreflection.app _)))

lemma weakEquivalence_deltaCoreflection_map_iff (f : X ⟶ Y) :
    WeakEquivalence (deltaCoreflection.map f) ↔ WeakEquivalence f := by
  simp only [modelCategory.weakEquivalence_iff]
  exact MorphismProperty.arrow_mk_iso_iff _ (deltaCoreflectionToSSetArrowIso f)

open modelCategory

lemma fibration_deltaCoreflection_map_iff (f : X ⟶ Y) :
    Fibration (deltaCoreflection.map f) ↔ Fibration f := by
  rw [← fibration_toSSet_map_iff, ← fibration_toSSet_map_iff, fibration_iff, fibration_iff]
  exact MorphismProperty.arrow_mk_iso_iff _ (deltaCoreflectionToSSetArrowIso f)

instance (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (deltaCoreflection.map f) := by
  rwa [weakEquivalence_deltaCoreflection_map_iff]

instance (f : X ⟶ Y) [Fibration f] : Fibration (deltaCoreflection.map f) := by
  rwa [fibration_deltaCoreflection_map_iff]

lemma mem_trivialFibrations_deltaCoreflection_map_iff (f : X ⟶ Y) :
    trivialFibrations _ (deltaCoreflection.map f) ↔ trivialFibrations _ f := by
  simp [mem_trivialFibrations_iff, fibration_deltaCoreflection_map_iff,
    weakEquivalence_deltaCoreflection_map_iff]

end TopCat
