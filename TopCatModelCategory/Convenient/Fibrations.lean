import TopCatModelCategory.Convenient.SSet
import TopCatModelCategory.ModelCategoryTopCat

open CategoryTheory HomotopicalAlgebra TopCat.modelCategory Topology Limits Opposite

universe u

namespace DeltaGenerated'

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

lemma bijective_toSSet_map_fromDeltaCoreflection_app_app (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((TopCat.toSSet.map (adj.counit.app Y)).app n) := by
  let e : (TopCat.toSSet.obj (TopCat.toDeltaGenerated'.obj Y).obj).obj n ≃
    (TopCat.toSSet.obj Y).obj n :=
    (TopCat.toSSetObjEquiv _ _).trans (Equiv.trans
      (WithGeneratedByTopology.continuousMapEquiv (Z := Y)) (TopCat.toSSetObjEquiv _ _).symm)
  exact e.bijective

instance (n : SimplexCategoryᵒᵖ) :
    IsIso ((TopCat.toSSet.map (adj.counit.app Y)).app n) := by
  rw [isIso_iff_bijective]
  apply bijective_toSSet_map_fromDeltaCoreflection_app_app

instance : IsIso (TopCat.toSSet.map (adj.counit.app Y)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  infer_instance

instance : IsIso (Functor.whiskerRight adj.counit.{u} TopCat.toSSet) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  dsimp
  infer_instance

noncomputable def arrowIso :
    Arrow.mk (TopCat.toSSet.map (toTopCat.map (TopCat.toDeltaGenerated'.map f))) ≅
      Arrow.mk (TopCat.toSSet.map f) :=
  ((Functor.mapArrowFunctor _ _).mapIso
    (asIso (Functor.whiskerRight adj.counit.{u} TopCat.toSSet))).app (Arrow.mk f)

lemma fibration_toTopCat_map_toDeltaGenerated'_map_iff (f : X ⟶ Y) :
    Fibration (toTopCat.map (TopCat.toDeltaGenerated'.map f)) ↔
      Fibration f := by
  rw [← fibration_toSSet_map_iff, ← fibration_toSSet_map_iff, fibration_iff, fibration_iff]
  exact MorphismProperty.arrow_mk_iso_iff _ (arrowIso f)

lemma weakEquivalence_toTopCat_map_toDeltaGenerated'_map_iff (f : X ⟶ Y) :
    WeakEquivalence (toTopCat.map (TopCat.toDeltaGenerated'.map f)) ↔
      WeakEquivalence f := by
  simp only [TopCat.modelCategory.weakEquivalence_iff]
  exact MorphismProperty.arrow_mk_iso_iff _ (arrowIso f)

lemma fibrations_inverseImage_toDeltaGenerated'_comp_toTopCat :
    (fibrations TopCat).inverseImage (TopCat.toDeltaGenerated' ⋙ toTopCat) =
      fibrations _ := by
  ext
  simp only [← fibration_iff, MorphismProperty.inverseImage_iff,
    Functor.comp_map, fibration_toTopCat_map_toDeltaGenerated'_map_iff]

lemma trivialFibrations_inverseImage_toDeltaGenerated'_comp_toTopCat :
    (trivialFibrations TopCat).inverseImage (TopCat.toDeltaGenerated' ⋙ toTopCat) =
      trivialFibrations _ := by
  ext
  simp only [MorphismProperty.inverseImage_iff, mem_trivialFibrations_iff,
    Functor.comp_map, fibration_toTopCat_map_toDeltaGenerated'_map_iff,
    weakEquivalence_toTopCat_map_toDeltaGenerated'_map_iff]

instance :
    ((fibrations _).inverseImage toTopCat.{u}).IsStableUnderBaseChange :=
  MorphismProperty.isStableUnderBaseChange_inverseImage_of_adjunction _ DeltaGenerated'.adj
    fibrations_inverseImage_toDeltaGenerated'_comp_toTopCat

instance :
    ((trivialFibrations _).inverseImage toTopCat.{u}).IsStableUnderBaseChange :=
  MorphismProperty.isStableUnderBaseChange_inverseImage_of_adjunction _ DeltaGenerated'.adj
    trivialFibrations_inverseImage_toDeltaGenerated'_comp_toTopCat

noncomputable def toTopCatCompToSSetCompEvaluationIso (n : SimplexCategory) :
    toTopCat.{u} ⋙ TopCat.toSSet ⋙ SSet.evaluation.obj (op n) ≅
      coyoneda.obj (op (GeneratedByTopCat.of (SimplexCategory.toTop.{u}.obj n))) :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso (by
    refine (TopCat.toSSetObjEquiv _ _).trans
      (Equiv.trans ?_ ConcreteCategory.homEquiv.symm)
    exact (Homeomorph.ulift.{u}.symm).continuousMapCongr (Homeomorph.refl _)))

instance : PreservesFiniteLimits (toTopCat.{u} ⋙ TopCat.toSSet) where
  preservesFiniteLimits J :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsLimits _ (fun ⟨n⟩ ↦
      (IsLimit.equivOfNatIsoOfIso
        (Functor.isoWhiskerLeft F (toTopCatCompToSSetCompEvaluationIso n).symm) _ _
          (Cones.ext ((toTopCatCompToSSetCompEvaluationIso n).app _)).symm).1
        (isLimitOfPreserves (coyoneda.obj _) hc))⟩⟩⟩

end DeltaGenerated'
