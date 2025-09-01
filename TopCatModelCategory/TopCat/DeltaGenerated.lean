import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.AlgebraicTopology.SingularSet
import TopCatModelCategory.ModelCategoryTopCat

open CategoryTheory Opposite Simplicial HomotopicalAlgebra Limits DeltaGenerated

namespace TopCat

instance : deltaGeneratedToTop.IsLeftAdjoint := inferInstance
instance : topToDeltaGenerated.IsRightAdjoint := coreflectorAdjunction.isRightAdjoint

lemma asIso_coreflectorAdjunction.unit.app_inv_hom_coe (X : DeltaGenerated.{u}) :
    (asIso (coreflectorAdjunction.unit.app X)).inv.hom.1 = id := by
  ext x
  exact ConcreteCategory.congr_hom (asIso (coreflectorAdjunction.unit.app X)).inv_hom_id x

def coreflectorAdjunctionUnitIso : 𝟭 _ ≅ deltaGeneratedToTop ⋙ topToDeltaGenerated :=
  NatIso.ofComponents (fun X ↦
    { hom := TopCat.ofHom ⟨id, (coreflectorAdjunction.unit.app X).hom.continuous⟩
      inv := TopCat.ofHom ⟨id, by
        convert (asIso (coreflectorAdjunction.unit.app X)).inv.hom.continuous
        exact (asIso_coreflectorAdjunction.unit.app_inv_hom_coe _).symm⟩ })

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
    DeltaGeneratedSpace (ULift.{u} n.toTopObj) :=
  Homeomorph.ulift.symm.isQuotientMap.deltaGeneratedSpace

instance (n : SimplexCategory) :
    DeltaGeneratedSpace (SimplexCategory.toTop.{u}.obj n) := by
  dsimp [uliftFunctor]
  infer_instance

noncomputable def deltaGeneratedToTopCompToSSetCompEvaluationIso (n : SimplexCategory):
    deltaGeneratedToTop.{u} ⋙ toSSet ⋙ SSet.evaluation.obj (op n) ≅
      coyoneda.obj (op (.of (SimplexCategory.toTop.{u}.obj n))) :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso ((TopCat.toSSetObjEquiv _ _).trans
    ((Homeomorph.continuousMapCongr (Homeomorph.ulift.{u}.symm) (Homeomorph.refl _)).trans
      ((ConcreteCategory.homEquiv (C := TopCat.{u})
        (X := uliftFunctor.obj (.of n.toTopObj)) (Y := X.toTop)).symm))))

instance : PreservesFiniteLimits (deltaGeneratedToTop.{u} ⋙ TopCat.toSSet) where
  preservesFiniteLimits J :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsLimits _ (fun ⟨n⟩ ↦
      (IsLimit.equivOfNatIsoOfIso
        (Functor.isoWhiskerLeft F (deltaGeneratedToTopCompToSSetCompEvaluationIso n).symm) _ _
          (Cones.ext ((deltaGeneratedToTopCompToSSetCompEvaluationIso n).app _)).symm).1
        (isLimitOfPreserves (coyoneda.obj _) hc))⟩⟩⟩

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

lemma deltaGeneratedSpace_of_isColimit {J : Type*} [Category J] {F : J ⥤ TopCat.{u}}
    {c : Cocone F} (hc : IsColimit c) [∀ j, DeltaGeneratedSpace (F.obj j)] :
    DeltaGeneratedSpace c.pt :=
  (TopCat.IsColimit.isQuotientMap hc).deltaGeneratedSpace

instance (n : SimplexCategory) :
    DeltaGeneratedSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj n)) := by
  have e : SSet.toTop.obj (SSet.stdSimplex.{u}.obj n) ≃ₜ n.toTopObj :=
    (homeoOfIso (SSet.toTopSimplex.{u}.app n)).trans Homeomorph.ulift
  exact e.symm.isQuotientMap.deltaGeneratedSpace

instance (X : SSet.{u}) : DeltaGeneratedSpace (SSet.toTop.obj X) := by
  have (j : (Functor.Elements X)ᵒᵖ) :
      DeltaGeneratedSpace ((Presheaf.functorToRepresentables X ⋙ SSet.toTop).obj j) :=
    inferInstanceAs (DeltaGeneratedSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj j.unop.1.unop)))
  exact deltaGeneratedSpace_of_isColimit (isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable X))

instance :
    ((fibrations TopCat.{u}).inverseImage deltaGeneratedToTop).IsStableUnderBaseChange where
  of_isPullback := by
    intro X₃ X₂ X₁ X₄ b r t l sq h
    let b' : X₃.toTop ⟶ X₄.toTop := b
    let r' : X₂.toTop ⟶ X₄.toTop := r
    let Z := pullback r' b'
    let t' : Z ⟶ _ := pullback.fst r' b'
    let l' : Z ⟶ _ := pullback.snd r' b'
    have sq' : IsPullback t' l' r' b' := IsPullback.of_hasPullback r' b'
    have hl' := MorphismProperty.of_isPullback (P := fibrations TopCat.{u}) sq' h
    rw [MorphismProperty.inverseImage_iff]
    rw [← fibration_iff, ← fibration_deltaCoreflection_map_iff, fibration_iff] at hl'
    obtain ⟨e, he⟩ : ∃ (e : DeltaGenerated.topToDeltaGenerated.obj Z ≅ X₁),
        e.hom ≫ l = deltaCoreflection.map l' ≫ fromDeltaCoreflection.app X₃.toTop := by
      obtain ⟨e', _, h⟩ :=
        IsPullback.exists_iso_of_isos sq (sq'.map DeltaGenerated.topToDeltaGenerated)
          (asIso (coreflectorAdjunction.unit.app _))
          (asIso (coreflectorAdjunction.unit.app _))
          (asIso (coreflectorAdjunction.unit.app _))
          (coreflectorAdjunction.unit.naturality r)
          (coreflectorAdjunction.unit.naturality b)
      refine ⟨e'.symm, ?_⟩
      dsimp at h ⊢
      rw [← cancel_mono (DeltaGenerated.coreflectorAdjunction.unit.app X₃), Category.assoc,
        h, e'.inv_hom_id_assoc]
      apply deltaGeneratedToTop.map_injective
      dsimp
      -- neees cleaning up...
      erw [Category.assoc, coreflectorAdjunction.right_triangle_components X₃.toTop,
        Category.comp_id]
      rfl
    refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1 hl'
    refine Arrow.isoMk (DeltaGenerated.deltaGeneratedToTop.mapIso e)
      (asIso (fromDeltaCoreflection.app X₃.toTop)) he

instance :
    ((trivialFibrations TopCat.{u}).inverseImage deltaGeneratedToTop).IsStableUnderBaseChange where
  of_isPullback := by
    intro X₃ X₂ X₁ X₄ b r t l sq h
    let b' : X₃.toTop ⟶ X₄.toTop := b
    let r' : X₂.toTop ⟶ X₄.toTop := r
    let Z := pullback r' b'
    let t' : Z ⟶ _ := pullback.fst r' b'
    let l' : Z ⟶ _ := pullback.snd r' b'
    have sq' : IsPullback t' l' r' b' := IsPullback.of_hasPullback r' b'
    have hl' := MorphismProperty.of_isPullback (P := trivialFibrations TopCat.{u}) sq' h
    rw [MorphismProperty.inverseImage_iff]
    rw [← mem_trivialFibrations_deltaCoreflection_map_iff] at hl'
    obtain ⟨e, he⟩ : ∃ (e : DeltaGenerated.topToDeltaGenerated.obj Z ≅ X₁),
        e.hom ≫ l = deltaCoreflection.map l' ≫ fromDeltaCoreflection.app X₃.toTop := by
      obtain ⟨e', _, h⟩ :=
        IsPullback.exists_iso_of_isos sq (sq'.map DeltaGenerated.topToDeltaGenerated)
          (asIso (coreflectorAdjunction.unit.app _))
          (asIso (coreflectorAdjunction.unit.app _))
          (asIso (coreflectorAdjunction.unit.app _))
          (coreflectorAdjunction.unit.naturality r)
          (coreflectorAdjunction.unit.naturality b)
      refine ⟨e'.symm, ?_⟩
      dsimp at h ⊢
      rw [← cancel_mono (DeltaGenerated.coreflectorAdjunction.unit.app X₃), Category.assoc,
        h, e'.inv_hom_id_assoc]
      apply deltaGeneratedToTop.map_injective
      dsimp
      -- neees cleaning up...
      erw [Category.assoc, coreflectorAdjunction.right_triangle_components X₃.toTop,
        Category.comp_id]
      rfl
    refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1 hl'
    refine Arrow.isoMk (DeltaGenerated.deltaGeneratedToTop.mapIso e)
      (asIso (fromDeltaCoreflection.app X₃.toTop)) he

end TopCat

noncomputable def SSet.toDeltaGenerated : SSet.{u} ⥤ DeltaGenerated where
  obj X := .of (toTop.obj X)
  map f := toTop.map f

noncomputable def SSet.toDeltaGeneratedCompIso :
    toDeltaGenerated.{u} ⋙ deltaGeneratedToTop ≅ toTop := Iso.refl _

noncomputable def SSet.toDeltaGeneratedIso :
    toDeltaGenerated.{u} ≅ toTop ⋙ topToDeltaGenerated :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (asIso coreflectorAdjunction.unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso topToDeltaGenerated

namespace DeltaGenerated

variable {J : Type*} [Category J] {F : J ⥤ DeltaGenerated.{u}}
  (c : Cone (F ⋙ deltaGeneratedToTop))

@[simps pt]
def coneOfTopCat : Cone F where
  pt := topToDeltaGenerated.obj c.pt
  π :=
    { app j :=
        fullyFaithfulDeltaGeneratedToTop.preimage
          ((coreflectorAdjunction.homEquiv _ _).symm
            (topToDeltaGenerated.map (c.π.app j)))
      naturality j₁ j₂ f := by
        ext x
        exact ConcreteCategory.congr_hom (c.w f).symm x }

lemma coneOfTopCat_π_app_apply {j : J} (x : DeltaGeneratedSpace.of c.pt) :
    (coneOfTopCat c).π.app j x = c.π.app j x := rfl

variable {c} (hc : IsLimit c)

def isLimitTopToDeltaGenerated {F : J ⥤ TopCat.{u}} {c : Cone F} (hc : IsLimit c) :
    IsLimit (topToDeltaGenerated.mapCone c) where
  lift s :=
    coreflectorAdjunction.homEquiv _ _
      (hc.lift ((Cones.postcompose ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (TopCat.fromDeltaCoreflection) ≫ F.rightUnitor.hom)).obj (deltaGeneratedToTop.mapCone s)))
  fac s j := by
    apply (coreflectorAdjunction.homEquiv _ _).symm.injective
    rw [Functor.mapCone_π_app, Adjunction.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply, IsLimit.fac]
    rfl
  uniq s m hm := by
    refine (coreflectorAdjunction.homEquiv _ _).symm.injective
      (hc.hom_ext (fun j ↦ ?_))
    ext x
    simpa using congr_fun ((forget _).congr_map (hm j)) x

def isLimitOfTopCat : IsLimit (coneOfTopCat c) :=
  (IsLimit.equivOfNatIsoOfIso
    (F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft _
    TopCat.coreflectorAdjunctionUnitIso ≪≫ (Functor.associator _ _ _).symm) _ _
    (Cones.ext (Iso.refl _))).2
    (isLimitTopToDeltaGenerated hc)

end DeltaGenerated
