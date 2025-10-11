import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.LeftKanExtensionAlongUliftYoneda
import TopCatModelCategory.SSet.ULift

universe v v' u u'

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

lemma TopologicalSpace.isOpen_ulift_iff {X : Type u} [TopologicalSpace X]
    (F : Set (ULift.{v} X)) : IsOpen F ↔ IsOpen (ULift.up ⁻¹' F) := by
  rw [Homeomorph.ulift.isInducing.isOpen_iff]
  aesop

namespace TopCat

def uliftFunctorComp :
    uliftFunctor.{v, u} ⋙ uliftFunctor.{v'} ≅ uliftFunctor.{max v v'} :=
  NatIso.ofComponents
    (fun X ↦ isoOfHomeo (Homeomorph.ulift.trans (Homeomorph.ulift.trans Homeomorph.ulift.symm)))

instance uliftFunctor_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v', u'} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J} :=
    { preservesColimit {K} := ⟨fun {c} hc ↦ by
        rw [nonempty_isColimit_iff]
        refine ⟨⟨isColimitOfPreserves (forget _ ⋙ CategoryTheory.uliftFunctor.{v}) hc⟩, ?_⟩
        dsimp
        ext F
        dsimp [uliftFunctor] at F ⊢
        rw [TopologicalSpace.isOpen_ulift_iff]
        simp only [((nonempty_isColimit_iff c).1 ⟨hc⟩).2]
        trans ∀ (i : J), IsOpen (c.ι.app i ⁻¹' (ULift.up ⁻¹' F))
        · rw [isOpen_iSup_iff]
          rfl
        · rw [isOpen_iSup_iff]
          apply forall_congr'
          intro i
          symm
          apply TopologicalSpace.isOpen_ulift_iff ⟩ }

end TopCat

namespace SimplexCategory

noncomputable def toTopCompUliftFunctor :
    toTop.{u} ⋙ TopCat.uliftFunctor.{v} ≅ toTop.{max u v} :=
  (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _ TopCat.uliftFunctorComp.{u, v, 0}

end SimplexCategory

namespace Topology.IsClosedEmbedding

variable {X : Type u} {Y : Type u'} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

lemma uliftMap (h : IsClosedEmbedding f) :
    IsClosedEmbedding (ULift.map.{_, _, v, v'} f) :=
  Homeomorph.ulift.symm.isHomeomorph.isClosedEmbedding.comp (h.comp
    Homeomorph.ulift.isHomeomorph.isClosedEmbedding)

end Topology.IsClosedEmbedding

namespace TopCat

lemma closedEmbeddings.uliftFunctor_map {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedEmbeddings f) : closedEmbeddings (uliftFunctor.{v}.map f) :=
  hf.uliftMap

lemma deformationRetracts.uliftFunctor_map {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : deformationRetracts f) : deformationRetracts (uliftFunctor.{v}.map f) := by
  obtain ⟨hf, rfl⟩ := hf
  exact ⟨{
    i := uliftFunctor.map hf.i
    r := uliftFunctor.map hf.r
    retract := by simp [← Functor.map_comp]
    h := ofHom ⟨fun ⟨x, t⟩ ↦ ULift.up (hf.h ⟨ULift.down x, homeomorphI.symm (homeomorphI t)⟩), by
      continuity⟩
    hi := by
      ext ⟨x, t⟩
      dsimp
      exact ULift.down_injective (congr_fun ((forget _).congr_map hf.hi) (by
        exact ⟨x.down, homeomorphI.symm (homeomorphI t)⟩))
    h₀ := by
      ext ⟨y⟩
      exact ULift.down_injective (congr_fun ((forget _).congr_map hf.h₀) y)
    h₁ := by
      ext ⟨y⟩
      exact ULift.down_injective (congr_fun ((forget _).congr_map hf.h₁) y)
  }, rfl⟩

end TopCat

namespace SSet

instance uliftFunctor_preservesColimit {J : Type u'} [Category.{v'} J]
    [HasColimitsOfShape J (Type u)] (F : J ⥤ SSet.{u}) :
    PreservesColimit F uliftFunctor.{v, u} := ⟨fun {c} hc ↦ ⟨by
      apply evaluationJointlyReflectsColimits
      intro k
      exact isColimitOfPreserves (CategoryTheory.uliftFunctor.{v, u})
        (isColimitOfPreserves ((evaluation _ _).obj k) hc)⟩⟩

instance uliftFunctor_preservesColimitsOfSize :
    PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} where
  preservesColimitsOfShape := { }

instance toTop_preservesColimitsOfSize :
    PreservesColimitsOfSize.{0, u} toTop.{u} := inferInstance

namespace toTopUliftIso

noncomputable def unit₁ : stdSimplex.{u} ⋙ SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v} ≅
    SimplexCategory.toTop.{max u v} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight toTopSimplex.{u} TopCat.uliftFunctor.{v} ≪≫
      SimplexCategory.toTopCompUliftFunctor.{v, u}

noncomputable def unit₂ : stdSimplex.{u} ⋙ SSet.uliftFunctor.{v} ⋙ SSet.toTop ≅
    SimplexCategory.toTop.{max u v} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.stdSimplex.compUliftFunctorIso.{v, u} _ ≪≫
      toTopSimplex.{max u v}

instance : Functor.IsLeftKanExtension _ unit₁.{v, u}.inv := by
  have := TopCat.uliftFunctor_preservesColimitsOfSize.{0, v, u, u}
  have := toTop_preservesColimitsOfSize.{u}
  erw [Presheaf.isLeftKanExtension_along_uliftYoneda_iff']
  exact ⟨inferInstance, inferInstance⟩

instance : Functor.IsLeftKanExtension _ unit₂.{v, u}.inv := by
  have := uliftFunctor_preservesColimitsOfSize.{v, u}
  erw [Presheaf.isLeftKanExtension_along_uliftYoneda_iff']
  exact ⟨inferInstance, inferInstance⟩

end toTopUliftIso

open toTopUliftIso in
noncomputable def toTopUliftIso :
    SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v} ≅
      SSet.uliftFunctor.{v} ⋙ SSet.toTop.{max v u} :=
  Functor.leftKanExtensionUnique _ unit₁.{v, u}.inv _ unit₂.{v, u}.inv

lemma toTopMap_ulift_closedEmbeddings {A B : SSet.{u}} {i : A ⟶ B}
    (hi : TopCat.closedEmbeddings (toTop.map i)) :
      TopCat.closedEmbeddings (toTop.map (SSet.uliftFunctor.{v}.map i)) :=
  (TopCat.closedEmbeddings.arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso toTopUliftIso.{v, u}).app (Arrow.mk i))).1
    (TopCat.closedEmbeddings.uliftFunctor_map.{v} hi)

lemma toTopMap_ulift_deformationRetracts {A B : SSet.{u}} {i : A ⟶ B}
    (hi : TopCat.deformationRetracts (toTop.map i)) :
    TopCat.deformationRetracts (toTop.map (SSet.uliftFunctor.{v}.map i)) :=
  (TopCat.deformationRetracts.arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso toTopUliftIso.{v, u}).app (Arrow.mk i))).1
    (TopCat.deformationRetracts.uliftFunctor_map.{v} hi)

end SSet
