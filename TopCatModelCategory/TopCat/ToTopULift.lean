import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.ULift

open CategoryTheory

universe v v' u u'

namespace TopCat

def uliftFunctorComp :
    uliftFunctor.{v, u} ⋙ uliftFunctor.{v'} ≅ uliftFunctor.{max v v'} :=
  NatIso.ofComponents
    (fun X ↦ isoOfHomeo (Homeomorph.ulift.trans (Homeomorph.ulift.trans Homeomorph.ulift.symm)))

end TopCat

namespace SimplexCategory

def toTopCompUliftFunctor :
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
  sorry

end TopCat

namespace SSet

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
  -- Presheaf.isLeftKanExtension_along_uliftYoneda_iff
  sorry

instance : Functor.IsLeftKanExtension _ unit₂.{v, u}.inv := by
  sorry

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
