import TopCatModelCategory.TopCat.Adj

open CategoryTheory

universe v v' u u'

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

end TopCat

namespace SSet

def toTopUliftIso :
    SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v} ≅
      SSet.uliftFunctor.{v} ⋙ SSet.toTop.{max v u} := by
  sorry

lemma toTopMap_ulift_closedEmbeddings {A B : SSet.{u}} {i : A ⟶ B}
    (hi : TopCat.closedEmbeddings (toTop.map i)) :
      TopCat.closedEmbeddings (toTop.map (SSet.uliftFunctor.{v}.map i)) :=
  (TopCat.closedEmbeddings.arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso toTopUliftIso.{v, u}).app (Arrow.mk i))).1
    (TopCat.closedEmbeddings.uliftFunctor_map.{v} hi)

end SSet
