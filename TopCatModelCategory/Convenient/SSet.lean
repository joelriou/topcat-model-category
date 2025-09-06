import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.TopCat.Adj

universe u

open CategoryTheory Limits Topology

namespace SSet

instance (n : SimplexCategory) : DeltaGeneratedSpace' n.toTopObj := sorry

instance (n : SimplexCategory) : DeltaGeneratedSpace' (SimplexCategory.toTop.{u}.obj n) :=
  (Homeomorph.ulift.{u} (X := n.toTopObj)).symm.isQuotientMap.isGeneratedBy

instance (n : SimplexCategory) : DeltaGeneratedSpace' (toTop.{u}.obj (stdSimplex.obj n)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).symm.isQuotientMap.isGeneratedBy

instance (X : SSet.{u}) : DeltaGeneratedSpace' (toTop.obj X) :=
  isGeneratedBy.of_isColimit (isColimitOfPreserves toTop X.isColimitCoconeFromElementsOp)
    (fun _ ↦ by dsimp; infer_instance)

noncomputable def toDeltaGenerated : SSet.{u} ⥤ DeltaGenerated' where
  obj X := .of (toTop.obj X)
  map f := toTop.map f

noncomputable def toDeltaGeneratedCompIso :
    toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat ≅ toTop := Iso.refl _

noncomputable def toDeltaGeneratedIso :
    toDeltaGenerated.{u} ≅ toTop ⋙ TopCat.toDeltaGenerated' :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ DeltaGenerated'.adjUnitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso TopCat.toDeltaGenerated'

end SSet
