import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.ToTopObjHomeo
import TopCatModelCategory.ConvexCompact

universe u

open CategoryTheory Limits Topology

namespace SSet

section

open NormedSpace SimplexCategory

instance (n : ℕ) : DeltaGeneratedSpace' (Hyperplane.stdSimplex n) := by
  let e := homeoClosedBallOfConvexCompact (Hyperplane.convex_stdSimplex n)
    (Hyperplane.isCompact_stdSimplex n) (Hyperplane.zero_mem_interior_stdSimplex n)
  exact e.symm.isQuotientMap.isGeneratedBy

instance (n : SimplexCategory) : DeltaGeneratedSpace' n.toTopObj := by
  induction' n using SimplexCategory.rec with n
  exact (Hyperplane.stdSimplexHomeo n).isQuotientMap.isGeneratedBy

end

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
