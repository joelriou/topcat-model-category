import TopCatModelCategory.Convenient.DeltaGenerated
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.ToTopObjHomeo
import TopCatModelCategory.ConvexCompact

universe u

open CategoryTheory Limits Topology

namespace SimplexCategory

namespace Hyperplane

open NormedSpace

noncomputable def stdSimplexHomeoClosedBall (n : ℕ) :
    stdSimplex n ≃ₜ (Metric.closedBall (0 : Hyperplane n) 1) := by
  obtain _ | n := n
  · exact
      { toFun _ := ⟨0, by simp⟩
        invFun _ := default
        left_inv _ := by subsingleton
        right_inv _ := by subsingleton }
  · exact homeoClosedBallOfConvexCompact (Hyperplane.convex_stdSimplex (n + 1))
      (Hyperplane.isCompact_stdSimplex _) (Hyperplane.zero_mem_interior_stdSimplex _)

end Hyperplane

end SimplexCategory

namespace SSet

section

open NormedSpace SimplexCategory



instance (n : ℕ) : DeltaGeneratedSpace' (Hyperplane.stdSimplex n) :=
  (Hyperplane.stdSimplexHomeoClosedBall n).symm.isQuotientMap.isGeneratedBy

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

instance (J : Type*) [Category J] :
    ReflectsColimitsOfShape J DeltaGenerated'.toTopCat.{u} where
  reflectsColimit := ⟨fun hc ↦ ⟨ObjectProperty.ιReflectsIsColimit _ hc⟩⟩

instance (J : Type*) [Category J] :
    PreservesColimitsOfShape J toDeltaGenerated.{u} where
  preservesColimit :=
    ⟨fun hc ↦ ⟨isColimitOfReflects DeltaGenerated'.toTopCat (isColimitOfPreserves toTop hc)⟩⟩

end SSet
