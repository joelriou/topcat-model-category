import TopCatModelCategory.TopCat.Adj

universe v u

open CategoryTheory Limits Opposite
instance PathConnectedSpace.ulift (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    PathConnectedSpace (ULift.{v} X) :=
  Equiv.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous

namespace TopCat

instance {J : Type v} (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (F : J → TopCat.{u}) :
    PreservesColimit (Discrete.functor F) (coyoneda.obj (op (TopCat.of X))) where
  preserves {c : Cofan _} hc :=
    ⟨(isColimitMapCoconeCofanMkEquiv (g := c.inj) _).2 (by
      dsimp
      sorry)⟩

instance test (J : Type v) (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    PreservesColimitsOfShape (Discrete J) (coyoneda.obj (op (TopCat.of X))) where
  preservesColimit := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

open Simplicial

instance (J : Type v) (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete J)
      (coyoneda.obj (op (SimplexCategory.toTop.{u}.obj n))) := by
  dsimp [SimplexCategory.toTop, uliftFunctor]
  infer_instance

instance (J : Type v) :
    PreservesColimitsOfShape (Discrete J) toSSet.{u} where
  preservesColimit := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _
    (fun ⟨n⟩ ↦ (IsColimit.equivOfNatIsoOfIso
      (NatIso.ofComponents (fun ⟨j⟩ ↦ Equiv.ulift.symm.toIso)) _  _
      (Cocones.ext Equiv.ulift.symm.toIso)).1
      (isColimitOfPreserves (coyoneda.obj (op (SimplexCategory.toTop.obj n))) hc))⟩⟩

end TopCat
