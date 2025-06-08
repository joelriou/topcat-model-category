import TopCatModelCategory.TopCat.Adj

universe v u

open CategoryTheory Limits Opposite

namespace TopCat

instance {J : Type v} (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (F : J → TopCat.{u}) :
    PreservesColimit (Discrete.functor F) (coyoneda.obj (op (TopCat.of X))) where
  preserves {c : Cofan _} hc :=
    ⟨(isColimitMapCoconeCofanMkEquiv (g := c.inj) _).2 (by
      dsimp
      sorry)⟩

instance (J : Type v) (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    PreservesColimitsOfShape (Discrete J) (coyoneda.obj (op (TopCat.of X))) where
  preservesColimit := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

instance (J : Type v) (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete J)
      (coyoneda.obj (op (SimplexCategory.toTop.obj n))) := by
  dsimp [SimplexCategory.toTop]
  infer_instance

instance (J : Type v) :
    PreservesColimitsOfShape (Discrete J) toSSet where
  preservesColimit := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _
    (fun ⟨n⟩ ↦ isColimitOfPreserves (coyoneda.obj (op (SimplexCategory.toTop.obj n))) hc)⟩⟩

end TopCat
