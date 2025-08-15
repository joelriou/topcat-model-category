import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.DeltaGenerated

open CategoryTheory Limits

namespace SSet

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.deltaCoreflection) := sorry

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop := sorry

attribute [local instance] comp_preservesFiniteLimits in
instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toSSet) :=
  preservesFiniteLimits_of_natIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (asIso (Functor.whiskerRight TopCat.fromDeltaCoreflection.{u} TopCat.toSSet)))

end SSet
