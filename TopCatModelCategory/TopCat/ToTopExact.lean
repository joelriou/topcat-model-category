import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.DeltaGenerated

open CategoryTheory Limits

namespace SSet

-- this is wrong: this is true only when we consider
-- the function from simplicial sets to some sort Kelley spaces

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.deltaCoreflection) := sorry

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop := sorry

end SSet
