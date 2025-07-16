import TopCatModelCategory.TopCat.Adj

open CategoryTheory Limits

namespace SSet

-- this is wrong: this is true only when we consider
-- the function from simplicial sets to Kelley spaces
--instance : PreservesFiniteLimits toTop := sorry

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop := sorry

end SSet
