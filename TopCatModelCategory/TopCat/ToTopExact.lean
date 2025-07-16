import TopCatModelCategory.TopCat.Adj

open CategoryTheory Limits

namespace SSet

-- this is wrong: this is true only when we consider
-- the function from simplicial sets to Kelley spaces
instance : PreservesFiniteLimits toTop := sorry

end SSet
