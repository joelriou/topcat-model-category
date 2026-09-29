module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import TopCatModelCategory.MonoCoprod

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet

instance : MonoCoprod SSet.{u} :=
  inferInstanceAs (MonoCoprod (SimplexCategoryᵒᵖ ⥤ Type u))

end SSet
