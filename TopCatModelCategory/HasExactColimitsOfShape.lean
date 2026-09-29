module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

@[expose] public section

universe v' u' u

namespace CategoryTheory

instance {C : Type u'} [Category.{v'} C] [IsFiltered C] [Small.{u} C] :
    HasExactColimitsOfShape C (Type u) where
  preservesFiniteLimits := by infer_instance

end CategoryTheory
