import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

universe v' u' u

namespace CategoryTheory

instance {C : Type u'} [Category.{v'} C] [IsFiltered C] [Small.{u} C] :
    HasExactColimitsOfShape C (Type u) where
  preservesFiniteLimits := by infer_instance

end CategoryTheory
