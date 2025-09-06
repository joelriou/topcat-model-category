import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import TopCatModelCategory.IsTerminal
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.ToTopEqualizers
import TopCatModelCategory.Convenient.Fibrations

open CategoryTheory Limits Simplicial HomotopicalAlgebra TopCat.modelCategory

namespace SSet

instance : PreservesLimitsOfShape (Discrete WalkingPair) toDeltaGenerated.{u} := by
  sorry

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop.{u} :=
  IsTerminal.preservesTerminal stdSimplex.isTerminalObj₀
    isTerminalToTopObjStdSimplex₀

instance (J : Type*) [Category J] [PreservesLimitsOfShape J toTop.{u}] :
    PreservesLimitsOfShape J toDeltaGenerated.{u} where
  preservesLimit {F} := by
    have : PreservesLimit F (toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat) :=
      preservesLimit_of_natIso _ toDeltaGeneratedCompIso.symm
    exact preservesLimit_of_reflects_of_preserves _ DeltaGenerated'.toTopCat

instance : PreservesFiniteProducts toDeltaGenerated.{u} :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

instance : PreservesFiniteLimits toDeltaGenerated.{u} :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toDeltaGenerated') := by
  exact preservesFiniteLimits_of_natIso SSet.toDeltaGeneratedIso

instance :
    PreservesFiniteLimits (toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat ⋙ TopCat.toSSet) :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toSSet) :=
  preservesFiniteLimits_of_natIso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso TopCat.toSSet.{u})

end SSet
