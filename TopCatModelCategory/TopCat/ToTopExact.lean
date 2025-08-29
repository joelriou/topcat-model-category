import TopCatModelCategory.IsTerminal
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.DeltaGenerated

open CategoryTheory Limits DeltaGenerated Simplicial

namespace SSet

instance : PreservesFiniteLimits toDeltaGenerated.{u} := sorry

instance : PreservesFiniteLimits (toTop.{u} ⋙ topToDeltaGenerated) :=
  preservesFiniteLimits_of_natIso SSet.toDeltaGeneratedIso

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop :=
  IsTerminal.preservesTerminal stdSimplex.isTerminalObj₀
    isTerminalToTopObjStdSimplex₀

instance : PreservesFiniteLimits (toDeltaGenerated.{u} ⋙ deltaGeneratedToTop ⋙ TopCat.toSSet) :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toSSet) :=
  preservesFiniteLimits_of_natIso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso TopCat.toSSet.{u})

end SSet
