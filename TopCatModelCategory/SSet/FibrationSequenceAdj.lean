import TopCatModelCategory.SSet.FibrationSequence
import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.TopCat.ToTopFibration
import TopCatModelCategory.TopCat.ToTopExact

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  TopCat.modelCategory Limits Simplicial Opposite

namespace SSet

namespace FibrationSequence

variable (seq : FibrationSequence.{0})

instance : IsIso (sSetTopAdj.unit.app Δ[0]) :=
  ⟨stdSimplex.isTerminalObj₀.from _, by simp,
    (stdSimplex.isTerminalObj₀.isTerminalObj (SSet.toTop ⋙ TopCat.toSSet)).hom_ext _ _⟩

@[simps]
noncomputable def toTopToSSet : FibrationSequence where
  F := TopCat.toSSet.obj (toTop.obj seq.F)
  E := TopCat.toSSet.obj (toTop.obj seq.E)
  B := TopCat.toSSet.obj (toTop.obj seq.B)
  i := TopCat.toSSet.map (toTop.map seq.i)
  p := TopCat.toSSet.map (toTop.map seq.p)
  f := (sSetTopAdj.unit.app seq.F).app _ seq.f
  e := (sSetTopAdj.unit.app seq.E).app _ seq.e
  b := (sSetTopAdj.unit.app seq.B).app _ seq.b
  hf := by simp only [← seq.hf, ← FunctorToTypes.comp,
      Adjunction.unit_naturality]
  he := by simp only [← seq.he, ← FunctorToTypes.comp,
      Adjunction.unit_naturality]
  isPullback :=
    (seq.isPullback.map (SSet.toTop ⋙ TopCat.toSSet)).of_iso (Iso.refl _) (Iso.refl _)
      (IsTerminal.uniqueUpToIso
        (stdSimplex.isTerminalObj₀.isTerminalObj (SSet.toTop ⋙ TopCat.toSSet))
        stdSimplex.isTerminalObj₀) (Iso.refl _) (by simp)
        (stdSimplex.isTerminalObj₀.hom_ext _ _) (by simp)
        (by simp [← cancel_epi (sSetTopAdj.unit.app Δ[0])])

instance : IsFibrant (seq.toTopToSSet.B) := by
  dsimp
  infer_instance

@[simps]
noncomputable def ιtoTopToSSet : seq ⟶ seq.toTopToSSet where
  mor₁ := sSetTopAdj.unit.app _
  mor₂ := sSetTopAdj.unit.app _
  mor₃ := sSetTopAdj.unit.app _

end FibrationSequence

end SSet
