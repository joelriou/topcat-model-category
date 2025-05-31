import TopCatModelCategory.SSet.PiZero
import TopCatModelCategory.TopCat.Adj

universe u

open Simplicial CategoryTheory Limits

namespace SSet

variable (X : SSet.{0})

/-lemma surjective_mapπ₀_sSetTopAdj.unit.app :
    Function.Surjective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  intro x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective x
  obtain ⟨⟨⟨n⟩, s⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget _)
    (X.isColimitCoconeFromElementsOp)) x
  induction' n using SimplexCategory.rec with n
  dsimp at x
  refine ⟨π₀.mk (X.map (⦋0⦌.const ⦋n⦌ 0).op s), ?_⟩
  dsimp [-TopCat.toSSetObj₀Equiv_symm_apply]
  sorry-/

end SSet
