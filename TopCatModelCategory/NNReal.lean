import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace NNReal

@[simp]
lemma coe_sum {α : Type*} (s : Finset α) (f : α → ℝ≥0) :
    (s.sum f).1 = s.sum (fun i ↦ (f i).1) :=
  map_sum (AddMonoidHom.mk' (fun (x : ℝ≥0) ↦ x.1) (by aesop)) _ _

@[simp]
lemma toReal_sum {α : Type*} (s : Finset α) (f : α → ℝ≥0) :
    toReal (s.sum f) = s.sum (fun i ↦ (f i).1) := by
  apply coe_sum

end NNReal
