import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.SSet.NonDegenerateSimplices
import Mathlib.Topology.MetricSpace.Bounded

universe v u

open CategoryTheory Simplicial Opposite

namespace SSet

variable {X : SSet.{u}} {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace AffineMap

variable (f : AffineMap X E)

lemma isBounded {n : SimplexCategory} (x : X.obj (op n)) :
    Bornology.IsBounded (Set.range (f.φ x)) :=
  (isCompact_range (f.continuous_φ x)).isBounded

noncomputable def diam (x : X.S) : ℝ := Metric.diam (Set.range (f.φ x.simplex))

lemma monotone_diam : Monotone f.diam := by
  intro x y h
  exact Metric.diam_mono (f.range_subset_of_le h) (f.isBounded y.simplex)

lemma zero_le_diam (x : X.S) : 0 ≤ f.diam x := Metric.diam_nonneg

lemma diam_le (x : (B.obj X).S) (y : X.S) (h : (x.simplex.obj (Fin.last _)).toS ≤ y) :
    f.b.diam x ≤ y.dim / (y.dim + 1) * f.diam y := by
  sorry

noncomputable def mesh : ℝ := iSup (fun (x : X.N) ↦ f.diam x.toS)

lemma diam_le_mesh [X.IsFinite] (x : X.S) : f.diam x ≤ f.mesh := by
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove x.toN)
  exact f.monotone_diam x.self_le_toS_toN

variable [X.Nonempty] [X.IsFinite]

lemma mesh_le_iff (r : ℝ) :
    f.mesh ≤ r ↔ ∀ (x : X.N), f.diam x.toS ≤ r :=
  ciSup_le_iff (Set.finite_range _).bddAbove

lemma monotone_self_div_succ (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a := by positivity) :
    a / (a + 1) ≤ b / (b + 1) := by
  simp only [ge_iff_le] at ha
  have (t : ℝ) (ht : t ≠ -1) : t / (t + 1) = 1 - 1 / (t + 1) := by
    grind
  rw [this a (by grind), this b (by grind), sub_le_sub_iff_left]
  exact one_div_le_one_div_of_le (by grind) (by simpa)

lemma mesh_b_le (d : ℕ) [X.HasDimensionLE d] : f.b.mesh ≤ d / (d + 1) * f.mesh := by
  rw [mesh_le_iff]
  intro x
  refine (f.diam_le x.toS _ (le_refl _)).trans
    (mul_le_mul (monotone_self_div_succ _ _ ?_) (diam_le_mesh _ _) (zero_le_diam _ _) (by positivity))
  simpa [Nat.lt_succ] using
    X.dim_lt_of_nondegenerate ⟨_, (x.simplex.obj (Fin.last _)).nonDegenerate⟩ (d + 1)

end AffineMap

end SSet
