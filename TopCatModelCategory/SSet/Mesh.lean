import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.SSet.Nonempty
import Mathlib.Topology.MetricSpace.Bounded

universe b u
open CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}} {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [X.Nonempty] [X.IsFinite]

namespace AffineMap

variable (f : AffineMap X E)

noncomputable def diam (x : X.S) : ℝ := Metric.diam (Set.range (f.φ x.simplex))

noncomputable def mesh : ℝ := iSup (fun (x : X.N) ↦ f.diam x.toS)

lemma mesh_le_iff (r : ℝ) :
    f.mesh ≤ r ↔ ∀ (x : X.N), f.diam x.toS ≤ r :=
  ciSup_le_iff (Set.finite_range _).bddAbove

end AffineMap

end SSet
