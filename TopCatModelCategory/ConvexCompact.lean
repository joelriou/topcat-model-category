import TopCatModelCategory.Polar

open Topology

universe u

namespace NormedSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Set E} (hX₁ : Convex ℝ X) (hX₂ : IsCompact X) (hX₃ : 0 ∈ interior X)

def homeoClosedBallOfConvexCompact :
    X ≃ₜ Metric.closedBall (0 : E) 1 := by
  have := hX₁
  have := hX₂
  have := hX₃
  sorry

end NormedSpace
