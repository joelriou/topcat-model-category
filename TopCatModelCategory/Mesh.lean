import Mathlib.Topology.MetricSpace.Bounded

universe u v

/-- If `U : ι → Set X` is an open covering of a compact metric space `X`,
there exists `ε > 0` such that any subset of `X` of diameter `≤ ε`
is containted in some `U i`. -/
lemma CompactSpace.exists_mesh' {X : Type u} [MetricSpace X] [CompactSpace X]
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hU' : ⋃ i, U i = Set.univ) :
    ∃ ε > 0, ∀ (S : Set X) (_ : S.Nonempty) (_ : Metric.diam S ≤ ε), ∃ (i : ι), S ⊆ U i := by
  obtain ⟨δ, hδ, hδ'⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU (by simp [hU'])
  refine ⟨δ/2, by simpa, fun S ⟨x, hx⟩ hS₂ ↦ ?_⟩
  obtain ⟨i, hi⟩ := hδ' x (by simp)
  refine ⟨i, fun s hs ↦ hi ?_⟩
  simp only [Metric.mem_ball]
  refine lt_of_le_of_lt (Metric.dist_le_diam_of_mem' ?_ hs hx)
    (lt_of_le_of_lt hS₂ (by simpa))
  simpa only [← Metric.isBounded_iff_ediam_ne_top] using
    Metric.isBounded_of_compactSpace
