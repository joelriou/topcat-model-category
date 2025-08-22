import Mathlib.Topology.MetricSpace.Bounded

universe u v

/-- If `U : ι → Set X` is an open covering of a compact metric space `X`,
there exists `ε > 0` such that any subset of `X` of diameter `≤ ε`
is containted in some `U i`. -/
lemma CompactSpace.exists_mesh {X : Type u} [MetricSpace X] [CompactSpace X]
    {ι : Type*} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hU' : ⋃ i, U i = Set.univ) :
    ∃ ε > 0, ∀ (S : Set X) (_ : Metric.diam S ≤ ε), ∃ (i : ι), S ⊆ U i := by
  let α := { p : (Σ (x : X), { r : ℝ // r > 0 }) //
    ∃ (i : ι), Metric.ball p.1 (2 * p.2) ⊆ U i}
  let V (a : α) : Set X := Metric.ball a.1.1 a.1.2
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover V (fun _ ↦ Metric.isOpen_ball) (by
    intro x _
    have hx := Set.mem_univ x
    rw [← hU', Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨ε, hε₁, hε₂⟩ := Metric.isOpen_iff.1 (hU i) _ hi
    obtain ⟨d, rfl⟩ : ∃ d, ε = 2 * d := ⟨ε/2, by ring⟩
    simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left] at hε₁
    exact le_iSup V ⟨⟨x, ⟨d, hε₁⟩⟩, i, hε₂⟩ (by simpa [V]))
  obtain ⟨ε, hε₁, hε₂⟩ : ∃ ε > 0, ∀ (a : T), ε ≤ a.1.1.2.1 := by
    by_cases hT' : T.Nonempty
    · let ρ (a : α) : ℝ := a.1.2.1
      refine ⟨(Finset.image ρ T).min' (by rwa [Finset.image_nonempty]), ?_,
        fun a ↦ (Finset.image _ _).min'_le _ (by
          simp only [Finset.mem_image]
          exact ⟨a.1, a.2, rfl⟩)⟩
      have := ((Finset.image ρ T).min'_mem (by rwa [Finset.image_nonempty]))
      simp only [Finset.mem_image] at this
      obtain ⟨a, ha, ha'⟩ := this
      simpa only [← ha'] using a.1.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty] at hT'
      exact ⟨1, by simp, fun ⟨a, ha⟩ ↦ by simp [hT'] at ha⟩
  refine ⟨ε, hε₁, fun S hS ↦ ?_⟩
  by_cases hS' : S.Nonempty
  · obtain ⟨x, hx⟩ := hS'
    have hx' := hT (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨a, ha, ha'⟩ := hx'
    have ha'' := hε₂ ⟨a, ha⟩
    obtain ⟨⟨x₀, r, hr⟩, i, hi⟩ := a
    refine ⟨i, fun y hy ↦ hi ?_⟩
    simp only [Metric.mem_ball]
    refine lt_of_le_of_lt (dist_triangle y x x₀)
      (lt_of_lt_of_eq (add_lt_add_of_le_of_lt (le_trans ?_ ha'') ha') (two_mul _).symm)
    refine le_trans (Metric.dist_le_diam_of_mem' ?_ hy hx) hS
    simpa only [← Metric.isBounded_iff_ediam_ne_top]
      using Metric.isBounded_of_compactSpace
  · obtain rfl : S = ∅ := by
      simpa only [← Set.not_nonempty_iff_eq_empty]
    exact ⟨Classical.arbitrary _, by simp⟩
