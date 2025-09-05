import TopCatModelCategory.Convenient.GeneratedBy
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.UnitBallRetract

universe v v' t u

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [tY : TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]
  [∀ n, IsGeneratedBy X (Fin n → ℝ)]

namespace Topology

namespace IsGeneratedBy

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

instance [FiniteDimensional ℝ E] : IsGeneratedBy X E := by
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₜ E :=
    AffineEquiv.toHomeomorphOfFiniteDimensional
      (finDimVectorspaceEquiv _ (by simp)).symm.toAffineEquiv
  exact e.isQuotientMap.isGeneratedBy

instance [FiniteDimensional ℝ E] : IsGeneratedBy X (Metric.closedBall (0 : E) 1) :=
  (Metric.closedBall.retraction_isQuotientMap E).isGeneratedBy

instance (x : E) (e : ℝ) [FiniteDimensional ℝ E] :
    IsGeneratedBy X (Metric.ball x e) := by
  by_cases he : 0 < e
  · exact ((openBallHomeoUnitBall x e he).trans
      (unitBallHomeo E)).symm.isQuotientMap.isGeneratedBy
  · rw [Metric.ball_eq_empty.2 (by grind)]
    infer_instance

instance (U : TopologicalSpace.Opens E) [FiniteDimensional ℝ E] : IsGeneratedBy X U := by
  have : IsGeneratedBy X E := by infer_instance
  have : IsGeneratedBy X (Metric.ball (0 : E) 1) := by infer_instance
  let ι := { i : E × ℝ // Metric.ball i.1 i.2 ⊆ U }
  let Y (i : ι) : Set E := Metric.ball i.1.1 i.1.2
  have hY (i : ι) : IsOpen (Y i) := Metric.isOpen_ball
  let f (i : ι) : C(Y i, U) := ⟨fun x ↦ ⟨x.1, i.2 x.2⟩, by continuity⟩
  apply IsGeneratedBy.mk' f
  intro V hV
  obtain ⟨W, hW, rfl⟩ : ∃ (W : Set E), W ⊆ U ∧ V = Subtype.val ⁻¹' W :=
    ⟨Subtype.val '' V, by
      rintro _ ⟨v, _, rfl⟩
      exact v.2, by simp⟩
  have hV (i : ι) := (hY i).isOpenMap_subtype_val _ (hV i)
  refine ⟨W, ?_, by simp⟩
  convert isOpen_iUnion hV
  ext w
  simp only [ContinuousMap.coe_mk, Set.mem_iUnion, Set.mem_image, Set.mem_preimage, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right, iff_self_and, f]
  intro hw
  obtain ⟨ε, _, hε⟩ := Metric.mem_nhds_iff.1 (U.isOpen.mem_nhds (hW hw))
  exact ⟨⟨⟨w, ε⟩, hε⟩, by simp [Y]; positivity⟩

end IsGeneratedBy

end Topology
