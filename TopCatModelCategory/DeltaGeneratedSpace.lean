import TopCatModelCategory.UnitBallRetract
import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

universe u

open Topology

instance : DeltaGeneratedSpace.{u} PUnit where
  le_deltaGenerated := by simp

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

instance (n : ℕ) : DeltaGeneratedSpace (Fin n → ℝ) where
  le_deltaGenerated U hU := by
    rw [isOpen_deltaGenerated_iff] at hU
    exact hU n (.id _)

instance [FiniteDimensional ℝ E] : DeltaGeneratedSpace E := by
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₜ E :=
    AffineEquiv.toHomeomorphOfFiniteDimensional
      (finDimVectorspaceEquiv _ (by simp)).symm.toAffineEquiv
  exact e.isQuotientMap.deltaGeneratedSpace

instance [FiniteDimensional ℝ E] :
    DeltaGeneratedSpace (Metric.closedBall (0 : E) 1) :=
  (Metric.closedBall.retraction_isQuotientMap E).deltaGeneratedSpace

namespace DeltaGeneratedSpace

lemma of_coinduced {X : Type*} [hX : TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    [∀ i, DeltaGeneratedSpace (Y i)]
    (hf : ⨆ i, TopologicalSpace.coinduced (f i) inferInstance = hX) :
    DeltaGeneratedSpace X where
  le_deltaGenerated := by
    have hf' (i : ι) : Continuous (f i) := by
      rw [continuous_def]
      intro U hU
      rw [← hf, isOpen_iSup_iff] at hU
      rw [← isOpen_coinduced]
      exact hU i
    intro U hU
    rw [isOpen_deltaGenerated_iff] at hU
    rw [← hf, isOpen_iSup_iff]
    intro i
    rw [isOpen_coinduced, DeltaGeneratedSpace.isOpen_iff]
    intro n g
    exact hU n (ContinuousMap.comp ⟨_, hf' i⟩ g)

lemma of_coinduced' {X : Type*} [hX : TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(Y i, X))
    [∀ i, DeltaGeneratedSpace (Y i)]
    (hf : hX ≤ ⨆ i, TopologicalSpace.coinduced (f i) inferInstance) :
    DeltaGeneratedSpace X :=
  of_coinduced (fun i ↦ f i) (le_antisymm (fun U hU ↦ by
    rw [isOpen_iSup_iff]
    intro i
    rw [isOpen_coinduced]
    exact (f i).continuous.isOpen_preimage _ hU) hf)

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance of_isEmpty (X : Type*) [TopologicalSpace X] [IsEmpty X] : DeltaGeneratedSpace X where
  le_deltaGenerated := Eq.le (by subsingleton)

instance (x : E) (e : ℝ) [FiniteDimensional ℝ E] :
    DeltaGeneratedSpace (Metric.ball x e) := by
  by_cases he : 0 < e
  · exact ((openBallHomeoUnitBall x e he).trans
      (unitBallHomeo E)).symm.isQuotientMap.deltaGeneratedSpace
  · rw [Metric.ball_eq_empty.2 (by grind)]
    infer_instance

lemma of_isOpen_normedSpace [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) :
    DeltaGeneratedSpace U := by
  let ι := { i : E × ℝ // Metric.ball i.1 i.2 ⊆ U }
  let Y (i : ι) : Set E := Metric.ball i.1.1 i.1.2
  have hY (i : ι) : IsOpen (Y i) := Metric.isOpen_ball
  let f (i : ι) : C(Y i, U) := ⟨fun x ↦ ⟨x.1, i.2 x.2⟩, by continuity⟩
  apply DeltaGeneratedSpace.of_coinduced' f
  intro V hV
  simp only [isOpen_iSup_iff, isOpen_coinduced] at hV
  obtain ⟨W, hW, rfl⟩ : ∃ (W : Set E), W ⊆ U ∧ V = Subtype.val ⁻¹' W :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  have hV (i : ι) := (hY i).isOpenMap_subtype_val _ (hV i)
  refine ⟨W, ?_, by simp⟩
  convert isOpen_iUnion hV
  ext w
  simp only [ContinuousMap.coe_mk, Set.mem_iUnion, Set.mem_image, Set.mem_preimage, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right, iff_self_and, f]
  intro hw
  obtain ⟨ε, _, hε⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds (hW hw))
  exact ⟨⟨⟨w, ε⟩, hε⟩, by simp [Y]; positivity⟩

end

end DeltaGeneratedSpace

lemma IsOpen.deltaGeneratedSpace
    {X : Type u} [TopologicalSpace X] [DeltaGeneratedSpace X] {U : Set X}
    (hU : IsOpen U) :
    DeltaGeneratedSpace U := by
  let ι := Σ (n : ℕ), C((Fin n → ℝ), X)
  let Y (i : ι) : Set (Fin i.1 → ℝ) := i.2 ⁻¹' U
  have hY (i : ι) : IsOpen (Y i) := i.2.continuous.isOpen_preimage _ hU
  let f (i : ι) : C(Y i, U) := i.snd.restrictPreimage U
  have (i : ι) := DeltaGeneratedSpace.of_isOpen_normedSpace (hY i)
  apply DeltaGeneratedSpace.of_coinduced' f
  intro V hV
  obtain ⟨W, hW, rfl⟩ : ∃ (W : Set X), W ⊆ U ∧ V = Subtype.val ⁻¹' W :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine ⟨W, ?_, rfl⟩
  simp only [isOpen_iSup_iff, isOpen_coinduced] at hV
  rw [DeltaGeneratedSpace.isOpen_iff]
  intro n p
  have := (hY ⟨n, p⟩).isOpenMap_subtype_val _ (hV ⟨n, p⟩)
  convert this
  ext g
  simp only [Set.mem_preimage, Set.mem_image, ContinuousMap.restrictPreimage_apply,
    Set.restrictPreimage_coe, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
    iff_self_and, Y, f]
  apply hW
