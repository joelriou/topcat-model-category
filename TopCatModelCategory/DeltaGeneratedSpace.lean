import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

universe u

open Topology

instance : DeltaGeneratedSpace.{u} PUnit where
  le_deltaGenerated := by simp

lemma Topology.IsQuotientMap.retraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (r : C(X, Y)) (s : C(Y, X)) (hrs : r.comp s = .id _) :
    IsQuotientMap r := by
  refine ⟨fun y ↦ ⟨s y, DFunLike.congr_fun hrs y⟩, ?_⟩
  ext U
  change IsOpen U ↔ IsOpen (r ⁻¹' U)
  refine ⟨fun h ↦ r.continuous.isOpen_preimage U h,
    fun h ↦ ?_⟩
  convert s.continuous.isOpen_preimage _ h
  simp [← Set.preimage_comp, ← ContinuousMap.coe_comp, hrs]

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Metric.closedBall

noncomputable def retraction (v : E) : Metric.closedBall (0 : E) 1 :=
  if hv : ‖v‖ ≤ 1 then ⟨v, by simpa using hv⟩ else ⟨‖v‖⁻¹ • v, by
    simpa [norm_smul] using inv_mul_le_one⟩

variable {E}

lemma retraction_of_dist_le_one (v : E) (hv : ‖v‖ ≤ 1) :
    retraction E v = ⟨v, by simpa using hv⟩ := by
  dsimp [retraction]
  aesop

lemma retraction_of_one_le_dist (v : E) (hv : 1 ≤ ‖v‖) :
    retraction E v = ⟨‖v‖⁻¹ • v, by simpa [norm_smul] using inv_mul_le_one⟩ := by
  obtain hv | hv := hv.lt_or_eq
  · exact dif_neg (by aesop)
  · simp [retraction_of_dist_le_one v (by grind), hv.symm]

variable (E)

lemma retraction_restrict_closedBall :
    (closedBall 0 1).restrict (retraction E) = fun v ↦ v := by
  ext v
  dsimp
  rw [retraction_of_dist_le_one _ (by simpa [closedBall] using v.2)]

@[continuity]
lemma continuous_retraction : Continuous (retraction E) := by
  rw [← continuousOn_univ]
  have : Set.univ = Metric.closedBall (0 : E) 1 ∪ { v | 1 ≤ ‖v‖} := by
    ext
    simpa using LinearOrder.le_total _ _
  rw [this]
  apply ContinuousOn.union_of_isClosed _ _ isClosed_closedBall
    (isClosed_le (by continuity) (by continuity))
  · have : (closedBall 0 1).restrict (retraction E) = id := by
      ext v
      dsimp
      rw [retraction_of_dist_le_one _ (by simpa [closedBall] using v.2)]
    rw [continuousOn_iff_continuous_restrict,
      retraction_restrict_closedBall]
    continuity
  · have : ({v | 1 ≤ ‖v‖}.restrict (retraction E)) =
        fun v ↦ ⟨‖v.1‖⁻¹ • v, by simpa [norm_smul] using inv_mul_le_one⟩ := by
      ext v
      dsimp
      rw [retraction_of_one_le_dist _ v.2]
    rw [continuousOn_iff_continuous_restrict, this]
    refine Continuous.subtype_mk (Continuous.smul (Continuous.inv₀ (by continuity) ?_)
      continuous_induced_dom) _
    rintro ⟨x, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    grind

@[simp]
lemma retraction_apply (x : Metric.closedBall (0 : E) 1) :
    retraction E x = x :=
  retraction_of_dist_le_one _ (by simpa [closedBall] using x.2)

lemma retraction_isQuotientMap :
    IsQuotientMap (retraction E) :=
  IsQuotientMap.retraction ⟨retraction E, by continuity⟩ ⟨Subtype.val, by continuity⟩
    (by aesop)

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
  (retraction_isQuotientMap E).deltaGeneratedSpace

end Metric.closedBall

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

variable (E) in
noncomputable def unitBallHomeo :
    Metric.ball (0 : E) 1 ≃ₜ E where
  toFun v := (1 - ‖v.1‖)⁻¹ • v
  invFun u := ⟨(1 + ‖u‖)⁻¹ • u, by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [inv_mul_lt_one₀ (by positivity), abs_of_pos (by positivity)]
    grind⟩
  left_inv v := by
    ext
    simp [smul_smul, norm_smul]
    rw [abs_of_pos (by
      simpa only [sub_pos, Metric.mem_ball, dist_zero_right] using v.2)]
    trans (1 : ℝ) • v
    · congr 1
      have : 1 - ‖v.1‖ ≠ 0 := by
        have := v.2
        simp only [Metric.mem_ball, dist_zero_right] at this
        rw [sub_ne_zero]
        intro hv'
        grind
      field_simp
    · rw [one_smul]
  right_inv u := by
    simp [smul_smul, norm_smul]
    rw [abs_of_pos (by positivity)]
    trans (1 : ℝ) • u
    · congr 1
      field_simp
    · rw [one_smul]
  continuous_toFun := by
    exact Continuous.smul (Continuous.inv₀ (by continuity) (by simp; grind)) continuous_subtype_val
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.smul (Continuous.inv₀ (by continuity) (by intro; positivity)) (by continuity)) _

noncomputable def openBallHomeoUnitBall (x : E) (e : ℝ) (he : 0 < e) :
    (Metric.ball x e) ≃ₜ Metric.ball (0 : E) 1 where
  toFun v := ⟨e⁻¹ • (v - x), by
    obtain ⟨v, hv⟩ := v
    simpa [dist_eq_norm, norm_smul, abs_of_pos he, inv_mul_lt_one₀ he] using hv⟩
  invFun u := ⟨x + e • u, by
    obtain ⟨u, hu⟩ := u
    simp only [Metric.mem_ball, dist_zero_right] at hu
    simpa [norm_smul, abs_of_pos he] using mul_lt_of_lt_one_right he hu⟩
  left_inv v := by
    ext
    simp [smul_smul, mul_inv_cancel₀ he.ne']
  right_inv u := by
    ext
    simp [smul_smul, inv_mul_cancel₀ he.ne']
  continuous_toFun := by exact (continuous_const.smul (by continuity)).subtype_mk _
  continuous_invFun :=
    by exact Continuous.subtype_mk (continuous_const.add (continuous_const.smul (by continuity))) _

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
