import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.SSet.NonDegenerateSimplices
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Convex

universe v u

open CategoryTheory Simplicial Opposite

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dist_centerMass_le {d : ℕ} (f : Fin (d + 1) → E) (x : convexHull ℝ (Set.range f)) :
    dist x.1 (Finset.univ.centerMass (R := ℝ) (fun _ ↦ 1) f) ≤ d / (d + 1) *
      Metric.diam (convexHull ℝ (Set.range f)) := by
  obtain _ | d := d
  · obtain ⟨x, hx⟩ := x
    have : Set.range f = {f 0} := by
      ext i
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        rfl
      · aesop
    simp [this] at hx
    simpa [Finset.centerMass]
  let G := Finset.univ.centerMass (R := ℝ) (fun _ ↦ 1) f
  suffices ∀ i, dist (f i) G ≤ (d + 1) / (d + 2) *
      Metric.diam (convexHull ℝ (Set.range f)) by
    obtain ⟨_, ⟨i, rfl⟩, ⟨_, rfl, h⟩⟩ := convexHull_exists_dist_ge2 x.2
      ((subset_convexHull ℝ _) (Set.mem_singleton G))
    rw [Nat.cast_add, Nat.cast_one,]
    simp only [add_assoc, one_add_one_eq_two]
    exact h.trans (this i)
  intro i
  let P : E := Finset.centerMass {i}ᶜ (R := ℝ) (fun _ ↦ 1) f
  have hi : Finset.card {i}ᶜ = d + 1 := by simpa using Finset.card_compl_add_card {i}
  have h : ∑ i ∈ {i}ᶜ, (1 : ℝ) = d + 1 := by simp [hi]
  have hP : dist (f i) G = (d + 1) / (d + 2) * dist (f i) P := by
    have : ((d : ℝ) + 2) • (f i - G) = ((d : ℝ) + 1) • (f i - P) := by
      have hp := Finset.centerMass_insert i {i}ᶜ (R := ℝ) (w := fun _ ↦ 1) f (by simp) (by
        simp only [h]
        positivity)
      simp only [Finset.insert_compl_self, Finset.sum_const, nsmul_eq_mul, mul_one, one_div] at hp
      simp only [hi, show (1 : ℝ) + ↑(d + 1) = d + 2 by simp; ring] at hp
      change G = _ + _ • P at hp
      rw [smul_sub, hp, smul_add, smul_smul, mul_inv_cancel₀ (by positivity), one_smul,
        smul_smul, mul_div_cancel₀ _ (by positivity), Nat.cast_add, Nat.cast_one,
        sub_add_eq_sub_sub]
      nth_rw 2 [← one_smul (M := ℝ) (f i)]
      rw [← sub_smul, add_sub_assoc, ← one_add_one_eq_two, add_sub_cancel_right, smul_sub]
    replace this := congr_arg norm this
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [← Nat.cast_two, ← Nat.cast_add] at this
    rw [abs_of_nonneg (by positivity), Nat.cast_add, Nat.cast_two] at this
    simp only [dist_eq_norm_sub]
    rw [← mul_right_inj' (a := (d : ℝ) + 2) (ne_of_gt (by positivity)), this, ← mul_assoc]
    congr
    rw [mul_comm, div_mul_cancel_of_imp, abs_eq_self]
    · positivity
    · intro h
      exact (ne_of_gt (show 0 < (d : ℝ) + 2 by positivity) h).elim
  rw [hP]
  refine mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
  exact Metric.dist_le_diam_of_mem
    (isBounded_convexHull.2 ((isCompact_range (by continuity)).isBounded))
      (subset_convexHull _ _ (Set.mem_range_self i)) (by
      apply Finset.centerMass_mem_convexHull _ (by simp) ?_ ?_
      · rw [h]
        apply Nat.cast_add_one_pos
      · aesop)

namespace SSet

variable {X : SSet.{u}}

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

lemma exists_diam_eq (x : X.S) :
    ∃ (i j : Fin (x.dim + 1)),
      f.diam x = dist (f.vertex (vertexOfSimplex x.simplex i))
          (f.vertex (vertexOfSimplex x.simplex j)) := by
  let φ (p : Fin (x.dim + 1) × Fin (x.dim + 1)) : ℝ :=
    dist (f.vertex (vertexOfSimplex x.simplex p.1)) (f.vertex (vertexOfSimplex x.simplex p.2))
  let μ := (Finset.univ.image φ).max' (by simp)
  have hμ : μ ∈ _ := (Finset.univ.image φ).max'_mem (by simp)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hμ
  obtain ⟨i, j, hij⟩ := hμ
  dsimp [φ] at hij
  refine ⟨i, j, ?_⟩
  simp only [diam, range_φ_eq_convexHull, convexHull_diam]
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by positivity) _
    rintro _ ⟨i', rfl⟩ _ ⟨j', rfl⟩
    dsimp
    rw [hij]
    exact (Finset.univ.image φ).le_max' _ (by simp [φ])
  · exact Metric.dist_le_diam_of_mem
      (Metric.isBounded_range_iff.2
        ⟨μ, fun i' j' ↦ (Finset.univ.image φ).le_max' _ (by simp [φ])⟩)
      (by simp) (by simp)

lemma diam_le_iff (x : X.S) (r : ℝ):
    f.diam x ≤ r ↔ ∀ (i j : Fin (x.dim + 1)),
      dist (f.vertex (vertexOfSimplex x.simplex i))
        (f.vertex (vertexOfSimplex x.simplex j)) ≤ r := by
  refine ⟨fun h i j ↦ le_trans (Metric.dist_le_diam_of_mem (f.isBounded x.simplex)
      ⟨_, f.φ_vertex x.simplex i⟩ ⟨_, f.φ_vertex x.simplex j⟩) h, fun h ↦ ?_⟩
  obtain ⟨i, j, hij⟩ := f.exists_diam_eq x
  rw [hij]
  apply h

lemma monotone_self_div_succ (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a := by positivity) :
    a / (a + 1) ≤ b / (b + 1) := by
  simp only [ge_iff_le] at ha
  have (t : ℝ) (ht : t ≠ -1) : t / (t + 1) = 1 - 1 / (t + 1) := by
    grind
  rw [this a (by grind), this b (by grind), sub_le_sub_iff_left]
  exact one_div_le_one_div_of_le (by grind) (by simpa)

lemma dist_b_vertex_le {x₁ x₂ : X.N} (hx : x₁ ≤ x₂) :
    dist (f.b.vertex (.mk₀ x₁)) (f.b.vertex (.mk₀ x₂)) ≤ x₂.dim / (x₂.dim + 1) * f.diam x₂.toS := by
  dsimp
  nth_rw 2 [vertex_b]
  dsimp [isobarycenter, SimplexCategory.toTopObj.isobarycenter]
  sorry

lemma diam_b_le (x : (B.obj X).S) (y : X.S) (h : (x.simplex.obj (Fin.last _)).toS ≤ y) :
    f.b.diam x ≤ y.dim / (y.dim + 1) * f.diam y := by
  rw [diam_le_iff]
  intro i j
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm]
    exact this _ _ (by omega)
  refine (f.dist_b_vertex_le (x.simplex.monotone hij)).trans
    (mul_le_mul (monotone_self_div_succ _ _ ?_ (by positivity))
      (f.monotone_diam (le_trans (x.simplex.monotone j.le_last) h))
    (f.zero_le_diam _) (by positivity))
  simpa using N.dim_le_of_toS_le
    ((N.le_iff_toS_le_toS.1 (x.simplex.monotone j.le_last)).trans h)

noncomputable def mesh : ℝ := iSup (fun (x : X.N) ↦ f.diam x.toS)

lemma diam_le_mesh [X.IsFinite] (x : X.S) : f.diam x ≤ f.mesh := by
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove x.toN)
  exact f.monotone_diam x.self_le_toS_toN

variable [X.Nonempty] [X.IsFinite]

lemma mesh_le_iff (r : ℝ) :
    f.mesh ≤ r ↔ ∀ (x : X.N), f.diam x.toS ≤ r :=
  ciSup_le_iff (Set.finite_range _).bddAbove

lemma mesh_b_le (d : ℕ) [X.HasDimensionLE d] : f.b.mesh ≤ d / (d + 1) * f.mesh := by
  rw [mesh_le_iff]
  intro x
  refine (f.diam_b_le x.toS _ (le_refl _)).trans
    (mul_le_mul (monotone_self_div_succ _ _ ?_) (diam_le_mesh _ _) (zero_le_diam _ _) (by positivity))
  simpa [Nat.lt_succ] using
    X.dim_lt_of_nondegenerate ⟨_, (x.simplex.obj (Fin.last _)).nonDegenerate⟩ (d + 1)

end AffineMap

end SSet
