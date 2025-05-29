import TopCatModelCategory.TopCat.Adj

open CategoryTheory MorphismProperty TopCat Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen NNReal

namespace TopCat

variable (n : ℕ)

section

variable (i : Fin (n + 1))

-- this definition should be changed using the results
-- in `BoundaryClosedEmbeddings.lean`
protected def horn : Set (ToType ⦋n⦌ → ℝ≥0) :=
  ⦋n⦌.toTopObj ⊓ (⨆ (j ∈ ({i}ᶜ : Set _)), setOf (fun f ↦ f j = 0))

variable {n}

lemma mem_horn_iff (f : ToType ⦋n⦌ → ℝ≥0) :
    f ∈ TopCat.horn n i ↔ f ∈ ⦋n⦌.toTopObj ∧ ∃ (j : Fin (n + 1))
      (_ : j ≠ i), f j = 0 := by
  simp [TopCat.horn]

lemma mem_horn_iff' (f : ⦋n⦌.toTopObj) :
    f.1 ∈ TopCat.horn n i ↔ ∃ (j : Fin (n + 1))
      (_ : j ≠ i), f j = 0 := by
  simp [TopCat.horn]

lemma horn_le_toTopObj : TopCat.horn n i ⊆ ⦋n⦌.toTopObj := by
  simp [TopCat.horn]

def horn.ι : of (TopCat.horn n i) ⟶ of (⦋n⦌.toTopObj) :=
  ofHom ⟨fun ⟨x, hx⟩ ↦ ⟨x, horn_le_toTopObj i hx⟩, by continuity⟩

end

namespace horn

variable {n}

lemma continuous_min {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) :
    Continuous (fun (f : ι → ℝ≥0) ↦ (Finset.image f S).min' (by simpa)) := by
  sorry

variable (i : Fin (n + 2))

noncomputable def μ : (ToType ⦋n + 1⦌ → ℝ≥0) → ℝ≥0 :=
  fun f ↦ (Finset.image f ({i}ᶜ : Finset _)).min' (by
    rw [Finset.image_nonempty, ← Finset.coe_nonempty, Finset.coe_compl,
      Finset.coe_singleton]
    exact Set.nonempty_compl_of_nontrivial i)

@[continuity]
lemma continuous_μ : Continuous (μ i) :=
  continuous_min _ (by
    rw [← Finset.coe_nonempty, Finset.coe_compl,
      Finset.coe_singleton]
    exact Set.nonempty_compl_of_nontrivial i)

def v : ToType ⦋n + 1⦌ → ℝ≥0 :=
  fun j ↦ if j = i then 0 else 1

noncomputable def h : (ToType ⦋n + 1⦌ → ℝ≥0) × TopCat.I.{0} → (ToType ⦋n + 1⦌ → ℝ≥0) :=
  fun ⟨f, t⟩ ↦ f - (TopCat.I.toNNReal (TopCat.I.symm t) * μ i f) • v i

@[continuity]
lemma continuous_h : Continuous (horn.h i) :=
  continuous_pi (fun j ↦ by
    apply Continuous.sub
    · exact (continuous_apply j).comp continuous_fst
    · continuity)

lemma h₁ (f : ToType ⦋n + 1⦌ → ℝ≥0) :
    h i ⟨f, 1⟩ = f := by
  simp [h]
  aesop

def deformationRetracts_ι : TopCat.deformationRetracts (horn.ι i) := sorry

end horn

end TopCat

namespace SSet

instance (n : ℕ) : T2Space |Δ[n]| := ⦋n⦌.toTopHomeo.symm.t2Space

def horn.deformationRetracts_ToTopMap {n : ℕ} (i : Fin (n + 2)) :
    TopCat.deformationRetracts (toTop.map (horn (n + 1) i).ι) := by
  refine (deformationRetracts.arrow_mk_iso_iff ?_).2
    (horn.deformationRetracts_ι i)
  sorry

noncomputable def horn.deformationRetractToTopMap {n : ℕ} (i : Fin (n + 2)) :
    TopCat.DeformationRetract |horn (n + 1) i| |Δ[n + 1]| :=
  (horn.deformationRetracts_ToTopMap i).choose

@[simp]
lemma horn.deformationRetractToTopMap_i {n : ℕ} (i : Fin (n + 2)) :
    (horn.deformationRetractToTopMap i).i = toTop.map (horn (n + 1) i).ι :=
  (horn.deformationRetracts_ToTopMap i).choose_spec

@[reassoc (attr := simp)]
lemma horn.ι_deformationRetractToTopMap_r {n : ℕ} (i : Fin (n + 2)) :
    toTop.map (horn (n + 1) i).ι ≫ (horn.deformationRetractToTopMap i).r = 𝟙 _ := by
  simpa only [deformationRetractToTopMap_i]
    using (horn.deformationRetractToTopMap i).retract


instance (Z : TopCat.{0}) : IsFibrant (TopCat.toSSet.obj Z) := by
  rw [isFibrant_iff, fibration_iff]
  intro _ _ _ hi
  simp only [J, iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  constructor
  intro t _ sq
  refine ⟨⟨
    { l := sSetTopAdj.homEquiv _ _
        ((horn.deformationRetractToTopMap i).r ≫ (sSetTopAdj.homEquiv _ _).symm t)
      fac_left := by
        simp [← Adjunction.homEquiv_naturality_left]
      fac_right := Subsingleton.elim _ _ }⟩⟩

end SSet
