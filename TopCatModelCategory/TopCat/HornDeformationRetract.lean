import TopCatModelCategory.TopCat.Adj

open CategoryTheory MorphismProperty TopCat Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen NNReal MonoidalCategory

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

lemma nonempty_image_singleton_compl (f : (ToType ⦋n + 1⦌ → ℝ≥0)) :
    (Finset.image f ({i}ᶜ : Finset _)).Nonempty := by
  rw [Finset.image_nonempty, ← Finset.coe_nonempty, Finset.coe_compl,
    Finset.coe_singleton]
  exact Set.nonempty_compl_of_nontrivial i

noncomputable def μ : (ToType ⦋n + 1⦌ → ℝ≥0) → ℝ≥0 :=
  fun f ↦ Finset.min' _ (nonempty_image_singleton_compl i f)

@[continuity]
lemma continuous_μ : Continuous (μ i) :=
  continuous_min _ (by
    rw [← Finset.coe_nonempty, Finset.coe_compl,
      Finset.coe_singleton]
    exact Set.nonempty_compl_of_nontrivial i)

lemma exists_eq_μ (f : ToType ⦋n + 1⦌ → ℝ≥0) :
    ∃ (j : Fin (n + 2)) (_ : j ≠ i), f j = μ i f := by
  have this := Finset.min'_mem _ (nonempty_image_singleton_compl i f)
  aesop

@[simp]
lemma μ_eq_zero (f : TopCat.horn (n + 1) i) :
    μ i f = 0 := by
  dsimp [μ]
  apply le_antisymm
  · apply Finset.min'_le
    obtain ⟨f, hf⟩ := f
    rw [mem_horn_iff] at hf
    obtain ⟨_, ⟨j, hj, hj'⟩⟩ := hf
    simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_singleton]
    exact ⟨j, hj, hj'⟩
  · simp

-- FIXME: v(i) should be -(n + 1)...
def v : ToType ⦋n + 1⦌ → ℝ≥0 :=
  fun j ↦ if j = i then 0 else 1

variable {i} in
lemma v_eq_one {j : Fin (n + 2)} (hij : j ≠ i) : v i j = 1 :=
  if_neg hij

noncomputable def h' : (ToType ⦋n + 1⦌ → ℝ≥0) × TopCat.I.{0} → (ToType ⦋n + 1⦌ → ℝ≥0) :=
  fun ⟨f, t⟩ ↦ f - (TopCat.I.toNNReal (TopCat.I.symm t) * μ i f) • v i

@[continuity]
lemma continuous_h' : Continuous (horn.h' i) :=
  continuous_pi (fun j ↦ by
    apply Continuous.sub
    · exact (continuous_apply j).comp continuous_fst
    · continuity)

@[simp]
lemma h'₁ (f : ToType ⦋n + 1⦌ → ℝ≥0) :
    h' i ⟨f, 1⟩ = f := by
  ext
  simp [h']

lemma hi' (f : TopCat.horn (n + 1) i) (t : TopCat.I) :
    h' i ⟨f, t⟩ = f := by
  ext
  simp [h']

@[simp]
noncomputable def h'' : ⦋n + 1⦌.toTopObj × TopCat.I.{0} → (ToType ⦋n + 1⦌ → ℝ≥0) :=
  fun ⟨f, t⟩ ↦ h' i ⟨f.1, t⟩

@[continuity]
lemma continuous_h'' : Continuous (horn.h'' i) := by
  let g : ⦋n + 1⦌.toTopObj × TopCat.I.{0} → (ToType ⦋n + 1⦌ → ℝ≥0) × TopCat.I.{0}  :=
    fun x ↦ ⟨x.1.1, x.2⟩
  have hg : Continuous g := by
    rw [continuous_prodMk]
    exact ⟨Continuous.fst' continuous_subtype_val, continuous_snd⟩
  exact (continuous_h' i).comp hg

@[simps! hom]
noncomputable def h : of ⦋n + 1⦌.toTopObj ⊗ I ⟶ of ⦋n + 1⦌.toTopObj :=
  ofHom ⟨fun x ↦ ⟨h'' i x, by
    sorry⟩, by
    apply Continuous.subtype_mk
    apply continuous_h''⟩

noncomputable def r : of ⦋n + 1⦌.toTopObj ⟶ of (TopCat.horn (n + 1) i) :=
  ofHom ⟨fun f ↦ ⟨h'' i ⟨f, 0⟩, by
    rw [mem_horn_iff]
    refine ⟨(h i ⟨f, 0⟩).2, ?_⟩
    obtain ⟨j, hij, hj⟩ := exists_eq_μ i f
    exact ⟨j, hij, by simp [h', hj, v_eq_one hij]⟩⟩, by
      apply Continuous.subtype_mk
      let g : ⦋n + 1⦌.toTopObj → ⦋n + 1⦌.toTopObj × I.{0} :=
        fun x ↦ ⟨x, 0⟩
      have hg : Continuous g := by continuity
      exact (continuous_h'' i).comp hg⟩

noncomputable def deformationRetractι : TopCat.DeformationRetract
    (of (TopCat.horn (n + 1) i)) (of ⦋n + 1⦌.toTopObj) where
  i := horn.ι i
  h := h i
  r := r i
  retract := by
    ext f : 2
    apply hi'
  hi := by
    ext ⟨f, t⟩ : 2
    apply hi'
  h₀ := rfl
  h₁ := by
    ext x : 2
    dsimp
    rw [ι₁_apply]
    simp

def deformationRetracts_ι : TopCat.deformationRetracts (horn.ι i) :=
  ⟨deformationRetractι i, rfl⟩

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
