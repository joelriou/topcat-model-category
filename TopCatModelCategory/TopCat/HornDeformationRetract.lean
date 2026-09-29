module

public import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings

@[expose] public section

open CategoryTheory MorphismProperty TopCat Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen NNReal MonoidalCategory

universe u

lemma stdSimplex.subtypeMk_apply {X : Type*} [Fintype X]
    (f : X → ℝ) (hf : f ∈ stdSimplex ℝ X) (x : X) :
    (⟨f, hf⟩ : stdSimplex ℝ X) x = f x := rfl

namespace TopCat

variable (n : ℕ)

section

variable (i : Fin (n + 1))

protected def horn : Set (Fin (n + 1) → ℝ) :=
  (SSet.Subcomplex.toTopSet (SSet.stdSimplex.ιToTop.{0} n)).obj (SSet.horn.{0} n i)

variable {n}

lemma mem_horn_iff (f : Fin (n + 1) → ℝ) :
    f ∈ TopCat.horn n i ↔ f ∈ stdSimplex ℝ (Fin (n + 1)) ∧ ∃ (j : Fin (n + 1))
      (_ : j ≠ i), f j = 0 := by
  simp only [TopCat.horn, SSet.horn_eq_iSup, SSet.Subcomplex.toTopSet_iSup,
    SSet.stdSimplex.toTopSet_obj_face_singleton_compl]
  aesop

lemma mem_horn_iff' (f : stdSimplex ℝ (Fin (n + 1))) :
    f.1 ∈ TopCat.horn n i ↔ ∃ (j : Fin (n + 1))
      (_ : j ≠ i), f j = 0 := by
  rw [mem_horn_iff]
  aesop

lemma horn_le_toTopObj : TopCat.horn n i ⊆ stdSimplex ℝ (Fin (n + 1)) :=
  (SSet.Subcomplex.toTopSet_obj_subset _ _).trans (by simp)

def horn.ι : of (TopCat.horn n i) ⟶ of (stdSimplex ℝ (Fin (n + 1))) :=
  ofHom ⟨fun ⟨x, hx⟩ ↦ ⟨x, horn_le_toTopObj i hx⟩, by continuity⟩

end

namespace horn

variable {n}

lemma continuous_min {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) :
    Continuous (fun (f : ι → ℝ) ↦ (Finset.image f S).min' (by simpa)) := by
  classical
  revert S
  apply Finset.induction
  · simp
  · intro i₀ S hi₀ hα h'
    by_cases hS : S.Nonempty
    · let α (f : ι → ℝ) := (Finset.image f S).min' (by simpa)
      let β (f : ι → ℝ) : ℝ := min (α f) (f i₀)
      have hβ : Continuous β := by continuity
      have : β = fun (f : ι → ℝ) ↦ (Finset.image f (insert i₀ S)).min' (by simp) := by
        ext f
        dsimp [α, β]
        apply le_antisymm
        · simp only [Finset.image_insert, Finset.le_min'_iff, Finset.mem_insert, Finset.mem_image,
            inf_le_iff, forall_eq_or_imp, le_refl, or_true, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, true_and]
          intro i hi
          left
          apply Finset.min'_le
          aesop
        · simp only [Finset.image_insert, le_inf_iff, Finset.le_min'_iff, Finset.mem_image,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          constructor <;> intros <;> apply Finset.min'_le <;> aesop
      rwa [← this]
    · simp only [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      simp only [insert_empty_eq, Finset.image_singleton, Finset.min'_singleton]
      continuity

variable (i : Fin (n + 2))

lemma nonempty_image_singleton_compl (f : (ToType ⦋n + 1⦌ → ℝ)) :
    (Finset.image f ({i}ᶜ : Finset _)).Nonempty := by
  rw [Finset.image_nonempty, ← Finset.coe_nonempty, Finset.coe_compl,
    Finset.coe_singleton]
  exact Set.nonempty_compl_of_nontrivial i

noncomputable def μ : (ToType ⦋n + 1⦌ → ℝ) → ℝ :=
  fun f ↦ Finset.min' _ (nonempty_image_singleton_compl i f)

variable {i} in
lemma μ_le (f : ToType ⦋n + 1⦌ → ℝ) {j : ToType ⦋n + 1⦌} (hij : j ≠ i) :
    μ i f ≤ f j :=
  Finset.min'_le _ _ (by aesop)

@[continuity]
lemma continuous_μ : Continuous (μ i) :=
  continuous_min _ (by
    rw [← Finset.coe_nonempty, Finset.coe_compl,
      Finset.coe_singleton]
    exact Set.nonempty_compl_of_nontrivial i)

lemma exists_eq_μ (f : ToType ⦋n + 1⦌ → ℝ) :
    ∃ (j : Fin (n + 2)) (_ : j ≠ i), f j = μ i f := by
  have this := Finset.min'_mem _ (nonempty_image_singleton_compl i f)
  aesop

@[simp]
lemma μ_eq_zero (f : TopCat.horn (n + 1) i) :
    μ i (fun j ↦ f.1 j)= 0 := by
  dsimp [μ]
  apply le_antisymm
  · apply Finset.min'_le
    obtain ⟨f, hf⟩ := f
    rw [mem_horn_iff] at hf
    obtain ⟨_, ⟨j, hj, hj'⟩⟩ := hf
    simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_singleton]
    refine ⟨j, hj, by simpa⟩
  · simp only [Finset.le_min'_iff, Finset.mem_image, Finset.mem_compl, Finset.mem_singleton,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro j hj
    apply (horn_le_toTopObj _ f.2).1

-- FIXME: v(i) should be -(n + 1)...
def v : ToType ⦋n + 1⦌ → ℝ :=
  fun j ↦ if j = i then - (n + 1) else 1

variable {i} in
lemma v_eq_one {j : Fin (n + 2)} (hij : j ≠ i) : v i j = 1 :=
  if_neg hij

@[simp]
lemma v_eq : v i i = - (n + 1) := if_pos rfl

@[simp]
lemma sum_v : ∑ (j : Fin (n + 2)), v i j = 0 := by
  rw [← Finset.sum_compl_add_sum {i}, Finset.sum_singleton, v_eq, ← sub_eq_add_neg,
    sub_eq_zero, Finset.sum_congr rfl (g := fun _ ↦ 1)
      (fun j hj ↦ v_eq_one (by simpa using hj)),
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_compl, Fintype.card_fin,
    Finset.card_singleton, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one]

noncomputable def h' : (ToType ⦋n + 1⦌ → ℝ) × TopCat.I.{u} → (ToType ⦋n + 1⦌ → ℝ) :=
  fun ⟨f, t⟩ j ↦ f j - TopCat.I.toℝ (TopCat.I.symm t) * μ i f * v i j

@[simps! hom]
noncomputable def h : of (stdSimplex ℝ (Fin (n + 2))) ⊗ I ⟶ of (stdSimplex ℝ (Fin (n + 2))) :=
  ofHom ⟨fun ⟨f, t⟩ ↦ ⟨fun j ↦ f j - TopCat.I.toℝ (TopCat.I.symm t) * μ i f * v i j, by
    obtain ⟨j₀, hj₀, hj₀'⟩ := exists_eq_μ i f
    dsimp
    constructor
    · intro j
      by_cases hij : j = i
      · erw [← hj₀']
        subst hij
        dsimp
        rw [v_eq, mul_neg, sub_neg_eq_add]
        exact add_nonneg (by simp) (mul_nonneg (mul_nonneg (I.symm t).1.2.1 (by simp))
          (by positivity))
      · dsimp
        rw [v_eq_one hij, mul_one, sub_nonneg]
        refine le_trans ?_ (μ_le (fun k ↦ f.1 k) hij)
        refine mul_le_of_le_one_left ?_ (I.symm t).1.2.2
        rw [← hj₀']
        simp
    · simp only [Finset.sum_sub_distrib, stdSimplex.sum_eq_one, sub_eq_self,
        ← Finset.mul_sum, sum_v, mul_zero]⟩, by
      have (j : Fin (n + 2)) :
        Continuous (fun (x : stdSimplex ℝ (Fin (n + 2)) × I.{0}) ↦ x.1 j) :=
          (stdSimplex.continuous_eval _).comp (by continuity)
      continuity⟩

lemma hi (f : TopCat.horn (n + 1) i) (t : TopCat.I) (j : ToType ⦋n + 1⦌):
    h i ⟨⟨f.1, horn_le_toTopObj i f.2⟩, t⟩ j = f.1 j := by
  simp [h]
  dsimp [DFunLike.coe]
  simp [μ_eq_zero _ f]

noncomputable def r : of (stdSimplex ℝ (Fin (n + 2))) ⟶ of (TopCat.horn (n + 1) i) :=
  ofHom ⟨fun f ↦ ⟨h i ⟨f, 0⟩, by
    rw [mem_horn_iff]
    refine ⟨(h i ⟨f, 0⟩).2, ?_⟩
    obtain ⟨j, hij, hj⟩ := exists_eq_μ i f
    exact ⟨j, hij, by simp [stdSimplex.subtypeMk_apply, hj, v_eq_one hij]⟩⟩, by
      apply Continuous.subtype_mk
      exact Continuous.comp continuous_subtype_val (ι₀ ≫ h i).hom.2⟩

noncomputable def deformationRetractι : TopCat.DeformationRetract
    (of (TopCat.horn (n + 1) i)) (of (stdSimplex ℝ (Fin (n + 2)))) where
  i := horn.ι i
  h := h i
  r := r i
  retract := by ext : 3; apply hi
  hi := by ext : 3; apply hi
  h₀ := rfl
  h₁ := by
    ext x : 4
    dsimp
    rw [ι₁_apply]
    simp [stdSimplex.subtypeMk_apply]

def deformationRetracts_ι : TopCat.deformationRetracts (horn.ι i) :=
  ⟨deformationRetractι i, rfl⟩

end horn

end TopCat

namespace SSet

def horn.deformationRetracts_toTopMap {n : ℕ} (i : Fin (n + 2)) :
    TopCat.deformationRetracts (toTop.{u}.map (horn (n + 1) i).ι) := by
  refine (deformationRetracts.arrow_mk_iso_iff
    (toTop.mapArrow.mapIso (horn.arrowUliftIso.{u, 0} _ i))).1
      (toTopMap_ulift_deformationRetracts.{u} ?_)
  refine (deformationRetracts.arrow_mk_iso_iff ?_).2
    (horn.deformationRetracts_ι i)
  exact (SSet.Subcomplex.arrowMkToTopMapιIso (stdSimplex.hιToTop (n + 1))
    (horn (n + 1) i)) ≪≫ Arrow.isoMk (Iso.refl _)
      (Set.functorToTopCat.mapIso (eqToIso (by simp))) rfl

noncomputable def horn.deformationRetractToTopMap {n : ℕ} (i : Fin (n + 2)) :
    TopCat.DeformationRetract |horn (n + 1) i| |Δ[n + 1]| :=
  (horn.deformationRetracts_toTopMap i).choose

@[simp]
lemma horn.deformationRetractToTopMap_i {n : ℕ} (i : Fin (n + 2)) :
    (horn.deformationRetractToTopMap i).i = toTop.map (horn (n + 1) i).ι :=
  (horn.deformationRetracts_toTopMap i).choose_spec

@[reassoc (attr := simp)]
lemma horn.ι_deformationRetractToTopMap_r {n : ℕ} (i : Fin (n + 2)) :
    toTop.map (horn (n + 1) i).ι ≫ (horn.deformationRetractToTopMap i).r = 𝟙 _ := by
  simpa only [deformationRetractToTopMap_i]
    using (horn.deformationRetractToTopMap i).retract


instance (Z : TopCat.{u}) : IsFibrant (TopCat.toSSet.obj Z) := by
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

instance (X : SSet.{u}) : IsFibrant ((SSet.toTop ⋙ TopCat.toSSet).obj X) := by
  dsimp
  infer_instance

end SSet
