import TopCatModelCategory.Convenient.GeneratedBy
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Homeomorph.Lemmas

universe v v' t u

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]
  (Y : Type v) [TopologicalSpace Y]

open IsGeneratedBy

noncomputable def Topology.IsOpenEmbedding.homeoRange {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) :
    X ≃ₜ Set.range f :=
  IsHomeomorph.homeomorph (f := fun x ↦ ⟨f x, Set.mem_range_self x⟩)
    { continuous := hf.continuous.subtype_mk _
      isOpenMap := by
        rw [hf.isOpen_range.isOpenEmbedding_subtypeVal.isOpenMap_iff]
        exact hf.isOpenMap
      bijective :=
        ⟨fun _ _ h ↦ hf.injective (by rwa [Subtype.ext_iff] at h), fun x ↦ by aesop⟩ }

@[simp]
noncomputable def Topology.IsOpenEmbedding.apply_homeoRange_symm {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) (x : Set.range f) :
    f (hf.homeoRange.symm x) = x.1 := by
  obtain ⟨x, rfl⟩ := hf.homeoRange.surjective x
  rw [Homeomorph.symm_apply_apply]
  rfl

lemma IsOpen.isGeneratedBy [IsGeneratedBy X Y] {U : Set Y} (hU : IsOpen U) :
    IsGeneratedBy X U := by
  let α := Σ (i : ι), C(X i, Y)
  let W (a : α) : TopologicalSpace.Opens (X a.1) :=
    ⟨a.2 ⁻¹' U, a.2.continuous.isOpen_preimage U hU⟩
  let g (a : α) : W a → U := U.restrictPreimage a.2
  have hg (a : α) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set U), (∀ (a : α), IsOpen ((g a) ⁻¹' V)) → IsOpen V by
    constructor
    rw [continuous_def]
    intro V hV
    exact this _ (fun a ↦ ((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2
      (hg a)).isOpen_preimage _ hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ U ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine continuous_subtype_val.isOpen_preimage _ ?_
  rw [isOpen_iff X]
  intro i f
  convert (W ⟨i, f⟩).isOpen.isOpenMap_subtype_val _ (hV ⟨i, f⟩)
  aesop

lemma Topology.IsOpenEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {U : Type*} [TopologicalSpace U] {f : U → Y}
    {hf : IsOpenEmbedding f} :
    IsGeneratedBy X U := by
  have := hf.isOpen_range.isGeneratedBy (X := X)
  exact hf.homeoRange.symm.isQuotientMap.isGeneratedBy
