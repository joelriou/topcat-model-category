import TopCatModelCategory.Convenient.GeneratedBy
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Homeomorph.Lemmas

universe v v' t u

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ (i : ι) (U : TopologicalSpace.Closeds (X i)), IsGeneratedBy X U]
  (Y : Type v) [TopologicalSpace Y]

open IsGeneratedBy

noncomputable def Topology.IsClosedEmbedding.homeoRange {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    X ≃ₜ Set.range f :=
  IsEmbedding.toHomeomorph hf.toIsEmbedding

@[simp]
noncomputable def Topology.IsClosedEmbedding.apply_homeoRange_symm
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) (x : Set.range f) :
    f (hf.homeoRange.symm x) = x.1 := by
  obtain ⟨x, rfl⟩ := hf.homeoRange.surjective x
  rw [Homeomorph.symm_apply_apply]
  rfl

lemma IsClosed.isGeneratedBy [IsGeneratedBy X Y] {F : Set Y} (hF : IsClosed F) :
    IsGeneratedBy X F := by
  let α := Σ (i : ι), C(X i, Y)
  let W (a : α) : TopologicalSpace.Closeds (X a.1) :=
    ⟨a.2 ⁻¹' F, IsClosed.preimage a.2.continuous hF⟩
  let g (a : α) : W a → F := F.restrictPreimage a.2
  have hg (a : α) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set F), (∀ (a : α), IsClosed ((g a) ⁻¹' V)) → IsClosed V by
    constructor
    rw [continuous_iff_isClosed]
    intro V hV
    exact this _ (fun a ↦ IsClosed.preimage
      (((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2 (hg a))) hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ F ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine IsClosed.preimage continuous_subtype_val ?_
  rw [isClosed_iff X]
  intro i f
  convert (W ⟨i, f⟩).isClosed.isClosedMap_subtype_val _ (hV ⟨i, f⟩)
  aesop

lemma Topology.IsClosedEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {U : Type*} [TopologicalSpace U] {f : U → Y}
    {hf : IsClosedEmbedding f} :
    IsGeneratedBy X U := by
  have := hf.isClosed_range.isGeneratedBy (X := X)
  exact hf.homeoRange.symm.isQuotientMap.isGeneratedBy
