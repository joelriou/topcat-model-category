import TopCatModelCategory.Convenient.GeneratedBy
import Mathlib.Topology.Sets.Opens

universe v v' t u

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]
  (Y : Type v) [TopologicalSpace Y]

namespace Topology.IsGeneratedBy

lemma of_isOpen [IsGeneratedBy X Y] {U : Set Y} (hU : IsOpen U) :
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

end Topology.IsGeneratedBy
