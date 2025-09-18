import TopCatModelCategory.SSet.NonDegenerateSimplices

universe u

open Simplicial CategoryTheory Limits

namespace SSet

variable (X : SSet.{u})

protected abbrev Nonempty : Prop := _root_.Nonempty (X _⦋0⦌)

instance (n : SimplexCategoryᵒᵖ) [X.Nonempty] : Nonempty (X.obj n) :=
  ⟨X.map (SimplexCategory.const n.unop ⦋0⦌ 0).op (Classical.arbitrary _)⟩

instance [X.Nonempty] : Nonempty X.N := ⟨N.mk (n := 0) (Classical.arbitrary _) (by simp)⟩

instance [X.Nonempty] : Nonempty X.S := ⟨S.mk (dim := 0) (Classical.arbitrary _)⟩

instance (T : Type u) [Preorder T] [Nonempty T] : (nerve T).Nonempty :=
  ⟨.mk₀ (Classical.arbitrary _)⟩

variable {X} in
lemma nonempty_of_hom {Y : SSet.{u}} (f : Y ⟶ X) [Y.Nonempty] : X.Nonempty :=
  ⟨f.app _ (Classical.arbitrary _)⟩

instance (n : SimplexCategory) : (stdSimplex.obj n).Nonempty :=
  ⟨stdSimplex.objEquiv.symm (SimplexCategory.const _ _ 0)⟩

lemma notNonempty_iff_hasDimensionLT_zero :
    ¬ X.Nonempty ↔ X.HasDimensionLT 0 := by
  simp only [not_nonempty_iff]
  refine ⟨fun _ ↦ ⟨fun n hn ↦ ?_⟩, fun _ ↦ ⟨fun x ↦ ?_⟩⟩
  · have := Function.isEmpty (X.map (⦋0⦌.const ⦋n⦌ 0).op)
    ext x
    exact isEmptyElim x
  · exact (lt_self_iff_false _).1
      (X.dim_lt_of_nondegenerate ⟨x, by simp⟩ 0)

variable {X} in
def isInitialOfNotNonempty (hX : ¬ X.Nonempty) : IsInitial X := by
  simp only [not_nonempty_iff] at hX
  have (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    Function.isEmpty (X.map (⦋0⦌.const n.unop 0).op)
  exact IsInitial.ofUniqueHom (fun Y ↦
    { app _ x := isEmptyElim x
      naturality _ _ _  := by ext x; exact isEmptyElim x })
    (fun _ _ ↦ by ext _ x; exact isEmptyElim x)

end SSet
