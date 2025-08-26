import TopCatModelCategory.SSet.NonDegenerateSimplices

universe u

open Simplicial CategoryTheory

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

end SSet
