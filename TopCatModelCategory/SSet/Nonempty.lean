import TopCatModelCategory.SSet.NonDegenerateSimplices

universe u

open Simplicial

namespace SSet

variable (X : SSet.{u})

protected abbrev Nonempty : Prop := _root_.Nonempty (X _⦋0⦌)

instance (n : SimplexCategoryᵒᵖ) [X.Nonempty] : Nonempty (X.obj n) :=
  ⟨X.map (SimplexCategory.const n.unop ⦋0⦌ 0).op (Classical.arbitrary _)⟩

instance [X.Nonempty] : Nonempty X.N := ⟨N.mk (n := 0) (Classical.arbitrary _) (by simp)⟩

instance [X.Nonempty] : Nonempty X.S := ⟨S.mk (dim := 0) (Classical.arbitrary _)⟩

end SSet
