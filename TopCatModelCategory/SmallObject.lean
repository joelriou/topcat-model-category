module

public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

@[expose] public section

universe w v u

open HomotopicalAlgebra

namespace CategoryTheory.SmallObject

variable {C : Type u} [Category.{v} C] {I : MorphismProperty C}

lemma exists_retract_relativeCellComplex_of_llp_rlp
    {X Y : C} {f : X ⟶ Y} (hp : I.rlp.llp f)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.toType]
    [I.IsCardinalForSmallObjectArgument κ] :
    ∃ (Y' : C) (r : Retract Y Y') (f' : X ⟶ Y') (_ : f ≫ r.i = f'),
      Nonempty (RelativeCellComplex.{w} (fun (_ : κ.ord.toType) => I.homFamily) f') := by
  have := hp _ (rlp_πObj I κ f)
  let ρ := RetractArrow.ofLeftLiftingProperty (ιObj_πObj I κ f)
  have fac : f ≫ ρ.i.right = ιObj I κ f := by
    have this : _ = 𝟙 X ≫ _ := ρ.i.w.symm
    rwa [Category.id_comp] at this
  refine ⟨obj I κ f, { i := ρ.i.right, r := πObj I κ f, retract := ρ.right.retract },
    ιObj I κ f, fac, ⟨relativeCellComplexιObj I κ f⟩⟩

lemma exists_retractArrow_relativeCellComplex_of_llp_rlp
    {X Y : C} {f : X ⟶ Y} (hp : I.rlp.llp f)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.toType]
    [I.IsCardinalForSmallObjectArgument κ] :
    ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : RetractArrow f f'),
      Nonempty (RelativeCellComplex.{w} (fun (_ : κ.ord.toType) => I.homFamily) f') := by
  obtain ⟨Y', r, f', fac, ⟨hf'⟩⟩ := exists_retract_relativeCellComplex_of_llp_rlp hp κ
  exact ⟨_, _, f', { i := Arrow.homMk (𝟙 X) r.i, r := Arrow.homMk (𝟙 X) r.r }, ⟨hf'⟩⟩

end CategoryTheory.SmallObject
