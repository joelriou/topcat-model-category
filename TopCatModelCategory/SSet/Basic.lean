import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-@[simps]
def const {X Y : SSet.{u}} (y : Y _[0]) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality n m f := by
    ext
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

@[reassoc (attr := simp)]
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _[0]) :
    f ≫ const z = const z := rfl

@[reassoc (attr := simp)]
lemma const_comp {X Y Z : SSet.{u}} (y : Y _[0]) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  ext m x
  simp [FunctorToTypes.naturality]-/

@[deprecated (since := "2025-03-19")]
alias yonedaEquiv_apply_comp := yonedaEquiv_comp

@[reassoc]
lemma stdSimplex.map_comp_yonedaEquiv_symm {X : SSet.{u}} {n m : SimplexCategory}
    (x : X.obj (op n)) (f : m ⟶ n) :
      stdSimplex.map f ≫ yonedaEquiv.symm x =
        yonedaEquiv.symm (X.map f.op x) := by
  apply yonedaEquiv.injective
  conv_rhs => rw [Equiv.apply_symm_apply, ← Category.id_comp f]
  rfl

@[reassoc]
lemma stdSimplex.δ_comp_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.δ i x) := by
  apply stdSimplex.map_comp_yonedaEquiv_symm

@[reassoc]
lemma stdSimplex.σ_comp_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    stdSimplex.σ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.σ i x) := by
  apply stdSimplex.map_comp_yonedaEquiv_symm

lemma yonedaEquiv_const {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv (const x : Δ[0] ⟶ X) = x := by
  simp [yonedaEquiv, yonedaCompUliftFunctorEquiv]

@[simp]
lemma yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv.symm x = const x := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]

protected abbrev evaluation : SimplexCategoryᵒᵖ ⥤ SSet.{u} ⥤ Type u :=
  evaluation _ _

end SSet
