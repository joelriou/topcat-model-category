import TopCatModelCategory.TopCat.T1Inclusion

universe w w' t v u

open CategoryTheory HomotopicalAlgebra Topology

namespace CategoryTheory.MorphismProperty

variable  {C : Type u} [Category.{v, u} C] (W : MorphismProperty C)
  {J : Type w'} [LinearOrder J]
  [OrderBot J] [SuccOrder J] [WellFoundedLT J] {α : J → Type t}
  {A B : (j : J) → α j → C}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)

def RelativeCellComplex (_ : ∀ j i, W (basicCell j i)) {X Y : C} (f : X ⟶ Y) :=
    HomotopicalAlgebra.RelativeCellComplex.{w} basicCell f

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Types

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → Type u}
  {B : (j : J) → α j → Type u}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)

def RelativeMonoCellComplex (h) {X Y : Type u} (f : X ⟶ Y) :=
    MorphismProperty.RelativeCellComplex.{w}
      (MorphismProperty.monomorphisms (Type u)) basicCell h f

namespace RelativeMonoCellComplex

variable {basicCell} {h} {X₀ X : Type u}
  {f : X₀ ⟶ X} (hf : RelativeMonoCellComplex.{w} basicCell h f)

variable (c : hf.Cells)

def cell : Set X := Set.range c.ι

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    hf.boundaryCell c ⊆ hf.cell c := by
  dsimp only [boundaryCell, cell]
  grind

def boundaryCellCompl : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

end RelativeMonoCellComplex

end CategoryTheory.Types

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → TopCat.{u}}
  {B : (j : J) → α j → TopCat.{u}}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)

def RelativeT₁CellComplex (h) {X₀ X : TopCat.{u}} (f : X₀ ⟶ X) :=
  MorphismProperty.RelativeCellComplex.{w} t₁Inclusions basicCell h f

variable {basicCell} {h} {X₀ X : TopCat.{u}}
  {f : X₀ ⟶ X} (hf : RelativeT₁CellComplex.{w} basicCell h f)

namespace RelativeT₁CellComplex

include hf

def t₁InclusionsTransfiniteCompositionOfShape :
    t₁Inclusions.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
  map_mem j hj := by
    refine (?_ : _ ≤ (_ : MorphismProperty _)) _ (hf.attachCells j hj).pushouts_coproducts
    simp only [MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
    rintro _ _ _ ⟨i⟩
    apply h

lemma isT₁Inclusion : IsT₁Inclusion f :=
  t₁Inclusions.transfiniteCompositionsOfShape_le _ _
    hf.t₁InclusionsTransfiniteCompositionOfShape.mem

lemma isT₁Inclusion_incl_app (j : J) :
    IsT₁Inclusion (hf.incl.app j) :=
  hf.t₁InclusionsTransfiniteCompositionOfShape.mem_incl_app j

lemma isT₁Inclusion_map {i j : J} (g : i ⟶ j) :
    IsT₁Inclusion (hf.F.map g) :=
  hf.t₁InclusionsTransfiniteCompositionOfShape.mem_map g

variable (c : hf.Cells)

def cell : Set X := Set.range c.ι

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    hf.boundaryCell c ⊆ hf.cell c := by
  dsimp only [boundaryCell, cell]
  grind

def locallyClosedCell : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

end RelativeT₁CellComplex

end TopCat
