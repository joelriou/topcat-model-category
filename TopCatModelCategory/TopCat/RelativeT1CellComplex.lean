import TopCatModelCategory.TopCat.T1Inclusion

universe w w' t v u

open CategoryTheory HomotopicalAlgebra Topology

namespace TopCat

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄}
  {b : X₃ ⟶ X₄} (sq : IsPushout t l r b)

end TopCat

namespace CategoryTheory.Types

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → Type u}
  {B : (j : J) → α j → Type u}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}

namespace RelativeInjectiveCellComplex

variable {h} {X₀ X : Type u}
  {f : X₀ ⟶ X} {hf : RelativeCellComplex.{w} basicCell f}
  (h : ∀ j i, Function.Injective (basicCell j i))

variable (c : hf.Cells)

def cell : Set X := Set.range c.ι

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    boundaryCell c ⊆ cell c := by
  dsimp only [boundaryCell, cell]
  grind

def boundaryCellCompl : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

end RelativeInjectiveCellComplex

end CategoryTheory.Types

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → TopCat.{u}}
  {B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X₀ X : TopCat.{u}} {f : X₀ ⟶ X}
  (hf : RelativeCellComplex.{w} basicCell f)
  (h : ∀ j i, t₁Inclusions (basicCell j i))

namespace RelativeT₁CellComplex

include hf

section

include h

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
    (t₁InclusionsTransfiniteCompositionOfShape hf h).mem

lemma isT₁Inclusion_incl_app (j : J) :
    IsT₁Inclusion (hf.incl.app j) :=
  (t₁InclusionsTransfiniteCompositionOfShape hf h).mem_incl_app j

lemma isT₁Inclusion_map {i j : J} (g : i ⟶ j) :
    IsT₁Inclusion (hf.F.map g) :=
  (t₁InclusionsTransfiniteCompositionOfShape hf h).mem_map g

end

variable {hf} (c : hf.Cells)

def cell : Set X := Set.range c.ι

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    boundaryCell c ⊆ cell c := by
  dsimp only [boundaryCell, cell]
  grind

def locallyClosedCell : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

end RelativeT₁CellComplex

end TopCat
