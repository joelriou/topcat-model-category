import TopCatModelCategory.AttachCells
import Mathlib.Order.SuccPred.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

--universe w t w' v u

open CategoryTheory Limits Category

/-namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
  (J : Type w') [LinearOrder J] [OrderBot J]
  {X Y : C} (f : X ⟶ Y)

structure TransfiniteCompositionOfShape [SuccOrder J] [WellFoundedLT J] where
  F : J ⥤ C
  isoBot : F.obj ⊥ ≅ X
  isWellOrderContinuous : F.IsWellOrderContinuous := by infer_instance
  incl : F ⟶ (Functor.const _).obj Y
  isColimit : IsColimit (Cocone.mk Y incl)
  fac : isoBot.inv ≫ incl.app ⊥ = f

variable [SuccOrder J] [WellFoundedLT J]

namespace TransfiniteCompositionOfShape

attribute [reassoc (attr := simp)] fac
attribute [instance] isWellOrderContinuous

variable (c : TransfiniteCompositionOfShape J f)

def arrowSucc (j : J) (_ : ¬ IsMax j) : Arrow C :=
  Arrow.mk (c.F.map (homOfLE (Order.le_succ j)))

-- generalize for initial segments...
@[simps]
def truncLE (j : J) : TransfiniteCompositionOfShape (Set.Iic j)
    (c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := c.F.restrictionLE j
  isoBot := c.isoBot
  incl := (c.F.coconeLE j).ι
  isColimit := c.F.isColimitCoconeLE j
  fac := rfl

variable (j : J)

end TransfiniteCompositionOfShape

end CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C} (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i)
  {X Y : C} (f : X ⟶ Y)

structure RelativeCellComplex
    extends TransfiniteCompositionOfShape J f where
  attachCells (j : J) (hj : ¬ IsMax j) : AttachCells (basicCell j)
    (F.map (homOfLE (Order.le_succ j)))

namespace RelativeCellComplex

variable {basicCell f} (c : RelativeCellComplex basicCell f)

structure Cells where
  j : J
  hj : ¬ IsMax j
  k : (c.attachCells j hj).ι

variable {c} in
def Cells.i (γ : Cells c) : α γ.j := (c.attachCells γ.j γ.hj).π γ.k

def cell (γ : Cells c) : B γ.j γ.i ⟶ Y :=
  (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

lemma hom_ext {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
    (h : ∀ (γ : Cells c), c.cell γ ≫ φ₁ = c.cell γ ≫ φ₂) :
    φ₁ = φ₂ := by
  refine c.isColimit.hom_ext (fun j ↦ ?_)
  dsimp
  induction j using SuccOrder.limitRecOn with
  | hm j hj =>
      obtain rfl := hj.eq_bot
      simpa [← cancel_epi c.isoBot.inv] using h₀
  | hs j hj hj' =>
      apply (c.attachCells j hj).hom_ext
      · simpa using hj'
      · intro i
        simpa only [assoc, cell] using h ({ hj := hj, k := i })
  | hl j hj hj' =>
      exact (c.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
        (fun ⟨k, hk⟩ ↦ by simpa using hj' k hk)

end RelativeCellComplex

end HomotopicalAlgebra-/

universe w t w' w''

namespace HomotopicalAlgebra

namespace RelativeCellComplex

variable {C : Type*} [Category C]
  {J : Type w'} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {α : J → Type t} {A B : ∀ (j : J), α j → C}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {J' : Type w''} [LinearOrder J'] [SuccOrder J'] [OrderBot J'] [WellFoundedLT J']
  {X Y : C} {f : X ⟶ Y}

def ofOrderIso (hf : RelativeCellComplex.{w} basicCell f) (e : J' ≃o J) :
    RelativeCellComplex.{w}
      (α := fun (j' : J') ↦ α (e j'))
      (fun _ i ↦ basicCell _ i) f where
  toTransfiniteCompositionOfShape :=
    hf.toTransfiniteCompositionOfShape.ofOrderIso e
  attachCells j hj :=
    (hf.attachCells (e j) (by simpa only [OrderIso.isMax_apply])).ofArrowIso
      (Arrow.isoMk (Iso.refl _)
        (hf.F.mapIso (eqToIso (OrderIso.map_succ e j).symm)) (by
          dsimp
          rw [id_comp, ← Functor.map_comp]
          rfl))

section
variable (hf : RelativeCellComplex.{w} basicCell f)
    {D : Type*} [Category D] (F : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J F] [PreservesColimitsOfShape J F]
    [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) F]
    [PreservesColimitsOfShape WalkingSpan F]

@[simps!]
noncomputable def map :
    RelativeCellComplex.{w} (fun j i ↦ F.map (basicCell j i)) (F.map f) where
  toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape.map F
  attachCells j hj := (hf.attachCells j hj).map F

@[simps]
def mapCellsEquiv : (hf.map F).Cells ≃ hf.Cells where
  toFun c :=
    { j := c.j
      hj := c.hj
      k := c.k }
  invFun c :=
    { j := c.j
      hj := c.hj
      k := c.k }

end

end RelativeCellComplex

end HomotopicalAlgebra
