import TopCatModelCategory.TopCat.Adj
import Mathlib.Analysis.Normed.Module.Basic

open CategoryTheory Simplicial Opposite

universe v u

namespace SimplexCategory.toTopObj

variable {n m : SimplexCategory}

def vertex (i : Fin (n.len + 1)) : n.toTopObj :=
  ⟨fun j ↦ if j = i then 1 else 0, by simp [toTopObj]⟩

@[simp]
lemma toTopMap_vertex (f : n ⟶ m) (i : Fin (n.len + 1)) :
    toTopMap f (vertex i) = vertex (f i) := by
  dsimp [toTopMap, vertex]
  aesop

variable {E : Type v} [AddCommGroup E] [Module ℝ E] (f : n.toTopObj → E)

def IsAffine : Prop :=
  ∀ (x : n.toTopObj), f x = ∑ (i : Fin (n.len + 1)), (x.1 i : ℝ) • f (vertex i)

end SimplexCategory.toTopObj

namespace SSet

variable {X : SSet.{u}} {E : Type v} [AddCommGroup E] [Module ℝ E]
  (f : |X| → E)

namespace IsAffineAt

noncomputable def map {n : SimplexCategory} (x : X.obj (op n)) : n.toTopObj → E :=
  f.comp (Function.comp
    (toTopSimplex.inv.app _ ≫ toTop.map (yonedaEquiv.symm x)) ULift.up)

end IsAffineAt

def IsAffineAt {n : SimplexCategory} (x : X.obj (op n)) : Prop :=
  SimplexCategory.toTopObj.IsAffine (IsAffineAt.map f x)

def IsAffine : Prop := ∀ ⦃n : SimplexCategory⦄ (x : X.obj (op n)), IsAffineAt f x

def isAffine : X.Subcomplex where
  obj := fun ⟨n⟩ ↦ setOf (fun x ↦ IsAffineAt f x)
  map := sorry

@[simp]
lemma mem_isAffine_iff {n : SimplexCategory} (x : X.obj (op n)) :
    x ∈ (isAffine f).obj _ ↔ IsAffineAt f x := Iff.rfl

lemma isAffine_iff_eq_top : IsAffine f ↔ isAffine f = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext ⟨n⟩ x
    simpa using h x
  · intro n x
    simp [← mem_isAffine_iff, h]

end SSet
