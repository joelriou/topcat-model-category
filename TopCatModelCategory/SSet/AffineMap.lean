import TopCatModelCategory.TopCat.Adj
import Mathlib.Analysis.Normed.Module.Basic

open CategoryTheory Simplicial Opposite

universe v u

variable {n m : SimplexCategory}

namespace SimplexCategory.toTopObj

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

namespace IsAffine

variable {f}
lemma precomp (hf : IsAffine f) (g : m ⟶ n) : IsAffine (f.comp (toTopMap g)) := by
  sorry

end IsAffine

end SimplexCategory.toTopObj

namespace SSet

variable {X : SSet.{u}} {E : Type v} [AddCommGroup E] [Module ℝ E]
  (f : |X| → E)

namespace IsAffineAt

noncomputable def φ (x : X.obj (op n)) : n.toTopObj → E :=
  f.comp (Function.comp
    (toTopSimplex.inv.app _ ≫ toTop.map (yonedaEquiv.symm x)) ULift.up)

omit [AddCommGroup E] [Module ℝ E] in
lemma precomp_φ {n : SimplexCategory} (x : X.obj (op n)) (g : m ⟶ n) :
    φ f (X.map g.op x) = φ f x ∘ SimplexCategory.toTopMap g := by
  dsimp only [φ]
  rw [SSet.yonedaEquiv_symm_map]
  dsimp
  simp only [Functor.map_comp, TopCat.hom_comp, ContinuousMap.coe_comp, Function.comp_assoc]
  apply congr_arg
  apply congr_arg
  ext x
  exact ConcreteCategory.congr_hom
    (toTopSimplex.{u}.inv.naturality g).symm (ULift.up x)

end IsAffineAt

def IsAffineAt {n : SimplexCategory} (x : X.obj (op n)) : Prop :=
  SimplexCategory.toTopObj.IsAffine (IsAffineAt.φ f x)

variable {f} in
lemma IsAffineAt.map {n m : SimplexCategory} {x : X.obj (op n)}
    (hx : IsAffineAt f x) (g : m ⟶ n) :
    IsAffineAt f (X.map g.op x) := by
  dsimp [IsAffineAt] at hx ⊢
  rw [precomp_φ]
  exact hx.precomp g

def IsAffine : Prop := ∀ ⦃n : SimplexCategory⦄ (x : X.obj (op n)), IsAffineAt f x

def isAffine : X.Subcomplex where
  obj := fun ⟨_⟩ ↦ setOf (fun x ↦ IsAffineAt f x)
  map _ _ hx := hx.map _

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
