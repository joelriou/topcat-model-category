import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.CoconeNPrime
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators

open CategoryTheory Simplicial Opposite NNReal Limits

universe v u

variable {n m : SimplexCategory}

namespace SimplexCategory.toTopObj

@[simps]
def barycenter {α : Type*} [Fintype α] (p : α → n.toTopObj) (w : α → ℝ≥0)
    (hw : ∑ a, w a = 1) : n.toTopObj :=
  ⟨fun j ↦ ∑ (a : α), w a • p a j, by
    dsimp [toTopObj]
    rw [Finset.sum_comm]
    conv_rhs => rw [← hw]
    congr
    ext a
    have := (p a).2
    dsimp [toTopObj] at this
    rw [Subtype.ext_iff] at this
    simp only [val_eq_coe, coe_sum, coe_one] at this
    simp only [coe_sum, NNReal.coe_mul]
    rw [← Finset.mul_sum, this, mul_one]⟩

def vertex (i : Fin (n.len + 1)) : n.toTopObj :=
  ⟨fun j ↦ if j = i then 1 else 0, by simp [toTopObj]⟩

lemma eq_barycenter_vertex (x : n.toTopObj) :
    x = barycenter vertex x.1 x.2 := by
  ext
  simp [vertex, barycenter]

lemma exists_barycenter_vertex (x : n.toTopObj) :
    ∃ (w : Fin (n.len + 1) → ℝ≥0) (hw : ∑ a, w a = 1),
      x = barycenter vertex w hw :=
  ⟨_, _, eq_barycenter_vertex x⟩

variable (n) in
noncomputable def isobarycenter : n.toTopObj :=
  barycenter vertex (fun _ ↦ 1 / (n.len + 1)) (by simp)

@[simp]
lemma toTopMap_vertex (f : n ⟶ m) (i : Fin (n.len + 1)) :
    toTopMap f (vertex i) = vertex (f i) := by
  dsimp [toTopMap, vertex]
  aesop

@[simp]
lemma toTopMap_barycenter (g : n ⟶ m)
    {α : Type*} [Fintype α] (p : α → n.toTopObj) (w : α → ℝ≥0)
    (hw : ∑ a, w a = 1) :
    toTopMap g (barycenter p w hw) = barycenter (fun a ↦ toTopMap g (p a)) w hw := by
  ext i
  simp only [toTopMap, barycenter_coe, smul_eq_mul, coe_sum, NNReal.coe_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

variable {E : Type v} [AddCommGroup E] [Module ℝ E] (f : n.toTopObj → E)

def IsAffine : Prop :=
  ∀ (x : n.toTopObj), f x = ∑ (i : Fin (n.len + 1)), (x.1 i : ℝ) • f (vertex i)

abbrev affineMap (p : Fin (n.len + 1) → E) : n.toTopObj → E :=
  fun x ↦ ∑ (i : Fin (n.len + 1)), (x.1 i : ℝ) • p i

@[simp]
lemma affineMap_vertex (p : Fin (n.len + 1) → E) (i : Fin (n.len + 1)) :
    affineMap p (vertex i) = p i := by
  dsimp [affineMap, vertex]
  rw [Finset.sum_eq_single (a := i)]
  all_goals aesop

lemma isAffine_affineMap (p : Fin (n.len + 1) → E) :
    IsAffine (affineMap p) := by
  intro
  simp

namespace IsAffine

variable {f} (hf : IsAffine f)

include hf

lemma exists_eq :
    ∃ (p : Fin (n.len + 1) → E), f = affineMap p :=
  ⟨fun i ↦ f (vertex i), by ext; rw [hf]⟩

lemma map_barycenter {α : Type*} [Fintype α] (p : α → n.toTopObj) (w : α → ℝ≥0)
    (hw : ∑ a, w a = 1) : f (barycenter p w hw) = ∑ (a : α), w a • f (p a) := by
  obtain ⟨q, rfl⟩ := hf.exists_eq
  simp only [Finset.smul_sum, affineMap]
  rw [Finset.sum_comm]
  congr
  ext j
  simp only [barycenter, smul_eq_mul, coe_sum, NNReal.coe_mul, Finset.sum_smul, ← smul_assoc]
  rfl

lemma precomp (g : m ⟶ n) : IsAffine (f.comp (toTopMap g)) := by
  intro x
  obtain ⟨w, hw, rfl⟩ := exists_barycenter_vertex x
  dsimp
  simp only [toTopMap_barycenter, toTopMap_vertex, coe_sum, NNReal.coe_mul, hf.map_barycenter]
  congr
  ext a
  dsimp [vertex]
  rw [Finset.sum_eq_single (a := a)]
  all_goals aesop

lemma ext {g : n.toTopObj → E} (hg : IsAffine g)
    (h : ∀ (i : Fin (n.len + 1)), f (vertex i) = g (vertex i)) : f = g := by
  ext x
  rw [hf, hg]
  simp [h]

end IsAffine

end SimplexCategory.toTopObj

namespace SSet

variable {X : SSet.{u}} {E : Type v} [AddCommGroup E] [Module ℝ E]

section

variable (f : |X| → E)

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
  refine ⟨fun h ↦ ?_, fun h n x ↦ ?_⟩
  · ext ⟨n⟩ x
    simpa using h x
  · simp [← mem_isAffine_iff, h]

end

variable (X E)
structure AffineMap where
  f : |X| → E
  isAffine : IsAffine f

namespace AffineMap

variable {X E} (f : AffineMap X E)

noncomputable abbrev φ {d : SimplexCategory} (s : X.obj (op d)) : d.toTopObj → E :=
  IsAffineAt.φ f.f s

noncomputable def isobarycenter (s : X.S) : E :=
  f.φ s.simplex (SimplexCategory.toTopObj.isobarycenter _)

namespace b

noncomputable def affineMap (s : (B.obj X).N) : ⦋s.dim⦌.toTopObj → E :=
  (SimplexCategory.toTopObj.affineMap
    (fun i ↦ f.isobarycenter (s.simplex.obj i).toS))

lemma affineMap_comp {s t : (B.obj X).N} (hst : s ≤ t) :
    (affineMap f t).comp (SimplexCategory.toTopMap (N.monoOfLE hst)) =
      affineMap f s := by
  refine SimplexCategory.toTopObj.IsAffine.ext
    (SimplexCategory.toTopObj.IsAffine.precomp
      (SimplexCategory.toTopObj.isAffine_affineMap _) _)
    (SimplexCategory.toTopObj.isAffine_affineMap _) (fun i ↦ ?_)
  dsimp [affineMap]
  simp only [SimplexCategory.toTopObj.toTopMap_vertex, SimplexCategory.len_mk,
    SimplexCategory.toTopObj.affineMap_vertex, ← N.map_monoOfLE hst]
  rfl

noncomputable def coconeTypes :
    ((B.obj X).functorN' ⋙ toTop ⋙ forget TopCat).CoconeTypes where
  pt := E
  ι s := Function.comp (affineMap f s) ⦋s.dim⦌.toTopHomeo
  ι_naturality {s t} hst := by
    rw [← affineMap_comp f (leOfHom hst), Function.comp_assoc, Function.comp_assoc]
    apply congr_arg
    exact SimplexCategory.toTopHomeo_naturality (N.monoOfLE (leOfHom hst))

noncomputable def g : |B.obj X| → E :=
  ((Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨isColimitOfPreserves (toTop ⋙ forget _) (B.obj X).isColimitCoconeN'⟩).desc
      (coconeTypes f)

lemma comp_g_toTop_map (s : (B.obj X).N) :
    Function.comp (g f) (toTop.map (yonedaEquiv.symm s.simplex)) =
      Function.comp (affineMap f s) ⦋s.dim⦌.toTopHomeo := by
  dsimp
  exact
  ((Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨isColimitOfPreserves (toTop ⋙ forget _) (B.obj X).isColimitCoconeN'⟩).fac
      (coconeTypes f) s

lemma isAffineAtφ_g (s : (B.obj X).N) :
    IsAffineAt.φ (g f) s.simplex =
      SimplexCategory.toTopObj.affineMap
        (fun i ↦ f.isobarycenter (s.simplex.obj i).toS) := by
  dsimp [IsAffineAt.φ]
  rw [← Function.comp_assoc, ← Function.comp_assoc]
  erw [comp_g_toTop_map]
  dsimp only [affineMap]
  rw [Function.comp_assoc, Function.comp_assoc]
  convert Function.comp_id _
  dsimp [SimplexCategory.toTopHomeo]
  ext x : 1
  exact congr_arg ULift.down (congr_fun ((forget _).congr_map
    (toTopSimplex.{u}.inv_hom_id_app ⦋s.dim⦌)) (ULift.up x))

lemma isAffine_g : IsAffine (g f) := by
  rw [isAffine_iff_eq_top, Subcomplex.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  dsimp [SSet.isAffine, IsAffineAt]
  have := isAffineAtφ_g f (N.mk x hx)
  dsimp at this
  rw [this]
  exact SimplexCategory.toTopObj.isAffine_affineMap _

end b

noncomputable def b : AffineMap (B.obj X) E := ⟨_, b.isAffine_g f⟩

end AffineMap

end SSet
