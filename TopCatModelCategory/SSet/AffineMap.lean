import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.CoconeNPrime
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Module.BigOperators

open CategoryTheory Simplicial Opposite NNReal Limits

universe v u

namespace SSet

def vertexOfSimplex {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) (i : Fin (n.len + 1)) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ n i).op x

lemma vertexOfSimplex_map {X : SSet.{u}} {m n : SimplexCategory}
    (x : X.obj (op n)) (f : m ⟶ n) (i : Fin (m.len + 1)) :
    vertexOfSimplex (X.map f.op x) i = vertexOfSimplex x (f i) := by
  dsimp [vertexOfSimplex]
  rw [← FunctorToTypes.map_comp_apply]
  rfl

end SSet

variable {n m : SimplexCategory}

namespace SimplexCategory.toTopObj

@[continuity]
lemma continuous_eval (i : ToType n) :
    Continuous (fun (x : n.toTopObj) ↦ x.1 i) :=
  (continuous_apply i).comp continuous_subtype_val

@[simp]
lemma sum_coe_eq_one (a : n.toTopObj) :
    ∑ (i : Fin (n.len + 1)), (a i : ℝ) = 1 := by
  rw [← NNReal.coe_sum, a.2, coe_one]

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

lemma continuous_affineMap {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Fin (n.len + 1) → E) :
    Continuous (affineMap p) := by
  continuity

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

lemma map (g : m ⟶ n) : IsAffine (f.comp (toTopMap g)) := by
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

lemma convex_range : Convex ℝ (Set.range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb h
  refine ⟨⟨fun i ↦ ⟨a * ↑(x i) + b * ↑(y i), ?_⟩, ?_⟩, ?_⟩
  · positivity
  · ext
    simp [toTopObj, Finset.sum_add_distrib, ← Finset.mul_sum, h]
  · obtain ⟨p, rfl⟩ := hf.exists_eq
    simp [affineMap, Finset.smul_sum, add_smul, Finset.sum_add_distrib, ← smul_assoc]

lemma map_barycenter_mem_of_convex
    {α : Type*} [Fintype α] (p : α → n.toTopObj) (w : α → ℝ≥0) (hw : ∑ a, w a = 1)
    {S : Set E} (hS : Convex ℝ S) (hq : ∀ (a : α), f (p a) ∈ S) :
    f (barycenter p w hw) ∈ S := by
  rw [hf.map_barycenter]
  exact hS.sum_mem (by simp) (by simp [← NNReal.coe_sum, hw]) (by tauto)

lemma range_subset_iff_of_convex {F : Set E} (hF : Convex ℝ F) :
    Set.range f ⊆ F ↔ ∀ i, f (vertex i) ∈ F := by
  have := hf
  refine ⟨fun h i ↦ h (by simp), fun h ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, hw, rfl⟩ := exists_barycenter_vertex x
  exact hf.map_barycenter_mem_of_convex _ _ _ hF h

lemma range_eq_convexHull :
    Set.range f = convexHull ℝ (Set.range (fun i ↦ f (vertex i))) := by
  apply subset_antisymm
  · rw [hf.range_subset_iff_of_convex (convex_convexHull _ _)]
    intro i
    exact subset_convexHull _ _ (by simp)
  · rw [(hf.convex_range).convexHull_subset_iff]
    grind

omit hf

lemma continuous {F : Type v} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (f : n.toTopObj → F) (hf : IsAffine f) :
    Continuous f := by
  obtain ⟨p, rfl⟩ := hf.exists_eq
  exact continuous_affineMap p

end IsAffine

end SimplexCategory.toTopObj

namespace SSet

variable {X Y : SSet.{u}} {E : Type v}

section

variable (f : |X| → E)

namespace IsAffineAt

noncomputable def φ (x : X.obj (op n)) : n.toTopObj → E :=
  f.comp (Function.comp
    (toTopSimplex.inv.app _ ≫ toTop.map (yonedaEquiv.symm x)) ULift.up)

lemma precomp_φ (g : Y ⟶ X) (y : Y.obj (op n)) :
    φ (f.comp (toTop.map g).hom) y = φ f (g.app _ y) := by
  dsimp [φ]
  rw [Function.comp_assoc, ← yonedaEquiv_symm_comp, Functor.map_comp]
  rfl

lemma map_φ {n : SimplexCategory} (x : X.obj (op n)) (g : m ⟶ n) :
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

variable [AddCommGroup E] [Module ℝ E]

def IsAffineAt {n : SimplexCategory} (x : X.obj (op n)) : Prop :=
  SimplexCategory.toTopObj.IsAffine (IsAffineAt.φ f x)

variable {f} in
lemma IsAffineAt.map {n m : SimplexCategory} {x : X.obj (op n)}
    (hx : IsAffineAt f x) (g : m ⟶ n) :
    IsAffineAt f (X.map g.op x) := by
  dsimp [IsAffineAt] at hx ⊢
  rw [map_φ]
  exact hx.map g

lemma IsAffineAt.precomp {y : Y.obj (op n)} {g : Y ⟶ X} (hy : IsAffineAt f (g.app _ y)) :
    IsAffineAt (f.comp (toTop.map g).hom) y := by
  dsimp [IsAffineAt] at hy ⊢
  rw [precomp_φ]
  assumption

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

variable [AddCommGroup E] [Module ℝ E]

variable (X E)
structure AffineMap where
  f : |X| → E
  isAffine : IsAffine f

namespace AffineMap

variable {X E} (f : AffineMap X E)

noncomputable abbrev φ {d : SimplexCategory} (s : X.obj (op d)) : d.toTopObj → E :=
  IsAffineAt.φ f.f s

lemma continuous_φ {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AffineMap X E)
    {n : SimplexCategory} (x : X.obj (op n)) : Continuous (f.φ x) :=
  (f.isAffine x).continuous

lemma map_φ {d e : SimplexCategory} (s : X.obj (op d)) (g : e ⟶ d) :
    f.φ (X.map g.op s) = f.φ s ∘ SimplexCategory.toTopMap g := by
  simp [IsAffineAt.map_φ]

lemma range_subset_of_le {s t : X.S} (hst : s ≤ t) :
    Set.range (f.φ s.simplex) ⊆ Set.range (f.φ t.simplex) := by
  obtain ⟨d, s, rfl⟩ := s.mk_surjective
  obtain ⟨e, t, rfl⟩ := t.mk_surjective
  rw [S.le_iff, Subpresheaf.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff] at hst
  dsimp at hst ⊢
  obtain ⟨g, rfl⟩ := hst
  rw [map_φ]
  grind

noncomputable def isobarycenter (s : X.S) : E :=
  f.φ s.simplex (SimplexCategory.toTopObj.isobarycenter _)

lemma range_φ_subset_range_f (s : X.S) :
    Set.range (f.φ s.simplex) ⊆ Set.range f.f := by
  dsimp [φ, IsAffineAt.φ]
  grind

lemma range_f_eq' :
    Set.range f.f = ⋃ (s : X.S), Set.range (f.φ s.simplex) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨⟨n⟩, s⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (toTop ⋙ forget _)
      (X.isColimitCoconeFromElementsOp)) x
    induction' n using SimplexCategory.rec with n
    dsimp at x ⊢
    obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso (toTopSimplex.{u}.app ⦋n⦌)).toEquiv.symm.surjective x
    simp only [Set.mem_iUnion]
    exact ⟨S.mk s, ULift.down x, rfl⟩
  · simpa only [Set.iUnion_subset_iff] using f.range_φ_subset_range_f

lemma range_f_eq :
    Set.range f.f = ⋃ (s : X.N), Set.range (f.φ s.simplex) := by
  rw [range_f_eq']
  apply subset_antisymm
  · simp only [Set.iUnion_subset_iff]
    intro s
    refine le_trans ?_ (le_iSup _ s.toN)
    exact f.range_subset_of_le s.self_le_toS_toN
  · simp only [Set.iUnion_subset_iff]
    intro s
    exact le_trans (by rfl) (le_iSup _ s.toS)

noncomputable def precomp (g : Y ⟶ X) : AffineMap Y E where
  f := Function.comp f.f (toTop.map g).hom
  isAffine _ y := (f.isAffine (g.app _ y)).precomp

@[simp]
lemma precomp_φ (g : Y ⟶ X) {d : SimplexCategory} (y : Y.obj (op d)) :
    (f.precomp g).φ y = f.φ (g.app _ y) :=
  IsAffineAt.precomp_φ f.f g y

namespace b

noncomputable def affineMap (s : (B.obj X).N) : ⦋s.dim⦌.toTopObj → E :=
  (SimplexCategory.toTopObj.affineMap
    (fun i ↦ f.isobarycenter (s.simplex.obj i).toS))

lemma isAffine_affineMap (s : (B.obj X).N) :
    SimplexCategory.toTopObj.IsAffine (affineMap f s) :=
  SimplexCategory.toTopObj.isAffine_affineMap _

lemma affineMap_comp {s t : (B.obj X).N} (hst : s ≤ t) :
    (affineMap f t).comp (SimplexCategory.toTopMap (N.monoOfLE hst)) =
      affineMap f s := by
  refine SimplexCategory.toTopObj.IsAffine.ext
    (SimplexCategory.toTopObj.IsAffine.map
      (SimplexCategory.toTopObj.isAffine_affineMap _) _)
    (SimplexCategory.toTopObj.isAffine_affineMap _) (fun i ↦ ?_)
  dsimp [affineMap]
  simp only [SimplexCategory.toTopObj.toTopMap_vertex, SimplexCategory.len_mk,
    SimplexCategory.toTopObj.affineMap_vertex, ← N.map_monoOfLE hst]
  rfl

lemma range_affineMap_le (s : (B.obj X).N) (t : X.N) (hs : s.simplex.obj (Fin.last _) ≤ t) :
    Set.range (affineMap f s) ⊆ Set.range (f.φ t.simplex) := by
  rw [(isAffine_affineMap f s).range_subset_iff_of_convex
    (f.isAffine t.simplex).convex_range]
  intro i
  dsimp only [affineMap]
  rw [SimplexCategory.toTopObj.affineMap_vertex]
  exact (f.isAffine (s.simplex.obj i).simplex).map_barycenter_mem_of_convex _ _ _
    (f.isAffine t.simplex).convex_range
    (fun a ↦ f.range_subset_of_le ((s.simplex.monotone i.le_last).trans hs) (by simp))

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

lemma b_φ (s : (B.obj X).N) :
    f.b.φ s.simplex = b.affineMap f s :=
  b.isAffineAtφ_g _ _

lemma range_b_f_subset_range_f : Set.range f.b.f ⊆ Set.range f.f := by
  simp only [range_f_eq, Set.iUnion_subset_iff]
  intro s
  rw [b_φ]
  exact (b.range_affineMap_le f s _ (le_refl _)).trans
    (le_trans (by rfl) (le_iSup _ (s.simplex.obj (Fin.last _))))

lemma φ_barycenter (s : X.obj (op n))
    {α : Type*} [Fintype α] (p : α → n.toTopObj) (w : α → ℝ≥0) (hw : ∑ a, w a = 1) :
    f.φ s (SimplexCategory.toTopObj.barycenter p w hw) =
      Finset.centerMass (R := ℝ) (Finset.univ) (fun a ↦ w a) (fun a ↦ f.φ s (p a)) := by
  dsimp [φ]
  rw [(f.isAffine s).map_barycenter, Finset.centerMass_eq_of_sum_1 _ _ (by
    rw [← NNReal.coe_sum, hw, coe_one])]
  rfl

noncomputable def vertex (x : X _⦋0⦌) : E := f.φ x default

lemma φ_vertex {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len + 1)) :
    f.φ x (SimplexCategory.toTopObj.vertex i) = f.vertex (vertexOfSimplex x i) := by
  have h₁ := congr_fun (f.map_φ x (SimplexCategory.const ⦋0⦌ n i)) default
  have h₂ := SimplexCategory.toTopObj.toTopMap_vertex (SimplexCategory.const ⦋0⦌ n i) 0
  dsimp [vertex, vertexOfSimplex] at h₁ ⊢
  rw [SimplexCategory.const_apply'] at h₂
  rw [h₁, ← h₂]
  congr
  subsingleton

lemma range_φ_eq_convexHull {d : SimplexCategory} (x : X.obj (op d)) :
    Set.range (f.φ x) =
      convexHull ℝ (Set.range (fun (i : Fin (d.len + 1)) ↦ f.vertex (vertexOfSimplex x i))) := by
  simp only [(f.isAffine x).range_eq_convexHull, ← f.φ_vertex]

@[simp]
lemma vertex_b (x : (B.obj X) _⦋0⦌) :
    f.b.vertex x = f.isobarycenter (x.obj 0).toS := by
  have := f.b_φ (N.mk x (by simp))
  dsimp [b.affineMap] at this
  dsimp only [vertex]
  rw [this]
  convert SimplexCategory.toTopObj.affineMap_vertex (fun i ↦ f.isobarycenter (x.obj i).toS) 0
  subsingleton

lemma isobarycenter_eq_centerMass (s : X.S) :
    f.isobarycenter s = Finset.univ.centerMass (fun _ ↦ (1 : ℝ))
        (fun i ↦ f.vertex (vertexOfSimplex s.simplex i)) := by
  dsimp [isobarycenter, SimplexCategory.toTopObj.isobarycenter]
  simp [φ_barycenter, φ_vertex]
  rw [← Finset.centerMass_smul_left (c := (s.dim : ℝ) + 1)]
  · congr
    ext
    simpa using mul_inv_cancel₀ (by positivity)
  · positivity

protected noncomputable def sd : (sd.obj X).AffineMap E := f.b.precomp (sdToB.app X)

end AffineMap

end SSet
