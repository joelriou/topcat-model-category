import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.CoconeNPrime
import TopCatModelCategory.FunctorIterate
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

namespace stdSimplex

def barycenter {X α : Type*} [Fintype X] [Fintype α] (p : α → stdSimplex ℝ X)
    (w : α → ℝ) (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1) : stdSimplex ℝ X :=
  ⟨fun x ↦ ∑ (a : α), w a • (p a).1 x,
    fun x ↦ Finset.sum_nonneg (fun a _ ↦ mul_nonneg (hw₀ a) ((p a).2.1 x)), by
    dsimp
    rw [Finset.sum_comm, ← hw₁]
    congr
    ext a
    rw [← Finset.mul_sum, (p a).2.2, mul_one]⟩

@[simp]
lemma barycenter_apply
    {X α : Type*} [Fintype X] [Fintype α] (p : α → stdSimplex ℝ X)
    (w : α → ℝ) (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1) (x : X) :
    barycenter p w hw₀ hw₁ x = ∑ (a : α), w a • p a x := rfl

lemma eq_barycenter_vertex {X : Type*} [Fintype X] [DecidableEq X] (f : stdSimplex ℝ X) :
    f = barycenter vertex f.1 f.2.1 f.2.2 := by
  ext x
  dsimp only [barycenter, DFunLike.coe]
  rw [Finset.sum_eq_single (a := x) _ (by simp), Pi.single_eq_same, smul_eq_mul, mul_one]
  intro y _ h
  rw [Pi.single_eq_of_ne' h, smul_zero]

lemma exists_barycenter_vertex {X : Type*} [Fintype X] [DecidableEq X] (f : stdSimplex ℝ X) :
    ∃ (w : X → ℝ) (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∑ a, w a = 1),
      f = barycenter vertex w hw₀ hw₁ :=
  ⟨_, _, _, eq_barycenter_vertex f⟩

variable (n) in
noncomputable def isobarycenter (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    stdSimplex ℝ X :=
  barycenter vertex (fun _ ↦ 1 / Fintype.card X) (by simp) (by simp)

@[simp]
lemma map_barycenter {X Y α : Type*} [Fintype X] [Fintype Y] [Fintype α]
    (g : X → Y) (p : α → stdSimplex ℝ X) (w : α → ℝ) (hw₀ : ∀ a, 0 ≤ w a)
    (hw₁ : ∑ a, w a = 1) :
    map g (barycenter p w hw₀ hw₁) = barycenter (fun a ↦ map g (p a)) w hw₀ hw₁ := by
  classical
  ext y
  simp only [map_coe, barycenter_apply, smul_eq_mul, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

variable {X : Type*} [Fintype X]
variable {E : Type v} [AddCommGroup E] [Module ℝ E] (f : stdSimplex ℝ X → E)

def IsAffine [DecidableEq X] : Prop :=
  ∀ (p : stdSimplex ℝ X), f p = ∑ (x : X), p x • f (vertex x)

abbrev affineMap (p : X → E) : stdSimplex ℝ X → E :=
  fun y ↦ ∑ (x : X), y x • p x

@[simp]
lemma affineMap_vertex [DecidableEq X] (p : X → E) (x : X) :
    affineMap p (vertex x) = p x := by
  dsimp [affineMap, vertex]
  rw [Finset.sum_eq_single (a := x)]
  all_goals aesop

lemma isAffine_affineMap [DecidableEq X] (p : X → E) :
    IsAffine (affineMap p) := by
  intro
  simp

variable (X) in
lemma affineMap_vertex_eq [DecidableEq X] :
    affineMap (Subtype.val ∘ vertex : X → _) = DFunLike.coe := by
  ext f x
  simp only [Finset.sum_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (a := x) _ (by simp), Pi.single_eq_same, mul_one]
  intro y _ h
  rw [Pi.single_eq_of_ne' h, mul_zero]

variable (X) in
lemma isAffine_dFunLikeCoe [DecidableEq X] :
    IsAffine (DFunLike.coe : stdSimplex ℝ X → _) := by
  rw [← affineMap_vertex_eq]
  apply isAffine_affineMap

lemma continuous_affineMap {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (p : X → E) :
    Continuous (affineMap p) := by
  continuity

lemma IsAffine.postcomp {f : stdSimplex ℝ X → E} [DecidableEq X] (hf : IsAffine f)
    {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (φ : E →ₗ[ℝ] E') : IsAffine (φ ∘ f) :=
  fun x ↦ by simp [hf x]

namespace IsAffine

variable {f} [DecidableEq X] (hf : IsAffine f)

include hf

lemma exists_eq :
    ∃ (p : X → E), f = affineMap p :=
  ⟨fun i ↦ f (vertex i), by ext; rw [hf]⟩

lemma exists_linearMap :
    ∃ (l : (X → ℝ) →ₗ[ℝ] E), f = l ∘ Subtype.val := by
  obtain ⟨p, rfl⟩ := hf.exists_eq
  exact ⟨Fintype.linearCombination ℝ p, rfl⟩

lemma map_barycenter {α : Type*} [Fintype α] (p : α → stdSimplex ℝ X) (w : α → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1) :
    f (barycenter p w hw₀ hw₁) = ∑ (a : α), w a • f (p a) := by
  obtain ⟨q, rfl⟩ := hf.exists_eq
  simp only [Finset.smul_sum, affineMap]
  rw [Finset.sum_comm]
  congr
  ext x
  simp [smul_smul, Finset.sum_smul]

lemma map {Y : Type*} [Fintype Y] [DecidableEq Y] (g : Y → X) :
    IsAffine (f.comp (stdSimplex.map g)) := by
  intro x
  obtain ⟨w, hw₀, hw₁, rfl⟩ := exists_barycenter_vertex x
  dsimp
  rw [stdSimplex.map_barycenter, hf.map_barycenter]
  congr 1
  ext y
  simp only [map_vertex]
  congr 1
  rw [Finset.sum_eq_single (a := y) (by aesop) (by aesop),
    Pi.single_eq_same, mul_one]

lemma ext {g : stdSimplex ℝ X → E} (hg : IsAffine g)
    (h : ∀ (x : X), f (vertex x) = g (vertex x)) : f = g := by
  ext x
  rw [hf, hg]
  simp [h]

lemma convex_range : Convex ℝ (Set.range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb h
  have := hf
  refine ⟨⟨fun i ↦ a * x i + b * y i,
    fun i ↦ add_nonneg (mul_nonneg ha (x.2.1 i))
      (mul_nonneg hb (y.2.1 i)), ?_⟩, ?_⟩
  · simpa [Finset.sum_add_distrib, ← Finset.mul_sum]
  · obtain ⟨p, rfl⟩ := hf.exists_eq
    simp [affineMap, Finset.smul_sum, Finset.sum_add_distrib,
      DFunLike.coe, add_smul, smul_smul]

lemma map_barycenter_mem_of_convex
    {α : Type*} [Fintype α] (p : α → stdSimplex ℝ X) (w : α → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1)
    {S : Set E} (hS : Convex ℝ S) (hq : ∀ (a : α), f (p a) ∈ S) :
    f (barycenter p w hw₀ hw₁) ∈ S := by
  rw [hf.map_barycenter]
  exact hS.sum_mem (by simpa) hw₁ (by simpa)

lemma range_subset_iff_of_convex {F : Set E} (hF : Convex ℝ F) :
    Set.range f ⊆ F ↔ ∀ i, f (vertex i) ∈ F := by
  have := hf
  refine ⟨fun h i ↦ h (by simp), fun h ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, hw₀, hw₁, rfl⟩ := exists_barycenter_vertex x
  exact hf.map_barycenter_mem_of_convex _ _ _ _ hF h

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
    (f : stdSimplex ℝ X → F) (hf : IsAffine f) :
    Continuous f := by
  obtain ⟨p, rfl⟩ := hf.exists_eq
  exact continuous_affineMap p

end IsAffine

end stdSimplex

namespace SSet

variable {X Y : SSet.{u}} {E : Type v}

section

variable (f : |X| → E)

namespace IsAffineAt

noncomputable def φ (x : X.obj (op n)) :
    _root_.stdSimplex ℝ (Fin (n.len + 1)) → E :=
  f.comp (Function.comp
    (toTopSimplex.inv.app _ ≫ toTop.map (yonedaEquiv.symm x)) ULift.up)

lemma precomp_φ (g : Y ⟶ X) (y : Y.obj (op n)) :
    φ (f.comp (toTop.map g).hom) y = φ f (g.app _ y) := by
  dsimp [φ]
  rw [Function.comp_assoc, ← yonedaEquiv_symm_comp, Functor.map_comp]
  rfl

lemma map_φ {n : SimplexCategory} (x : X.obj (op n)) (g : m ⟶ n) :
    φ f (X.map g.op x) = φ f x ∘ stdSimplex.map g := by
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
  stdSimplex.IsAffine (IsAffineAt.φ f x)

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

section

variable {f} {E' : Type*} [AddCommGroup E'] [Module ℝ E']

lemma IsAffineAt.postcomp
    {x : X.obj (op n)} (hx : IsAffineAt f x) (φ : E →ₗ[ℝ] E') :
    IsAffineAt (φ ∘ f) x :=
  stdSimplex.IsAffine.postcomp hx φ

lemma IsAffine.postcomp
    (hf : IsAffine f) (φ : E →ₗ[ℝ] E') :
    IsAffine (φ ∘ f) :=
  fun _ x ↦ (hf x).postcomp φ

end

end

variable [AddCommGroup E] [Module ℝ E]

variable (X E)
structure AffineMap where
  f : |X| → E
  isAffine : IsAffine f

namespace AffineMap

variable {X E} (f : AffineMap X E)

noncomputable abbrev φ {d : SimplexCategory} (s : X.obj (op d)) :
    _root_.stdSimplex ℝ (Fin (d.len + 1)) → E :=
  IsAffineAt.φ f.f s

lemma continuous_φ {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AffineMap X E)
    {n : SimplexCategory} (x : X.obj (op n)) : Continuous (f.φ x) :=
  (f.isAffine x).continuous

lemma map_φ {d e : SimplexCategory} (s : X.obj (op d)) (g : e ⟶ d) :
    f.φ (X.map g.op s) = f.φ s ∘ stdSimplex.map g := by
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
  f.φ s.simplex (stdSimplex.isobarycenter _)

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
    induction n using SimplexCategory.rec with | _ n
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

lemma range_precomp_f_subset_range_f (g : Y ⟶ X) :
    Set.range (f.precomp g).f ⊆ Set.range f.f := by
  dsimp [precomp]
  apply Set.range_comp_subset_range

@[simp]
lemma precomp_φ (g : Y ⟶ X) {d : SimplexCategory} (y : Y.obj (op d)) :
    (f.precomp g).φ y = f.φ (g.app _ y) :=
  IsAffineAt.precomp_φ f.f g y

@[simps -fullyApplied f]
def postcomp {E' : Type*} [AddCommGroup E'] [Module ℝ E'] (φ : E →ₗ[ℝ] E') :
    AffineMap X E' where
  f := φ ∘ f.f
  isAffine := f.isAffine.postcomp φ

@[continuity]
lemma continuous {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X.AffineMap E) :
    Continuous f.f := by
  rw [TopCat.continuous_iff_of_isColimit' _
    (isColimitOfPreserves toTop (Presheaf.colimitOfRepresentable X))]
  rintro ⟨⟨n⟩, x⟩
  convert ((f.continuous_φ x).comp
    Homeomorph.ulift.continuous).comp (toTopSimplex.hom.app n).hom.continuous
  ext x
  dsimp [φ, IsAffineAt.φ] at x ⊢
  congr
  exact (ConcreteCategory.congr_hom (toTopSimplex.app n).hom_inv_id x).symm

@[simp]
lemma isobarycenter_precomp (g : Y ⟶ X) (s : Y.S) :
    (f.precomp g).isobarycenter s = f.isobarycenter (s.map g) := by
  simp [isobarycenter]

noncomputable def vertex (x : X _⦋0⦌) : E := f.φ x default

lemma φ_vertex {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len + 1)) :
    f.φ x (stdSimplex.vertex i) = f.vertex (vertexOfSimplex x i) := by
  have h₁ := congr_fun (f.map_φ x (SimplexCategory.const ⦋0⦌ n i)) default
  have h₂ := stdSimplex.map_vertex (S := ℝ) (SimplexCategory.const ⦋0⦌ n i) 0
  dsimp [vertex, vertexOfSimplex] at h₁ ⊢
  rw [SimplexCategory.const_apply'] at h₂
  rw [h₁, ← h₂]
  congr
  subsingleton

@[simp]
lemma precomp_vertex (f : X.AffineMap E) (g : Y ⟶ X) (y : Y _⦋0⦌) :
    (f.precomp g).vertex y = f.vertex (g.app _ y) := by
  simp [vertex]

@[simp]
lemma postcomp_vertex (f : X.AffineMap E)
    {E' : Type*} [AddCommGroup E'] [Module ℝ E'] (φ : E →ₗ[ℝ] E') (x : X _⦋0⦌) :
    (f.postcomp φ).vertex x = φ (f.vertex x) :=
  rfl

@[ext]
lemma ext {f g : X.AffineMap E}
    (h : ∀ (x : X _⦋0⦌), f.vertex x = g.vertex x) : f = g := by
  suffices f.f = g.f by cases f; cases g; aesop
  suffices ∀ {d : SimplexCategory} (s : X.obj (op d)), f.φ s = g.φ s by
    ext y
    obtain ⟨⟨⟨d⟩, s⟩, z, rfl⟩:= Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (toTop ⋙ forget _) (isColimitCoconeFromElementsOp X)) y
    dsimp at z ⊢
    replace this := congr_fun (this s) (d.toTopHomeo z)
    dsimp [φ, IsAffineAt.φ] at this
    have hz : z = toTopSimplex.{u}.inv.app d (ULift.up (d.toTopHomeo z)) := by
      obtain ⟨z, rfl⟩ := d.toTopHomeo.symm.surjective z
      simp
      rfl
    convert this
  intro d s
  exact stdSimplex.IsAffine.ext (f.isAffine s) (g.isAffine s)
    (fun i ↦ by simp [φ_vertex, h])

namespace b

noncomputable def affineMap (s : (B.obj X).N) :
    _root_.stdSimplex ℝ (Fin (s.dim + 1)) → E :=
  (stdSimplex.affineMap
    (fun i ↦ f.isobarycenter (s.simplex.obj i).toS))

lemma isAffine_affineMap (s : (B.obj X).N) :
    stdSimplex.IsAffine (affineMap f s) :=
  stdSimplex.isAffine_affineMap _
lemma affineMap_comp {s t : (B.obj X).N} (hst : s ≤ t) :
    (affineMap f t).comp (stdSimplex.map (N.monoOfLE hst)) =
      affineMap f s := by
  refine stdSimplex.IsAffine.ext
    (stdSimplex.IsAffine.map
      (stdSimplex.isAffine_affineMap _) _)
    (stdSimplex.isAffine_affineMap _) (fun i ↦ ?_)
  dsimp [affineMap]
  simp only [stdSimplex.map_vertex, stdSimplex.affineMap_vertex,
    ← N.map_monoOfLE hst]
  rfl

lemma range_affineMap_le (s : (B.obj X).N) (t : X.N) (hs : s.simplex.obj (Fin.last _) ≤ t) :
    Set.range (affineMap f s) ⊆ Set.range (f.φ t.simplex) := by
  rw [(isAffine_affineMap f s).range_subset_iff_of_convex
    (f.isAffine t.simplex).convex_range]
  intro i
  dsimp only [affineMap]
  rw [stdSimplex.affineMap_vertex]
  exact (f.isAffine (s.simplex.obj i).simplex).map_barycenter_mem_of_convex _ _ _ _
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
      stdSimplex.affineMap
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
  exact stdSimplex.isAffine_affineMap _

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
    {α : Type*} [Fintype α] (p : α → _root_.stdSimplex ℝ (Fin (n.len + 1))) (w : α → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1) :
    f.φ s (stdSimplex.barycenter p w hw₀ hw₁) =
      Finset.centerMass (R := ℝ) (Finset.univ) (fun a ↦ w a) (fun a ↦ f.φ s (p a)) := by
  dsimp [φ]
  rw [(f.isAffine s).map_barycenter, Finset.centerMass_eq_of_sum_1 _ _ hw₁]

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
  convert stdSimplex.affineMap_vertex (fun i ↦ f.isobarycenter (x.obj i).toS) 0
  subsingleton

lemma isobarycenter_eq_centerMass (s : X.S) :
    f.isobarycenter s = Finset.univ.centerMass (fun _ ↦ (1 : ℝ))
        (fun i ↦ f.vertex (vertexOfSimplex s.simplex i)) := by
  dsimp [isobarycenter, stdSimplex.isobarycenter]
  simp [φ_barycenter, φ_vertex]
  rw [← Finset.centerMass_smul_left (c := (s.dim : ℝ) + 1)]
  · congr
    ext
    simpa using mul_inv_cancel₀ (by positivity)
  · positivity

lemma b_precomp (g : Y ⟶ X) [Mono g] :
    (f.precomp g).b = f.b.precomp (B.map g) := by
  ext s
  dsimp
  rw [vertex_b, isobarycenter_precomp, precomp_vertex, vertex_b, B_map_app_obj,
    toS_mapN_of_nonDegenerate]
  rw [nonDegenerate_iff_of_mono]
  exact (s.obj 0).nonDegenerate

protected noncomputable def sd : (sd.obj X).AffineMap E := f.b.precomp (sdToB.app X)

lemma range_sd_f_subset_range_f : Set.range f.sd.f ⊆ Set.range f.f :=
  (f.b.range_precomp_f_subset_range_f _).trans f.range_b_f_subset_range_f

noncomputable def sdIter (n : ℕ) : ((sd.iter n).obj X).AffineMap E := by
  induction n with
  | zero => exact f
  | succ n hn => exact hn.sd

@[simp]
lemma sdIter_zero : f.sdIter 0 = f := rfl

@[simp]
lemma sdIter_succ (n : ℕ) : f.sdIter (n + 1) = (f.sdIter n).sd := rfl

lemma range_sdIter_f_subset_range_f (n : ℕ) : Set.range (f.sdIter n).f ⊆ Set.range f.f := by
  induction n with
  | zero => rfl
  | succ n hn => exact (range_sd_f_subset_range_f _).trans hn

lemma isAffineAtφ_toTopHomeo (n : ℕ) :
    (IsAffineAt.φ (fun s i ↦ ⦋n⦌.toTopHomeo s i)
      (SSet.yonedaEquiv.{u} (𝟙 _))) = DFunLike.coe := by
  ext f i
  simpa [IsAffineAt.φ] using DFunLike.congr_fun (⦋n⦌.toTopHomeo.right_inv f) i

noncomputable def stdSimplex (n : ℕ) :
    (Δ[n] : SSet.{u}).AffineMap (Fin (n + 1) → ℝ) where
  f := DFunLike.coe ∘ ⦋n⦌.toTopHomeo
  isAffine := by
    rw [isAffine_iff_eq_top, stdSimplex.subcomplex_eq_top_iff, mem_isAffine_iff]
    dsimp only [IsAffineAt]
    erw [isAffineAtφ_toTopHomeo]
    exact stdSimplex.isAffine_dFunLikeCoe (Fin (n + 1))

@[simp]
lemma stdSimplex_f_toTopHomeo_symm {n : ℕ}  (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex n).f (⦋n⦌.toTopHomeo.symm x) = x := by
  simpa [stdSimplex] using ⦋n⦌.toTopHomeo.right_inv x

lemma injective_stdSimplex_f (n : ℕ) :
    Function.Injective (stdSimplex n).f := by
  intro x y h
  obtain ⟨x, rfl⟩ := ⦋n⦌.toTopHomeo.symm.surjective x
  obtain ⟨y, rfl⟩ := ⦋n⦌.toTopHomeo.symm.surjective y
  simp only [stdSimplex_f_toTopHomeo_symm] at h
  obtain rfl : x = y := by aesop
  rfl

end AffineMap

end SSet
