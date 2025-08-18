import TopCatModelCategory.SSet.Simplices
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

universe u

open CategoryTheory Simplicial Limits Opposite

@[simp]
lemma SSet.id_app {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    NatTrans.app (𝟙 X) n x = x := rfl

lemma Quiver.Hom.op_surjective {C : Type*} [Quiver C] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ (g : Y.unop ⟶ X.unop), f = g.op := ⟨f.unop, rfl⟩

instance {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsSplitMono f.op where
  exists_splitMono := ⟨⟨(section_ f).op, Quiver.Hom.unop_inj (by simp)⟩⟩

lemma SimplexCategory.isIso_iff_len_eq_of_epi {n m : SimplexCategory} (f : n ⟶ m) [Epi f] :
    IsIso f ↔ n.len = m.len := by
  have hf := len_le_of_epi f
  refine ⟨fun _ ↦ le_antisymm (len_le_of_mono f) hf, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  have h := (epi_iff_surjective (f := f)).1 inferInstance
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], h⟩

lemma SimplexCategory.exists_mono_fac {n m : SimplexCategory} (f : n ⟶ m) :
    ∃ (d : ℕ) (p : n ⟶ ⦋d⦌) (i : ⦋d⦌ ⟶ m), Epi p ∧ Mono i ∧ p ≫ i = f := by
  suffices ∃ (d : SimplexCategory) (p : n ⟶ d) (i : d ⟶ m), Epi p ∧ Mono i ∧ p ≫ i = f by
    obtain ⟨d, p, i, _, _, fac⟩ := this
    induction' d using SimplexCategory.rec with d
    exact ⟨d, p, i, inferInstance, inferInstance, fac⟩
  exact ⟨_, _, _, inferInstance, inferInstance, image.fac f⟩

namespace SSet

variable (X : SSet.{u})

structure N extends X.S where mk'' ::
  nonDegenerate : simplex ∈ X.nonDegenerate _

namespace N

variable {X}

@[simps toS]
def mk' (s : X.S) (hs : s.2 ∈ X.nonDegenerate _) : X.N where
  toS := s
  nonDegenerate := hs

lemma mk'_surjective (s : X.N) :
    ∃ (t : X.S) (ht : t.2 ∈ X.nonDegenerate _), s = mk' t ht :=
  ⟨s.toS, s.nonDegenerate, rfl⟩

@[simps]
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) : X.N where
  simplex := x
  nonDegenerate := hx

lemma mk_surjective (x : X.N) :
    ∃ (n : ℕ) (y : X.nonDegenerate n), x = N.mk _ y.2 :=
  ⟨x.1.1, ⟨_, x.nonDegenerate⟩, rfl⟩

@[deprecated (since := "2025-08-06")] alias exists_nonDegenerate := mk_surjective

lemma induction
    {motive : ∀ {n : ℕ} (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate _), Prop}
    (h₁ : ∀ (x : X.N), motive x.1.2 x.2)
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) : motive x hx :=
  h₁ (mk x hx)

instance : Preorder X.N := Preorder.lift toS

lemma le_iff {x y : X.N} : x ≤ y ↔ x.subcomplex ≤ y.subcomplex :=
  Iff.rfl

lemma le_iff_toS_le_toS {x y : X.N} : x ≤ y ↔ x.toS ≤ y.toS := Iff.rfl

lemma le_iff_exists {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.1.1⦌ ⟶ ⦋y.1.1⦌) (_ : Mono f), X.map f.op y.1.2 = x.1.2 := by
  simp only [le_iff, CategoryTheory.Subpresheaf.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  refine ⟨?_, by tauto⟩
  rintro ⟨f, hf⟩
  refine ⟨f, ?_, hf⟩
  have : IsIso (factorThruImage f) := by
    rw [SimplexCategory.isIso_iff_len_eq_of_epi]
    obtain h | h := (SimplexCategory.len_le_of_epi
      (factorThruImage f)).eq_or_lt
    · exact h.symm
    · exfalso
      apply (mem_nonDegenerate_iff_notMem_degenerate _ _).1 x.2
      rw [mem_degenerate_iff]
      refine ⟨_, h, factorThruImage f, inferInstance, ?_⟩
      rw [← image.fac f, op_comp, FunctorToTypes.map_comp_apply] at hf
      rw [← hf]
      apply Set.mem_range_self
  have := isIso_of_mono_of_epi (factorThruImage f)
  rw [← image.fac f]
  infer_instance

lemma le_of_le {x y : X.N} (h : x ≤ y) : x.1.1 ≤ y.1.1 := by
  rw [le_iff_exists] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

instance : PartialOrder X.N where
  le_antisymm x₁ x₂ h h' := by
    obtain ⟨n₁, ⟨x₁, hx₁⟩, rfl⟩ := x₁.mk_surjective
    obtain ⟨n₂, ⟨x₂, hx₂⟩, rfl⟩ := x₂.mk_surjective
    obtain rfl : n₁ = n₂ := le_antisymm (le_of_le h) (le_of_le h')
    rw [le_iff_exists] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop

lemma subcomplex_injective {x y : X.N} (h : x.subcomplex = y.subcomplex) :
    x = y := by
  apply le_antisymm
  all_goals
  · rw [le_iff, h]

lemma subcomplex_injective_iff {x y : X.N} :
    x.subcomplex = y.subcomplex ↔ x = y :=
  ⟨subcomplex_injective, by rintro rfl; rfl⟩

lemma eq_iff {x y : X.N} : x = y ↔ x.subcomplex = y.subcomplex :=
  ⟨by rintro rfl; rfl, fun h ↦ by
    apply le_antisymm
    all_goals
    · rw [le_iff, h]⟩

def toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) : A.toSSet.N :=
  N.mk' (x.toS.toSubcomplex hx) (by
    rw [Subcomplex.mem_nonDegenerate_iff]
    exact x.nonDegenerate)

lemma toS_toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
    (x.toSubcomplex hx).toS = x.toS.toSubcomplex hx := rfl

lemma toSubcomplex_le_toSubcomplex_iff
    (x y : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) (hy : y.simplex ∈ A.obj _) :
    x.toSubcomplex hx ≤ y.toSubcomplex hy ↔ x ≤ y := by
  apply S.toSubcomplex_le_toSubcomplex_iff

section

variable (s : X.N) {d : ℕ} (hd : s.dim = d)

abbrev cast : X.N where
  toS := s.toS.cast hd
  nonDegenerate := by
    subst hd
    exact s.nonDegenerate

lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

lemma ext_iff (x y : X.N) :
    x = y ↔ x.toS = y.toS := by
  obtain ⟨x, hx, rfl⟩ := x.mk'_surjective
  obtain ⟨y, hy, rfl⟩ := y.mk'_surjective
  simp [mk']

@[ext]
lemma ext {x y : X.N} (h : x.toS = y.toS) :
    x = y := by
  rwa [ext_iff]

lemma mk_eq_iff_sMk_eq {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x ∈ X.nonDegenerate _) (hy : y ∈ X.nonDegenerate _) :
    N.mk x hx = N.mk y hy ↔ S.mk x = S.mk y := by
  rw [ext_iff]
  rfl

end N

@[simps]
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := x.subcomplex
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

@[simps! obj]
def functorN : X.N ⥤ SSet.{u} :=
  X.orderEmbeddingN.monotone.functor ⋙ Subcomplex.toPresheafFunctor

variable {X} in
@[simp]
lemma functorN_map {x₁ x₂ : X.N} (f : x₁ ⟶ x₂) :
    X.functorN.map f = Subcomplex.homOfLE (X.orderEmbeddingN.monotone (leOfHom f)) := rfl

namespace S

variable {X}

lemma subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex = y.subcomplex := by
  refine le_antisymm ?_ ?_
  · simp only [Subcomplex.ofSimplex_le_iff]
    exact ⟨f.op, by aesop⟩
  · simp only [Subcomplex.ofSimplex_le_iff]
    have := isSplitEpi_of_epi f
    have : Function.Injective (X.map f.op) := by
      rw [← mono_iff_injective]
      infer_instance
    refine ⟨(section_ f).op, this ?_⟩
    dsimp
    rw [← hf, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]

lemma existsUnique_n (x : X.S) : ∃! (y : X.N), y.subcomplex = x.subcomplex :=
  existsUnique_of_exists_of_unique (by
      obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
      obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
      exact ⟨N.mk y.1 y.2, (subcomplex_eq_of_epi _ _ f rfl).symm⟩)
    (fun y₁ y₂ h₁ h₂ ↦ N.subcomplex_injective (by rw [h₁, h₂]))

/-- This is the non degenerate simplex of a simplicial set which
generates the same subcomplex as a given simplex. -/
noncomputable def toN (x : X.S) : X.N := x.existsUnique_n.exists.choose

@[simp]
lemma subcomplex_toN (x : X.S) : x.toN.subcomplex = x.subcomplex :=
  x.existsUnique_n.exists.choose_spec

lemma toN_eq_iff {x : X.S} {y : X.N} :
    x.toN = y ↔ y.subcomplex = x.subcomplex :=
  ⟨by rintro rfl; simp, fun h ↦ x.existsUnique_n.unique (by simp) h⟩

lemma toN_of_nonDegenerate (x : X.S) (hx : x.simplex ∈ X.nonDegenerate _) :
    x.toN = N.mk _ hx := by
  rw [toN_eq_iff]
  rfl

lemma existsUnique_toNπ' {x : X.S} {y : X.N} (hy : x.toN = y) :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Epi f ∧ X.map f.op y.simplex = x.simplex := by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff, hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  exact existsUnique_of_exists_of_unique ⟨f, inferInstance, rfl⟩
    (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ unique_nonDegenerate₃ _ _ _ _ hf₁.symm _ _ hf₂.symm)

section

variable {x : X.S} {y : X.N} (hy : x.toN = y)

noncomputable def toNπ' {x : X.S} {y : X.N} (hy : x.toN = y) : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_toNπ' hy).exists.choose

instance : Epi (toNπ' hy) := (existsUnique_toNπ' hy).exists.choose_spec.1

@[simp]
lemma map_toNπ' : X.map (toNπ' hy).op y.simplex = x.simplex :=
  (existsUnique_toNπ' hy).exists.choose_spec.2

lemma dim_toN_le (x : X.S) : x.toN.dim ≤ x.dim :=
  SimplexCategory.le_of_epi (toNπ' (x := x) rfl)

lemma toNπ'_eq_iff (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) :
    toNπ' hy = f ↔ X.map f.op y.simplex = x.simplex := by
  constructor
  · rintro rfl
    simp
  · intro hf
    refine (existsUnique_toNπ' hy).unique ⟨inferInstance, by simp⟩
      ⟨?_, hf⟩
    obtain ⟨d, p, i, _, _, fac⟩ := SimplexCategory.exists_mono_fac f
    obtain h | rfl := (SimplexCategory.le_of_mono i).lt_or_eq
    · exfalso
      let z := S.mk (X.map i.op y.simplex)
      have h₁ : z.toN = y := by
        rw [toN_eq_iff]
        apply le_antisymm
        · rw [← hy, x.subcomplex_toN, Subpresheaf.ofSection_le_iff]
          exact ⟨p.op, by simp [← hf, ← fac, z]⟩
        · rw [Subpresheaf.ofSection_le_iff]
          exact ⟨i.op, rfl⟩
      have h₂ := z.dim_toN_le
      rw [N.ext_iff] at h₁
      rw [S.dim_eq_of_eq h₁] at h₂
      simpa [z] using lt_of_lt_of_le h h₂
    · obtain rfl := SimplexCategory.eq_id_of_mono i
      simpa [← fac]

end

noncomputable def toNπ (x : X.S) : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌ := toNπ' rfl

instance (x : X.S) : Epi x.toNπ := by dsimp [toNπ]; infer_instance

@[simp]
lemma map_toNπ (x : X.S) : X.map x.toNπ.op x.toN.simplex = x.simplex := by
  simp [toNπ]

lemma toNπ_eq_iff (x : X.S) (f : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌) :
    x.toNπ = f ↔ X.map f.op x.toN.simplex = x.simplex := by
  apply toNπ'_eq_iff

lemma self_le_toS_toN (s : X.S) : s ≤ s.toN.toS := by
  rw [S.le_iff, subcomplex_toN]

lemma toS_toN_le_self (s : X.S) : s.toN.toS ≤ s := by
  rw [S.le_iff, subcomplex_toN]

end S

variable {X}

@[simp]
lemma N.toS_toN (x : X.N) : x.toS.toN = x := by
  rw [S.toN_eq_iff]

lemma N.toN_surjective : Function.Surjective (S.toN (X := X)) :=
  fun s ↦ ⟨s.toS, by simp⟩


variable (X)

@[simps]
def coconeN : Cocone X.functorN where
  pt := X
  ι := { app _ := Subcomplex.ι _ }

namespace isColimitCoconeN

variable {X}

lemma hom_ext {Y : SSet.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X.N), (Subcomplex.ofSimplex x.1.2).ι ≫ f = (Subcomplex.ofSimplex x.1.2).ι ≫ g) :
    f = g := by
  rw [← cancel_epi (Subcomplex.topIso _).hom, ← Subpresheaf.equalizer_eq_iff,
    Subcomplex.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simpa [Subpresheaf.equalizer] using
    congr_fun (NatTrans.congr_app (h (N.mk _ hx)) (op ⦋n⦌))
      ⟨x, Subcomplex.mem_ofSimplex_obj x⟩

variable (s : Cocone X.functorN)

noncomputable def descApp {n : ℕ} (x : X _⦋n⦌) : s.pt _⦋n⦌ :=
  yonedaEquiv (stdSimplex.map (S.mk x).toNπ ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app (S.mk x).toN)

lemma descApp_apply {n : ℕ} (x : X _⦋n⦌) (y : X.N) (f : ⦋n⦌ ⟶ ⦋y.1.1⦌) [Epi f]
    (hf : X.map f.op y.1.2 = x) :
    descApp s x = yonedaEquiv (stdSimplex.map f ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app y) := by
  obtain rfl : (S.mk x).toN = y := by
    rw [S.toN_eq_iff, ← hf]
    exact (S.subcomplex_eq_of_epi _ _ f rfl).symm
  dsimp only [descApp]
  congr
  rwa [S.toNπ_eq_iff]

@[simp]
lemma descApp_apply' (x : X.N) :
    descApp s x.1.2 = (s.ι.app x).app _ ⟨x.1.2, Subcomplex.mem_ofSimplex_obj _⟩ :=  by
  rw [descApp_apply s x.1.2 x (𝟙 _) (by simp), CategoryTheory.Functor.map_id, Category.id_comp,
    yonedaEquiv_comp, Subcomplex.yonedaEquiv_toOfSimplex]

noncomputable def desc : X ⟶ s.pt where
  app := fun ⟨n⟩ ↦ by
    induction' n using SimplexCategory.rec with n
    exact descApp _
  naturality := by
    rintro ⟨n⟩ ⟨m⟩ f
    obtain ⟨f, rfl⟩ := Quiver.Hom.op_surjective f
    induction' n using SimplexCategory.rec with n
    induction' m using SimplexCategory.rec with m
    dsimp [SimplexCategory.rec]
    ext x
    dsimp [descApp]
    have h : (S.mk (X.map f.op x)).toN ≤ (S.mk x).toN := by
      rw [N.le_iff, S.subcomplex_toN, S.subcomplex_toN, Subpresheaf.ofSection_le_iff,
        Subcomplex.mem_ofSimplex_obj_iff]
      exact ⟨f, rfl⟩
    apply yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply, SSet.yonedaEquiv_symm_map,
      Equiv.symm_apply_apply, ← s.w (homOfLE h)]
    dsimp
    simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
    rw [← cancel_mono (Subcomplex.ι _)]
    apply yonedaEquiv.injective
    dsimp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.toOfSimplex_ι,
      yonedaEquiv_map_comp, Equiv.apply_symm_apply, S.map_toNπ]

@[simp]
lemma desc_app_apply {n : ℕ} (x : X _⦋n⦌) :
    (desc s).app _ x = descApp _ x := rfl

@[reassoc (attr := simp)]
def fac (x : X.N) : (Subcomplex.ofSimplex x.1.2).ι ≫ desc s = s.ι.app x := by
  rw [← cancel_epi (Subcomplex.toOfSimplex _),
    Subcomplex.toOfSimplex_ι_assoc, yonedaEquiv_symm_comp, desc_app_apply,
    descApp_apply']
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Subcomplex.yonedaEquiv_toOfSimplex]

end isColimitCoconeN

noncomputable def isColimitCoconeN : IsColimit X.coconeN where
  desc := isColimitCoconeN.desc
  fac := isColimitCoconeN.fac
  uniq s m hm := isColimitCoconeN.hom_ext (by aesop)

variable {X} {Y : SSet.{u}} (f : X ⟶ Y)

@[simps -isSimp coe]
noncomputable def mapN : X.N →o Y.N where
  toFun x := (S.map f x.toS).toN
  monotone' x x' h := by
    simp only [N.le_iff, S.subcomplex_toN, Subpresheaf.ofSection_le_iff, S.map_dim,
      S.map_simplex, mem_ofSimplex_obj_iff] at h ⊢
    obtain ⟨g, hg⟩ := h
    exact ⟨g, by simp only [← hg, FunctorToTypes.naturality]⟩

@[simp]
lemma mapN_toN (x : X.S) :
    mapN f x.toN = (S.map f x).toN := by
  simp only [mapN_coe]
  simp [N.eq_iff]

lemma toS_mapN_of_nonDegenerate (x : X.N) (hx : f.app _ x.simplex ∈ Y.nonDegenerate _) :
    (mapN f x).toS = S.map f x.toS := by
  conv_lhs => rw [← x.toS_toN, mapN_toN]
  rw [S.toN_of_nonDegenerate _ hx]
  rfl

lemma toS_mapN_of_isIso (x : X.N) [IsIso f] :
    (mapN f x).toS = S.map f x.toS :=
  toS_mapN_of_nonDegenerate _ _
    (by simpa only [nonDegenerate_iff_of_isIso] using x.nonDegenerate)

lemma toS_mapN_of_mono (x : X.N) [Mono f] :
    (mapN f x).toS = S.map f x.toS :=
  toS_mapN_of_nonDegenerate _ _
    (by simpa only [nonDegenerate_iff_of_mono] using x.nonDegenerate)

@[simp]
lemma mapN_id : mapN (𝟙 X) = OrderHom.id := by
  ext x
  obtain ⟨x, rfl⟩ := x.toN_surjective
  simp

lemma mapN_mapN {Z : SSet.{u}} (g : Y ⟶ Z) (x : X.N) :
    mapN g (mapN f x) = mapN (f ≫ g) x := by
  obtain ⟨x, rfl⟩ := x.toN_surjective
  simp [S.map_map]

@[simp]
lemma subcomplex_mapN (x : X.N) : (mapN f x).subcomplex = Subcomplex.image x.subcomplex f := by
  simp [mapN]

namespace N

attribute [local simp] mapN_mapN in
@[simps]
noncomputable def functor : SSet.{u} ⥤ PartOrd.{u} where
  obj X := .of X.N
  map f := PartOrd.ofHom (mapN f)

end N

lemma N.mapN_ι_simplex_mem_obj {A : X.Subcomplex} (x : A.toSSet.N) :
    (mapN A.ι x).simplex ∈ A.obj _ := by
  rw [toS_mapN_of_mono]
  simp

@[simp]
lemma N.toSubcomplex_mapN_ι {A : X.Subcomplex} (x : A.toSSet.N) :
    (mapN A.ι x).toSubcomplex x.mapN_ι_simplex_mem_obj = x := by
  rw [N.ext_iff]
  apply S.map_injective_of_mono A.ι
  rw [toS_toSubcomplex, S.map_toSubcomplex, toS_mapN_of_mono A.ι]

@[simp]
lemma N.mapN_ι_toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
    mapN A.ι (x.toSubcomplex hx) = x := by
  rw [ext_iff, toS_mapN_of_mono, toS_toSubcomplex, S.map_ι_toSubcomplex]

lemma N.mapN_injective_of_mono [Mono f] :
    Function.Injective (mapN f) := by
  intro s t h
  rw [N.ext_iff] at h ⊢
  exact S.map_injective_of_mono f (by simpa only [toS_mapN_of_mono] using h)

end SSet
