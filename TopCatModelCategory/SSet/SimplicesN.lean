import TopCatModelCategory.SSet.Simplices
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

universe u

open CategoryTheory Simplicial Limits Opposite

lemma Quiver.Hom.op_surjective {C : Type*} [Quiver C] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ (g : Y.unop ⟶ X.unop), f = g.op := ⟨f.unop, rfl⟩

instance {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsSplitMono f.op where
  exists_splitMono := ⟨⟨(section_ f).op, Quiver.Hom.unop_inj (by simp)⟩⟩

lemma SimplexCategory.isIso_iff_len_eq_of_epi {n m : SimplexCategory} (f : n ⟶ m) [Epi f] :
    IsIso f ↔ n.len = m.len := by
  have hf := len_le_of_epi (f := f) inferInstance
  refine ⟨fun _ ↦ le_antisymm (len_le_of_mono (f := f) inferInstance) hf, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  have h := (epi_iff_surjective (f := f)).1 inferInstance
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], h⟩

namespace SSet

variable (X : SSet.{u})

def N : Type u := Sigma (fun (n : ℕ) ↦ X.nonDegenerate n)

namespace N

variable {X}

abbrev mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) : X.N :=
    ⟨n, x, hx⟩

lemma induction
    {motive : ∀ {n : ℕ} (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate _), Prop}
    (h₁ : ∀ (x : X.N), motive x.2.1 x.2.2)
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) : motive x hx :=
  h₁ ⟨n, x, hx⟩

instance : LE X.N where
  le x y := Subcomplex.ofSimplex x.2.1 ≤ Subcomplex.ofSimplex y.2.1

lemma le_iff {x y : X.N} : x ≤ y ↔ Subcomplex.ofSimplex x.2.1 ≤ Subcomplex.ofSimplex y.2.1 :=
  Iff.rfl

lemma le_iff_exists {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.1⦌ ⟶ ⦋y.1⦌) (_ : Mono f), X.map f.op y.2 = x.2 := by
  simp only [le_iff, CategoryTheory.Subpresheaf.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  refine ⟨?_, by tauto⟩
  rintro ⟨f, hf⟩
  refine ⟨f, ?_, hf⟩
  have : IsIso (factorThruImage f) := by
    rw [SimplexCategory.isIso_iff_len_eq_of_epi]
    obtain h | h := (SimplexCategory.len_le_of_epi
      (f := factorThruImage f) inferInstance).eq_or_lt
    · exact h.symm
    · exfalso
      apply (mem_nonDegenerate_iff_not_mem_degenerate _ _).1 x.2.2
      rw [mem_degenerate_iff]
      refine ⟨_, h, factorThruImage f, inferInstance, ?_⟩
      rw [← image.fac f, op_comp, FunctorToTypes.map_comp_apply] at hf
      rw [← hf]
      apply Set.mem_range_self
  have := isIso_of_mono_of_epi (factorThruImage f)
  rw [← image.fac f]
  infer_instance

lemma le_of_le {x y : X.N} (h : x ≤ y) : x.1 ≤ y.1 := by
  rw [le_iff_exists] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono hf

instance : PartialOrder X.N where
  le_refl x := by simp only [le_iff, le_refl]
  le_antisymm := by
    rintro ⟨n₁, x₁⟩ ⟨n₂, x₂⟩ h h'
    obtain rfl : n₁ = n₂ := le_antisymm (le_of_le h) (le_of_le h')
    rw [le_iff_exists] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop
  le_trans _ _ _ h h' := by
    simp only [le_iff] at h h' ⊢
    exact h.trans h'

lemma eq_iff {x y : X.N} : x = y ↔ Subcomplex.ofSimplex x.2.1 = Subcomplex.ofSimplex y.2.1 :=
  ⟨by rintro rfl; rfl, fun h ↦ by
    apply le_antisymm
    all_goals
    · rw [le_iff, h]⟩

end N

@[simps]
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := Subcomplex.ofSimplex x.2.1
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

@[simps]
def coconeN : Cocone X.functorN where
  pt := X
  ι := { app _ := Subcomplex.ι _ }

section

variable {n : ℕ} (x : X _⦋n⦌)

noncomputable def toN : X.N :=
  ⟨_, (X.exists_nonDegenerate x).choose_spec.choose_spec.choose_spec.choose⟩

noncomputable def toNπ : ⦋n⦌ ⟶ ⦋(X.toN x).1⦌ :=
  (X.exists_nonDegenerate x).choose_spec.choose

instance : Epi (X.toNπ x) :=
  (X.exists_nonDegenerate x).choose_spec.choose_spec.choose

instance : IsSplitEpi (X.toNπ x) := isSplitEpi_of_epi _

@[simp]
lemma map_toNπ_op_toN : X.map (X.toNπ x).op (X.toN x).2.1 = x :=
  (X.exists_nonDegenerate x).choose_spec.choose_spec.choose_spec.choose_spec.symm

@[simp]
lemma map_splitEpiSection_eq_toN_snd (h : SplitEpi (X.toNπ x)) :
    X.map h.section_.op x = (X.toN x).2 := by
  nth_rw 6 [← X.map_toNπ_op_toN x]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, h.id,
    op_id, FunctorToTypes.map_id_apply]

@[simp]
lemma map_section_eq_toN_snd :
    X.map (section_ (X.toNπ x)).op x = (X.toN x).2 :=
  map_splitEpiSection_eq_toN_snd _ _ (IsSplitEpi.exists_splitEpi (f := X.toNπ x)).some

@[simp]
lemma ofSimplex_toN : Subcomplex.ofSimplex (X.toN x).2.1 = Subcomplex.ofSimplex x := by
  refine le_antisymm ?_ ?_
  · simp only [Subpresheaf.ofSection_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    have : IsSplitEpi (X.toNπ x) := isSplitEpi_of_epi _
    have h : Mono (X.map (X.toNπ x).op) := inferInstance
    rw [mono_iff_injective] at h
    exact ⟨section_ (X.toNπ x), by simp⟩
  · simp only [Subpresheaf.ofSection_le_iff, Subcomplex.mem_ofSimplex_obj_iff]
    exact ⟨X.toNπ x, by simp⟩

variable {X} in
lemma N.ext {n : ℕ} (x : X _⦋n⦌) (y₁ y₂ : X.N) (f₁ : ⦋n⦌ ⟶ ⦋y₁.1⦌)
    (f₂ : ⦋n⦌ ⟶ ⦋y₂.1⦌) [Epi f₁] [Epi f₂]
    (hf₁ : X.map f₁.op y₁.2.1 = x) (hf₂ : X.map f₂.op y₂.2.1 = x) : y₁ = y₂ := by
  obtain ⟨n₁, y₁⟩ := y₁
  obtain ⟨n₂, y₂⟩ := y₂
  obtain rfl := X.unique_nonDegenerate₁ x _ _ hf₁.symm _ _ hf₂.symm
  obtain rfl := X.unique_nonDegenerate₂ x _ _ hf₁.symm _ _ hf₂.symm
  rfl

lemma toN_eq {n : ℕ} (x : X _⦋n⦌) (y : X.N) (f : ⦋n⦌ ⟶ ⦋y.1⦌) [Epi f]
    (h : X.map f.op y.2.1 = x) : X.toN x = y :=
  N.ext x _ _ (X.toNπ x) f (by simp) h

lemma toN_surjective (s : X.N) : ∃ (n : ℕ) (x : X.nonDegenerate n), s = X.toN x.1 :=
  ⟨s.1, s.2, (X.toN_eq _ _ (𝟙 _) (by simp)).symm⟩

end

namespace isColimitCoconeN

variable {X}

lemma hom_ext {Y : SSet.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X.N), (Subcomplex.ofSimplex x.2.1).ι ≫ f = (Subcomplex.ofSimplex x.2.1).ι ≫ g) :
    f = g := by
  rw [← cancel_epi (Subcomplex.topIso _).hom, ← Subpresheaf.equalizer_eq_iff,
    Subcomplex.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simpa [Subpresheaf.equalizer] using
    congr_fun (NatTrans.congr_app (h ⟨n, ⟨x, hx⟩⟩) (op ⦋n⦌))
      ⟨x, Subcomplex.mem_ofSimplex_obj x⟩

variable (s : Cocone X.functorN)

noncomputable def descApp {n : ℕ} (x : X _⦋n⦌) : s.pt _⦋n⦌ :=
  yonedaEquiv (stdSimplex.map (X.toNπ x) ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app (X.toN x))

lemma descApp_apply {n : ℕ} (x : X _⦋n⦌) (y : X.N) (f : ⦋n⦌ ⟶ ⦋y.1⦌) [Epi f]
    (hf : X.map f.op y.2.1 = x) :
    descApp s x = yonedaEquiv (stdSimplex.map f ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app y) := by
  obtain rfl : y = X.toN x := by
    obtain ⟨m, y⟩ := y
    obtain rfl := X.unique_nonDegenerate₁ x _ _ hf.symm _ _ ((X.map_toNπ_op_toN x).symm)
    obtain rfl := X.unique_nonDegenerate₂ x _ _ hf.symm _ _ ((X.map_toNπ_op_toN x).symm)
    rfl
  obtain rfl := X.unique_nonDegenerate₃ x _ _ hf.symm _ _ ((X.map_toNπ_op_toN x).symm)
  rfl

@[simp]
lemma descApp_apply' (x : X.N) :
    descApp s x.2.1 = (s.ι.app x).app _ ⟨x.2, Subcomplex.mem_ofSimplex_obj _⟩ := by
  rw [descApp_apply s x.2.1 x (𝟙 _) (by simp), CategoryTheory.Functor.map_id, Category.id_comp,
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
    have h : X.toN (X.map f.op x) ≤ X.toN x := by
      rw [N.le_iff, ofSimplex_toN, ofSimplex_toN, Subpresheaf.ofSection_le_iff,
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
      yonedaEquiv_map_comp, Equiv.apply_symm_apply, map_toNπ_op_toN]

@[simp]
lemma desc_app_apply {n : ℕ} (x : X _⦋n⦌) :
    (desc s).app _ x = descApp _ x := rfl

@[reassoc (attr := simp)]
def fac (x : X.N) : (Subcomplex.ofSimplex x.2.1).ι ≫ desc s = s.ι.app x := by
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
  toFun x := Y.toN (f.app _ x.2.1)
  monotone' x x' h := by
    simp only [N.le_iff, ofSimplex_toN, Subpresheaf.ofSection_le_iff,
      mem_ofSimplex_obj_iff] at h ⊢
    obtain ⟨g, hf⟩ := h
    exact ⟨g, by simp only [← hf, FunctorToTypes.naturality]⟩

@[simp]
lemma mapN_toN {n : ℕ} (x : X _⦋n⦌) :
    mapN f (X.toN x) = Y.toN (f.app _ x) := by
  have : IsSplitEpi (X.toNπ x) := isSplitEpi_of_epi _
  simp only [mapN_coe]
  apply le_antisymm
  · simp only [N.le_iff, ofSimplex_toN, Subpresheaf.ofSection_le_iff,
      mem_ofSimplex_obj_iff]
    exact ⟨section_ (X.toNπ x), by rw [← FunctorToTypes.naturality, map_section_eq_toN_snd]⟩
  · simp only [N.le_iff, ofSimplex_toN, Subpresheaf.ofSection_le_iff,
      mem_ofSimplex_obj_iff]
    exact ⟨X.toNπ x, by rw [← FunctorToTypes.naturality, map_toNπ_op_toN]⟩

@[simp]
lemma id_app {n : SimplexCategoryᵒᵖ} (x : X.obj n) : NatTrans.app (𝟙 X) n x = x := rfl

@[simp]
lemma mapN_id : mapN (𝟙 X) = OrderHom.id := by
  ext x
  obtain ⟨n, x, rfl⟩ := X.toN_surjective x
  simp

lemma mapN_mapN {Z : SSet.{u}} (g : Y ⟶ Z) (x : X.N) :
    mapN g (mapN f x) = mapN (f ≫ g) x := by
  obtain ⟨n, x, rfl⟩ := X.toN_surjective x
  simp

end SSet
