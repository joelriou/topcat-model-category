import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.Skeleton
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe u

open CategoryTheory MonoidalCategory Limits Simplicial HomotopicalAlgebra
  ChosenFiniteProducts SSet.modelCategoryQuillen

namespace SSet

/-namespace horn₁₁

lemma eq_face : horn.{u} 1 1 = stdSimplex.face {1} := by
  rw [horn_eq_iSup]
  letI : Unique ({1}ᶜ : Set (Fin 2)) :=
    { default := ⟨0, by simp⟩
      uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
  rw [iSup_unique]
  rfl

lemma ι_eq : (horn.{u} 1 1).ι = const.{u} (stdSimplex.obj₀Equiv.{u}.symm 1) := by
  rw [← Subcomplex.isoOfEq_hom_ι eq_face, stdSimplex.face_singleton_eq_const, comp_const]

noncomputable def iso : Δ[0] ≅ (horn 1 1 : SSet.{u}) :=
  stdSimplex.faceSingletonIso _ ≪≫ Subcomplex.isoOfEq eq_face.symm

@[reassoc (attr := simp)]
lemma iso_hom_ι : iso.{u}.hom ≫ Λ[1, 1].ι = stdSimplex.δ 0 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

end horn₁₁-/

section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)

abbrev PushoutTensor := Functor.PushoutObjObj (curriedTensor SSet.{u}) f₁ f₂

namespace PushoutTensor

section

variable {f₁ f₂} (h : PushoutTensor f₁ f₂)

@[simps]
noncomputable def flip : PushoutTensor f₂ f₁ where
  pt := h.pt
  inl := (β_ _ _).hom ≫ h.inr
  inr := (β_ _ _).hom ≫ h.inl
  isPushout := h.isPushout.flip.of_iso (β_ _ _) (β_ _ _) (β_ _ _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι_flip : h.inl ≫ h.flip.ι = (β_ _ _).hom ≫ f₂ ▷ _ := by
  rw [← cancel_epi (β_ _ _).hom]
  simpa using h.flip.inr_ι

@[reassoc (attr := simp)]
lemma inr_ι_flip : h.inr ≫ h.flip.ι = (β_ _ _).hom ≫ _ ◁ f₁ := by
  rw [← cancel_epi (β_ _ _).hom]
  simpa using h.flip.inl_ι

@[reassoc]
lemma ι_flip : h.flip.ι = h.ι ≫ (β_ _ _).hom := by
  apply h.isPushout.hom_ext <;> simp

noncomputable def flipArrowIso : Arrow.mk h.flip.ι ≅ Arrow.mk h.ι :=
  Arrow.isoMk (Iso.refl _) (β_ _ _) (by simp [ι_flip])

end

section

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)

@[simps]
noncomputable def unionProd : PushoutTensor A.ι B.ι where
  pt := A.unionProd B
  inl := Subcomplex.unionProd.ι₁ A B
  inr := Subcomplex.unionProd.ι₂ A B
  isPushout := Subcomplex.unionProd.isPushout _ _

@[simp]
lemma ι_unionProd : (unionProd A B).ι = (A.unionProd B).ι := by
  apply (unionProd A B).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    dsimp
  · rw [Functor.PushoutObjObj.inr_ι]
    dsimp

end

section

variable {X Y : SSet.{u}} (i : X ⟶ Y)

@[simps]
noncomputable def horn₁₁ :
    PushoutTensor i (horn.{u} 1 1).ι where
  pt := pushout i ι₁
  inl := fst _ _ ≫ pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := (IsPushout.of_hasPushout i ι₁).of_iso
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ (horn₁.iso 1)))
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ (horn₁.iso 1)))
      (Iso.refl _) (Iso.refl _) (by aesop_cat) (by
        dsimp
        rw [Category.comp_id, id_tensorHom, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, horn₁.iso₁_hom_ι]
        rfl) (by simp) (by simp)

lemma ι_horn₁₁ : (horn₁₁ i).ι = pushout.desc ι₁ (i ▷ Δ[1]) (by simp) := by
  apply (horn₁₁ i).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    dsimp
    rw [Category.assoc, pushout.inl_desc, horn₁.ι_eq]
    rfl
  · rw [Functor.PushoutObjObj.inr_ι]
    dsimp
    rw [pushout.inr_desc]

@[simps]
noncomputable def horn₁₀ :
    PushoutTensor i (horn.{u} 1 0).ι where
  pt := pushout i ι₀
  inl := fst _ _ ≫ pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := (IsPushout.of_hasPushout i ι₀).of_iso
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ (horn₁.iso 0)))
      ((stdSimplex.rightUnitor _).symm ≪≫ (Iso.refl _ ⊗ (horn₁.iso 0)))
      (Iso.refl _) (Iso.refl _) (by aesop_cat) (by
        dsimp
        rw [Category.comp_id, id_tensorHom, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, horn₁.iso₀_hom_ι]
        rfl) (by simp) (by simp)

lemma ι_horn₁₀ : (horn₁₀ i).ι = pushout.desc ι₀ (i ▷ Δ[1]) (by simp) := by
  apply (horn₁₀ i).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    dsimp
    rw [Category.assoc, pushout.inl_desc, horn₁.ι_eq]
    rfl
  · rw [Functor.PushoutObjObj.inr_ι]
    dsimp
    rw [pushout.inr_desc]

end

end PushoutTensor

section

variable {X₁ X₂ X₃ : SSet.{u}} (A₁ : X₁.Subcomplex) (A₂ : X₂.Subcomplex) (A₃ : X₃.Subcomplex)

noncomputable abbrev Subcomplex.unionProd₃ : (X₁ ⊗ X₂ ⊗ X₃).Subcomplex :=
  A₁.unionProd (A₂.unionProd A₃)

noncomputable abbrev Subcomplex.unionProd₃.ι₁ :
    X₁ ⊗ (A₂.unionProd A₃) ⟶ unionProd₃ A₁ A₂ A₃ :=
  Subcomplex.unionProd.ι₁ _ _

noncomputable abbrev Subcomplex.unionProd₃.ι₂₃ :
    (A₁ : SSet) ⊗ X₂ ⊗ X₃ ⟶ unionProd₃ A₁ A₂ A₃ :=
  Subcomplex.unionProd.ι₂ _ _

namespace Subcomplex.unionProd

noncomputable def assocIso :
    ((A₁.unionProd A₂).unionProd A₃ : SSet) ≅ unionProd₃ A₁ A₂ A₃ where
  hom := Subcomplex.lift (((A₁.unionProd A₂).unionProd A₃).ι ≫ (α_ _ _ _).hom) (by
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, image_top]
    rintro n x ⟨⟨⟨⟨x₁, x₂⟩, x₃⟩, hx⟩, rfl⟩
    simp only [comp_app, Subpresheaf.toPresheaf_obj, types_comp_apply, Subpresheaf.ι_app,
      associator_hom_app_apply]
    simp only [mem_unionProd_iff] at hx ⊢
    tauto)
  inv := Subcomplex.lift ((unionProd₃ A₁ A₂ A₃).ι ≫ (α_ _ _ _).inv) (by
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, image_top]
    rintro n x ⟨⟨⟨x₁, x₂, x₃⟩, hx⟩, rfl⟩
    simp only [mem_unionProd_iff] at hx ⊢
    tauto)
  hom_inv_id := rfl
  inv_hom_id := rfl

noncomputable def assocArrowIso :
    Arrow.mk ((A₁.unionProd A₂).unionProd A₃).ι ≅ Arrow.mk (unionProd₃ A₁ A₂ A₃).ι :=
  Arrow.isoMk (assocIso _ _ _) (α_ _ _ _)

end Subcomplex.unionProd

noncomputable def PushoutTensor.unionProd₃ : PushoutTensor A₁.ι (A₂.unionProd A₃).ι where
  pt := Subcomplex.unionProd₃ A₁ A₂ A₃
  inl := Subcomplex.unionProd₃.ι₁ _ _ _
  inr := Subcomplex.unionProd₃.ι₂₃ _ _ _
  isPushout := (PushoutTensor.unionProd A₁ (A₂.unionProd A₃)).isPushout

@[simp]
lemma PushoutTensor.ι_unionProd₃ :
    (unionProd₃ A₁ A₂ A₃).ι = (Subcomplex.unionProd₃ A₁ A₂ A₃).ι :=
  PushoutTensor.ι_unionProd A₁ (A₂.unionProd A₃)

end

variable {X Y : SSet.{u}} (f₃ : X ⟶ Y)

abbrev PullbackIhom := Functor.PullbackObjObj MonoidalClosed.internalHom f₁ f₃

end

lemma hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
    {A₁ A₂ B₁ B₂ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂} (h₁₂ : PushoutTensor f₁ f₂)
    {X Y : SSet.{u}} {f₃ : X ⟶ Y} (h₁₃ : PullbackIhom f₁ f₃) :
    HasLiftingProperty h₁₂.ι f₃ ↔ HasLiftingProperty f₂ h₁₃.π :=
  MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff h₁₂ h₁₃

open MorphismProperty in
lemma anodyneExtensions.pushoutTensorι₂' {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (k : Fin 2)
    (h : PushoutTensor i (horn 1 k).ι) :
    anodyneExtensions h.ι := by
  intro X Y p hp
  rw [← HomotopicalAlgebra.fibration_iff] at hp
  have H : PullbackIhom Λ[1, k].ι p := Functor.PullbackObjObj.ofHasPullback _ _ _
  suffices (monomorphisms _).rlp H.π by
    rw [← HasLiftingProperty.iff_of_arrow_iso_left h.flipArrowIso,
      hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom _ H]
    exact this _ (monomorphisms.infer_property _)
  rw [← modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp]
  rintro _ _ _ ⟨n⟩
  rw [← hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom (PushoutTensor.unionProd _ _)]
  dsimp
  simp
  apply anodyneExtensions.hasLeftLiftingProperty
  -- this should be improved...
  fin_cases k
  · convert subcomplex_unionProd_face_boundary_ι_mem n 0 <;> apply horn₁.eq_face
  · convert subcomplex_unionProd_face_boundary_ι_mem n 1 <;> apply horn₁.eq_face

lemma hornOneUnionProdInclusions_le_anodyneExtensions :
    hornOneUnionProdInclusions.{u} ≤ anodyneExtensions := by
  rintro _ _ i hi
  simp [hornOneUnionProdInclusions] at hi
  obtain ⟨k, X, ⟨A⟩⟩ := hi
  simpa using anodyneExtensions.pushoutTensorι₂' A.ι k (PushoutTensor.unionProd _ _)

open MorphismProperty in
lemma hornOneUnionProdInclusions_rlp :
    hornOneUnionProdInclusions.{u}.rlp = fibrations SSet := by
  apply le_antisymm
  · simpa using antitone_rlp modelCategoryQuillen.J_le_hornOneUnionProdInclusions
  · rw [← le_llp_iff_le_rlp]
    apply hornOneUnionProdInclusions_le_anodyneExtensions


namespace fibrations

section

variable {B S T : SSet.{u}} {A : B.Subcomplex} {p : S ⟶ T} (h : PullbackIhom A.ι p)

lemma hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ' [Fibration p]
    {Y : SSet.{u}} (X : Y.Subcomplex) (k : Fin 2) :
    HasLiftingProperty (X.unionProd Λ[1, k]).ι h.π := by
  rw [← hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
    (PushoutTensor.unionProd₃ A X Λ[1, k]), PushoutTensor.ι_unionProd₃]
  dsimp
  have hp : fibrations _ p := by rwa [← HomotopicalAlgebra.fibration_iff]
  rw [← hornOneUnionProdInclusions_rlp] at hp
  have := hp _ (mem_hornOneUnionProdInclusions k (A.unionProd X))
  apply HasLiftingProperty.of_arrow_iso_left (Subcomplex.unionProd.assocArrowIso _ _ _)

end

section

variable {A B S T : SSet.{u}} {i : A ⟶ B} {p : S ⟶ T} (h : PullbackIhom i p)

open MonoidalClosed in
lemma hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ [Mono i] [Fibration p]
    {Y : SSet.{u}} (X : Y.Subcomplex) (k : Fin 2) :
    HasLiftingProperty (X.unionProd Λ[1, k]).ι h.π := by
  let h' : PullbackIhom (Subcomplex.range i).ι p :=
    { pt := h.pt
      fst := h.fst ≫ (pre (inv (Subpresheaf.toRange i))).app _
      snd := h.snd
      isPullback := by
        fapply h.isPullback.of_iso (Iso.refl _)
          ((internalHom.mapIso (asIso (Subpresheaf.toRange i)).symm.op).app S) (Iso.refl _)
          ((internalHom.mapIso (asIso (Subpresheaf.toRange i)).symm.op).app T)
          (by simp) (by simp) (by simp) ?_
        · dsimp
          rw [Category.id_comp, ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
          congr 2
          simp }
  have H := hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ' h' X k
  have : h'.π = h.π := by
    apply h'.isPullback.hom_ext
    · rw [h'.π_fst]
      dsimp [h']
      rw [h.π_fst_assoc]
      dsimp
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
      congr 2
      simp
    · rw [h'.π_snd]
      dsimp [h']
      rw [h.π_snd]
      dsimp
  rwa [this] at H

instance [Mono i] [Fibration p] : Fibration h.π := by
  rw [HomotopicalAlgebra.fibration_iff, ← hornOneUnionProdInclusions_rlp]
  intro _ _ _ hj
  simp only [hornOneUnionProdInclusions, MorphismProperty.iSup_iff] at hj
  obtain ⟨_, _, ⟨_⟩⟩ := hj
  apply hasLiftingProperty_unionProd_horn₁_ι_pullbackIhomπ

end

end fibrations

namespace anodyneExtensions

section

variable {A₁ A₂ B₁ B₂ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}

variable (h₁₂ : PushoutTensor f₁ f₂)

lemma pushoutTensorι₂ [Mono f₁] (hf₂ : anodyneExtensions f₂) : anodyneExtensions h₁₂.ι := by
  dsimp [anodyneExtensions]
  intro X Y p hp
  rw [← HomotopicalAlgebra.fibration_iff] at hp
  let h₁₃ : PullbackIhom f₁ p := Functor.PullbackObjObj.ofHasPullback _ _ _
  rw [hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom _ h₁₃]
  apply hf₂.hasLeftLiftingProperty

lemma pushoutTensorι₁ [Mono f₂] (hf₁ : anodyneExtensions f₁) : anodyneExtensions h₁₂.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1 (pushoutTensorι₂ h₁₂.flip hf₁)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _) (by simp [PushoutTensor.ι_flip])

end

lemma subcomplex_unionProd_mem_of_left {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using pushoutTensorι₁ (PushoutTensor.unionProd A B) hA

lemma subcomplex_unionProd_mem_of_right {X Y : SSet.{u}}
    (A : X.Subcomplex) (B : Y.Subcomplex) (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _))).2
    (subcomplex_unionProd_mem_of_left B A hB)

lemma pushout_desc_ι₁_whiskerRight_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    anodyneExtensions (pushout.desc (f := i) (g := ι₁) ι₁ (i ▷ Δ[1]) (by simp)) := by
  rw [← PushoutTensor.ι_horn₁₁]
  exact pushoutTensorι₂ (PushoutTensor.horn₁₁ i) (horn_ι_mem 0 1)

lemma pushout_desc_ι₀_whiskerRight_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    anodyneExtensions (pushout.desc (f := i) (g := ι₀) ι₀ (i ▷ Δ[1]) (by simp)) := by
  rw [← PushoutTensor.ι_horn₁₀]
  exact pushoutTensorι₂ (PushoutTensor.horn₁₀ i) (horn_ι_mem 0 0)

lemma face (i : Fin 2) : anodyneExtensions.{u} (stdSimplex.face ({i})).ι := by
  rw [← horn₁.eq_face i]
  exact horn_ι_mem 0 i

end anodyneExtensions

end SSet
