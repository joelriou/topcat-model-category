module

public import TopCatModelCategory.PseudoFunctor.LaxNatTrans
public import TopCatModelCategory.PseudoFunctor.Pseudofunctor
public import TopCatModelCategory.Iso
public import TopCatModelCategory.MorphismProperty
public import TopCatModelCategory.CatCommSq
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Bicategory

namespace Pseudofunctor

section

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

@[simps]
def const (Y : C) : Pseudofunctor B C where
  obj _ := Y
  map _ := 𝟙 _
  map₂ _ := 𝟙 _
  mapId _ := Iso.refl _
  mapComp _ _ := (λ_ (𝟙 Y)).symm

variable {B} (F : Pseudofunctor B C)

instance (X : B) : IsIso (F.toLax.mapId X) := by dsimp; infer_instance
instance {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) : IsIso (F.toLax.mapComp f g) := by dsimp; infer_instance

end

end Pseudofunctor

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
  {F : Pseudofunctor (LocallyDiscrete B) Cat.{v₂, u₂}}

namespace MorphismProperty

section

variable (F)

def ofPseudofunctor : MorphismProperty B := fun _ _ f ↦ (F.map ⟨f⟩).toFunctor.IsEquivalence

@[simp]
lemma ofPseudofunctor_iff {X Y : B} (f : X ⟶ Y) :
    ofPseudofunctor F f ↔ (F.map ⟨f⟩).toFunctor.IsEquivalence := Iff.rfl

instance : (ofPseudofunctor F).IsMultiplicative where
  id_mem X := Functor.isEquivalence_of_iso (show _ ≅ 𝟭 _ from F.mapId ⟨X⟩).symm
  comp_mem f g hf hg := by
    rw [ofPseudofunctor_iff] at hf hg
    have : Functor.IsEquivalence (F.map ⟨f⟩ ⋙ F.map ⟨g⟩) := inferInstance
    exact Functor.isEquivalence_of_iso (F.mapComp ⟨f⟩ ⟨g⟩).symm

instance : (ofPseudofunctor F).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [ofPseudofunctor_iff] at hg hfg
    have := Functor.isEquivalence_of_iso (F.mapComp ⟨f⟩ ⟨g⟩)
    exact Functor.isEquivalence_of_comp_right (F.map ⟨f⟩) (F.map ⟨g⟩)
  of_precomp f g hf hfg := by
    rw [ofPseudofunctor_iff] at hf hfg
    have := Functor.isEquivalence_of_iso (F.mapComp ⟨f⟩ ⟨g⟩)
    exact Functor.isEquivalence_of_comp_left (F.map ⟨f⟩) (F.map ⟨g⟩)

instance : (ofPseudofunctor F).IsStableUnderRetracts where
  of_retract {X₁ X₂ Y₁ Y₂ f g} hf hg := by
    rw [ofPseudofunctor_iff] at hg ⊢
    let e₁ : F.map ⟨hf.i.left⟩ ⋙ F.map ⟨hf.r.left⟩ ≅ 𝟭 _ := by
      refine (F.mapComp' _ _ _ ?_).symm ≪≫ F.mapId ⟨X₁⟩
      rw [← Quiver.Hom.id_toLoc, ← hf.left.retract, Quiver.Hom.comp_toLoc]
      rfl
    let e₂ : F.map ⟨hf.i.right⟩ ⋙ F.map ⟨hf.r.right⟩ ≅ 𝟭 _ := by
      refine (F.mapComp' _ _ _ ?_).symm ≪≫ F.mapId ⟨X₂⟩
      rw [← Quiver.Hom.id_toLoc, ← hf.right.retract, Quiver.Hom.comp_toLoc]
      rfl
    have sq : CommSq hf.i.left f g hf.i.right := ⟨hf.i.w⟩
    have sq' : CommSq hf.r.left g f hf.r.right := ⟨hf.r.w⟩
    letI := F.catCommSqOfSq sq
    letI := F.catCommSqOfSq sq'
    apply Functor.isEquivalence_of_retract (e₁ := e₁) (e₂ := e₂) (F := F.map ⟨f⟩) (G := F.map ⟨g⟩)
    dsimp [CatCommSq.iso]
    ext X
    rw [← cancel_epi ((F.map ⟨f⟩).map ((F.mapComp' ⟨hf.i.left⟩ ⟨hf.r.left⟩ ⟨𝟙 _⟩
      (by rw [← hf.left.retract]; rfl)).hom.app X))]
    have := NatTrans.congr_app (congr_arg Iso.hom (F.isoMapOfSq'_horiz_comp
      sq sq' hf.left.retract hf.right.retract)) X
    dsimp [e₁, e₂] at this ⊢
    simp only [comp_id, id_comp] at this ⊢
    erw [← reassoc_of% this]
    rw [F.isoMapOfSq'_horiz_id f]
    dsimp
    erw [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    simp

end

section

variable (π : LaxNatTrans F.toLax (Pseudofunctor.const _ (Cat.of C)).toLax)

def ofLaxNatTrans : MorphismProperty B := fun _ _ f ↦ IsIso (π.naturality ⟨f⟩)

@[simp]
lemma ofLaxNatTrans_iff {X Y : B} (f : X ⟶ Y) :
    ofLaxNatTrans π f ↔ IsIso (π.naturality ⟨f⟩) := Iff.rfl

lemma ofLaxNatTrans_iff_isIso_app {X Y : B} (f : X ⟶ Y) :
    ofLaxNatTrans π f ↔ ∀ (x : F.obj ⟨X⟩), IsIso ((π.naturality ⟨f⟩).app x) := by
  rw [ofLaxNatTrans_iff, NatTrans.isIso_iff_isIso_app]
  rfl

instance : (ofLaxNatTrans π).IsMultiplicative where
  id_mem X := by
    have := π.naturality_id ⟨X⟩
    dsimp at this
    simp only [Bicategory.whiskerLeft_id, id_comp] at this
    change IsIso (π.naturality (𝟙 { as := X }))
    rw [this]
    infer_instance
  comp_mem {X Y Z} f g hf hg := by
    simp only [ofLaxNatTrans_iff] at hf hg ⊢
    have := π.naturality_comp ⟨f⟩ ⟨g⟩
    dsimp at this
    simp only [unitors_equal, whiskerLeft_rightUnitor, assoc, Bicategory.whiskerRight_id,
      Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left] at this
    change IsIso (π.naturality ({ as := f } ≫ { as := g }))
    rw [this]
    infer_instance

instance : (ofLaxNatTrans π).HasOfPostcompProperty (ofLaxNatTrans π) where
  of_postcomp {X Y Z} f g hg hfg := by
    simp only [ofLaxNatTrans_iff_isIso_app] at hg hfg ⊢
    intro x
    have := NatTrans.congr_app (π.naturality_comp ⟨f⟩ ⟨g⟩) x
    dsimp [Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app] at this
    simp only [id_comp] at this
    replace hfg : IsIso ((π.naturality (⟨f⟩ ≫ ⟨g⟩)).app x) := hfg x
    simpa [this] using hfg

instance : (ofPseudofunctor F ⊓ ofLaxNatTrans π).HasTwoOutOfThreeProperty where
  of_postcomp {X Y Z} f g hg hfg :=
    ⟨(ofPseudofunctor F).of_postcomp _ _ hg.1 hfg.1,
      (ofLaxNatTrans π).of_postcomp _ _ hg.2 hfg.2⟩
  of_precomp := by
    rintro X Y Z f g ⟨hf₁, hf₂⟩ ⟨hfg₁, hfg₂⟩
    refine ⟨(ofPseudofunctor F).of_precomp _ _ hf₁ hfg₁, ?_⟩
    simp only [ofPseudofunctor_iff ] at hf₁
    simp only [ofLaxNatTrans_iff_isIso_app] at hf₂ hfg₂ ⊢
    rintro y
    obtain ⟨x, ⟨e⟩⟩ : ∃ (x : F.obj ⟨X⟩), Nonempty ((F.map ⟨f⟩).obj x ≅ y) :=
      ⟨_, ⟨(F.map ⟨f⟩).objObjPreimageIso y⟩⟩
    have := NatTrans.congr_app (π.naturality_comp ⟨f⟩ ⟨g⟩) x
    dsimp [Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app] at this
    simp only [id_comp] at this
    simpa [NatTrans.isIso_app_iff_of_iso _ e.symm, this] using
      (show IsIso ((π.naturality (⟨f⟩ ≫ ⟨g⟩)).app x) from hfg₂ x)

end

section

variable {ι : Type*} (π : ι → LaxNatTrans F.toLax (Pseudofunctor.const _ (Cat.of C)).toLax)

def ofLaxNatTransFamily : MorphismProperty B :=
  (ofPseudofunctor F ⊓ ⨅ (i : ι), ofLaxNatTrans (π i))

instance : (ofLaxNatTransFamily π).IsMultiplicative := by
  dsimp [ofLaxNatTransFamily]
  infer_instance

@[simp]
lemma ofLaxNatTransFamily_iff {X Y : B} (f : X ⟶ Y) :
    ofLaxNatTransFamily π f ↔ ofPseudofunctor F f ∧ ∀ i, ofLaxNatTrans (π i) f := by
  simp only [ofLaxNatTransFamily, ofPseudofunctor_iff, min_iff, iInf_iff]

instance : (ofLaxNatTransFamily π).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    simp only [ofLaxNatTransFamily_iff] at hg hfg ⊢
    exact ⟨(ofPseudofunctor F).of_postcomp f g hg.1 hfg.1,
      fun i ↦ (ofLaxNatTrans (π i)).of_postcomp f g (hg.2 i) (hfg.2 i)⟩
  of_precomp f g hf hfg := by
    simp only [ofLaxNatTransFamily_iff] at hf hfg ⊢
    refine ⟨(ofPseudofunctor F).of_precomp f g hf.1 hfg.1, fun i ↦ ?_⟩
    have : (ofPseudofunctor F ⊓ ofLaxNatTrans (π i)) f := ⟨hf.1, hf.2 i⟩
    exact ((ofPseudofunctor F ⊓ ofLaxNatTrans (π i)).of_precomp f g this
      (⟨hfg.1, hfg.2 i⟩)).2

end

end MorphismProperty

end CategoryTheory
