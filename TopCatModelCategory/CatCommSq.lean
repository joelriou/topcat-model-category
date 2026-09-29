module

public import Mathlib.CategoryTheory.CatCommSq

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ D₁ D₁ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂)
  {i₁ : C₁ ⥤ D₁} {r₁ : D₁ ⥤ C₁} (e₁ : i₁ ⋙ r₁ ≅ 𝟭 C₁)
  {i₂ : C₂ ⥤ D₂} {r₂ : D₂ ⥤ C₂} (e₂ : i₂ ⋙ r₂ ≅ 𝟭 C₂)
  [CatCommSq i₁ F G i₂] [CatCommSq r₁ G F r₂]
  (h : isoWhiskerRight e₁ F = Functor.associator _ _ _ ≪≫
    isoWhiskerLeft i₁ (CatCommSq.iso r₁ G F r₂) ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (CatCommSq.iso i₁ F G i₂) r₂ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F e₂ ≪≫ F.rightUnitor ≪≫ F.leftUnitor.symm)

variable (i₂) in
include e₁ i₂ in
lemma faithful_of_retract [G.Faithful] : F.Faithful where
  map_injective {X Y f g} h := by
    have : i₁.map f = i₁.map g := G.map_injective (by
      have h₁ := NatIso.naturality_2 (CatCommSq.iso i₁ F G i₂) f
      have h₂ := NatIso.naturality_2 (CatCommSq.iso i₁ F G i₂) g
      dsimp at h₁ h₂
      rw [← h₁, ← h₂, h])
    have h₁ := NatIso.naturality_1 e₁ f
    have h₂ := NatIso.naturality_1 e₁ g
    dsimp at h₁ h₂
    rw [← h₁, ← h₂, this]

include h in
lemma full_of_retract [G.Full] : F.Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := G.map_surjective
      ((CatCommSq.iso i₁ F G i₂).hom.app X ≫ i₂.map f ≫ (CatCommSq.iso i₁ F G i₂).inv.app Y)
    refine ⟨e₁.inv.app X ≫ r₁.map g ≫ e₁.hom.app Y, ?_⟩
    have h₁ := NatIso.naturality_2 (CatCommSq.iso r₁ G F r₂) g
    have h₂ := congr_app (congr_arg Iso.hom h) Y
    have h₃ := congr_app (congr_arg Iso.inv h) X
    have h₄ := NatIso.naturality_1 e₂ f
    dsimp at h₁ h₂ h₃ h₄
    simp only [hg, ← h₁, h₂, h₃, h₄, F.map_comp, ← r₂.map_comp_assoc, comp_obj,
      Category.comp_id, Category.id_comp, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

variable (r₁) in
include e₂ i₂ r₁ in
lemma essSurj_of_retract [G.EssSurj] : F.EssSurj where
  mem_essImage X₂ := by
    obtain ⟨Y₁, ⟨e⟩⟩ : ∃ (Y₁ : D₁), Nonempty (G.obj Y₁ ≅ i₂.obj X₂) :=
      ⟨_, ⟨G.objObjPreimageIso (i₂.obj X₂)⟩⟩
    exact ⟨r₁.obj Y₁, ⟨(CatCommSq.iso r₁ G F r₂).app Y₁ ≪≫ r₂.mapIso e ≪≫ e₂.app X₂⟩⟩

include h in
lemma isEquivalence_of_retract [G.IsEquivalence] : F.IsEquivalence where
  faithful := faithful_of_retract F G e₁ i₂
  full := full_of_retract F G e₁ e₂ h
  essSurj := essSurj_of_retract F G r₁ e₂

end Functor

end CategoryTheory
