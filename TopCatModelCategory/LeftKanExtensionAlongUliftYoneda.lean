import Mathlib.CategoryTheory.Limits.Presheaf

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Limits

namespace Limits

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} (c : Cocone F)

lemma nonempty_isColimit_cocone_iff_of_isTerminal {X : C} (hX : IsTerminal X) :
    Nonempty (IsColimit c) ↔ IsIso (c.ι.app X) := by
  constructor
  · rintro ⟨hc⟩
    let s : Cocone F :=
      { pt := F.obj X
        ι :=
          { app Y := F.map (hX.from Y)
            naturality _ _ _ := by simp [← F.map_comp] } }
    exact ⟨hc.desc s, by aesop_cat, hc.hom_ext (fun Y ↦ by aesop_cat)⟩
  · intro
    exact ⟨{
      desc s := inv (c.ι.app X) ≫ s.ι.app X
      fac s Y := by
        rw [← c.w_assoc (hX.from Y), IsIso.hom_inv_id_assoc, s.w]
      uniq s m hm := by simp [← hm X]
    }⟩

end Limits

section

variable {C : Type u₁} [Category.{v₁} C]

@[simps]
def uliftYoneda.initialElement (X : C) :
    (uliftYoneda.{w}.obj X).Elements :=
  Functor.elementsMk (uliftYoneda.{w}.obj X) (op X) (uliftYonedaEquiv (𝟙 _))

def uliftYoneda.isInitialInitialElement (X : C) :
    IsInitial (initialElement.{w} X) :=
  IsInitial.ofUniqueHom (fun e ↦ CategoryOfElements.homMk _ _ e.2.down.op
    (ULift.down_injective (by simp [uliftYonedaEquiv]))) (by
      rintro e ⟨f, hf⟩
      dsimp at f hf
      ext
      simp [← hf, uliftYonedaEquiv])

end

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : C ⥤ D}

variable (E : Functor.LeftExtension uliftYoneda.{w} A)

section

variable (P : Cᵒᵖ ⥤ Type max w v₁)

@[simps]
def coconeOfLeftExtension :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ A) where
  pt := E.right.obj P
  ι :=
    { app e := E.hom.app e.unop.1.unop ≫ E.right.map (uliftYonedaEquiv.symm e.unop.2)
      naturality {e e'} f := by
        dsimp
        simp only [NatTrans.naturality_assoc, Functor.comp_obj, Functor.comp_map,
          Category.comp_id, ← Functor.map_comp]
        congr
        rw [← uliftYonedaEquiv_symm_map, CategoryOfElements.map_snd] }

variable {E P} in
def isColimitCoconeOfLeftExtensionEquiv :
     IsColimit (coconeOfLeftExtension E P) ≃
      (E.IsPointwiseLeftKanExtensionAt P) := by
  refine Equiv.trans ?_
    (IsColimit.whiskerEquivalenceEquiv
      (CategoryOfElements.costructuredArrowULiftYonedaEquivalence.{w} P)).symm
  exact (IsColimit.equivOfNatIsoOfIso (Iso.refl _) _ _ (Cocones.ext (Iso.refl _)))

lemma nonempty_coconeOfLextExtension_iff :
    Nonempty (IsColimit (coconeOfLeftExtension E P)) ↔
      Nonempty (E.IsPointwiseLeftKanExtensionAt P) :=
  isColimitCoconeOfLeftExtensionEquiv.nonempty_congr

end

lemma nonempty_isPointwiseLeftKanExtensionAt_uliftYoneda_obj_iff (X : C) :
    Nonempty (E.IsPointwiseLeftKanExtensionAt (uliftYoneda.{w}.obj X)) ↔
      IsIso (E.hom.app X) := by
  simp [← nonempty_coconeOfLextExtension_iff,
    nonempty_isColimit_cocone_iff_of_isTerminal _
    (terminalOpOfInitial (uliftYoneda.isInitialInitialElement.{w} X))]

lemma isPointwiseLeftKanExtensionAt_iff_of_isIso [IsIso E.hom]
    (P : Cᵒᵖ ⥤ Type max w v₁) :
    Nonempty (E.IsPointwiseLeftKanExtensionAt P) ↔
      PreservesColimit (functorToRepresentables P) E.right := by
  rw [← nonempty_coconeOfLextExtension_iff]
  trans Nonempty (IsColimit (E.right.mapCocone (coconeOfRepresentable P)))
  · exact (IsColimit.equivOfNatIsoOfIso
      (Functor.isoWhiskerLeft (CategoryOfElements.π P).leftOp (asIso E.hom)) _ _
        (by exact Cocones.ext (Iso.refl _))).nonempty_congr
  · constructor
    · rintro ⟨h⟩
      exact preservesColimit_of_preserves_colimit_cocone (colimitOfRepresentable P) h
    · intro
      exact ⟨isColimitOfPreserves E.right (colimitOfRepresentable P)⟩

lemma isPointwiseLeftKanExtension_along_uliftYoneda_iff_isIso_and_preservesColimit :
    Nonempty E.IsPointwiseLeftKanExtension ↔
      (IsIso E.hom ∧ ∀ (P : Cᵒᵖ ⥤ Type max w v₁),
        PreservesColimit (functorToRepresentables P) E.right) := by
  constructor
  · rintro ⟨h⟩
    have : IsIso E.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro P
      rw [← nonempty_isPointwiseLeftKanExtensionAt_uliftYoneda_obj_iff]
      exact ⟨h _⟩
    exact ⟨inferInstance, fun P ↦ (isPointwiseLeftKanExtensionAt_iff_of_isIso E P).1 ⟨h P⟩⟩
  · rintro ⟨_, h⟩
    refine ⟨fun P ↦ Nonempty.some ?_⟩
    rw [isPointwiseLeftKanExtensionAt_iff_of_isIso]
    apply h

/-lemma isPointwiseLeftKanExtension_along_uliftYoneda_iff_isIso_and_preservesColimitsOfSize :
    Nonempty E.IsPointwiseLeftKanExtension ↔
      (IsIso E.hom ∧ PreservesColimitsOfSize.{v₁, max w u₁ v₁} E.right) := by
  sorry-/

lemma isLeftKanExtension_along_uliftYoneda_iff'
    [uliftYoneda.{w}.HasPointwiseLeftKanExtension A]
    (L : (Cᵒᵖ ⥤ Type (max w v₁)) ⥤ D)
    (α : A ⟶ uliftYoneda.{w} ⋙ L) :
    L.IsLeftKanExtension α ↔ IsIso α ∧
      ∀ (P : Cᵒᵖ ⥤ Type max w v₁),
        PreservesColimit (functorToRepresentables P) L := by
  have := isPointwiseLeftKanExtension_along_uliftYoneda_iff_isIso_and_preservesColimit (Functor.LeftExtension.mk _ α)
  dsimp at this
  rw [← this]
  constructor
  · intro h
    exact ⟨Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _⟩
  · rintro ⟨h⟩
    exact h.isLeftKanExtension

/-lemma isLeftKanExtension_along_uliftYoneda_iff''
    [uliftYoneda.{w}.HasPointwiseLeftKanExtension A]
    (L : (Cᵒᵖ ⥤ Type (max w v₁)) ⥤ D)
    (α : A ⟶ uliftYoneda.{w} ⋙ L) :
    L.IsLeftKanExtension α ↔ IsIso α ∧
      Limits.PreservesColimitsOfSize.{v₁, max w u₁ v₁} L := by
  have := isPointwiseLeftKanExtension_along_uliftYoneda_iff (Functor.LeftExtension.mk _ α)
  dsimp at this
  rw [← this]
  constructor
  · intro h
    exact ⟨Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _⟩
  · rintro ⟨h⟩
    exact h.isLeftKanExtension-/


end Presheaf

end CategoryTheory
