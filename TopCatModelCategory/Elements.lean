import Mathlib.CategoryTheory.Elements

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

@[simps!]
def mapCompIso {F₁ F₂ F₃ : C ⥤ Type w} (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    map f ⋙ map g ≅ map (f ≫ g) :=
  NatIso.ofComponents (fun _ ↦ isoMk _ _ (Iso.refl _) (by simp))

@[simps!]
def mapId' {F : C ⥤ Type w} (f : F ⟶ F) (hf : f = 𝟙 _ := by cat_disch) :
    map f ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x ↦ isoMk _ _ (Iso.refl _) (by simp [hf]))

end CategoryOfElements

open CategoryOfElements

@[simps]
def Elements.equivalenceOfIso {F G : C ⥤ Type w} (e : F ≅ G) :
    F.Elements ≌ G.Elements where
  functor := map e.hom
  inverse := map e.inv
  unitIso := (mapId' _).symm ≪≫ (mapCompIso _ _ ).symm
  counitIso := (mapCompIso _ _ ) ≪≫ mapId' _

end CategoryTheory
