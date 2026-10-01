module

public import Mathlib.CategoryTheory.Elements

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

@[simps!]
def mapCompIso {F₁ F₂ F₃ : C ⥤ Type w} (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    f.mapElements ⋙ g.mapElements ≅ (f ≫ g).mapElements :=
  NatIso.ofComponents (fun _ ↦ Functor.Elements.isoMk (Iso.refl _))

@[simps!]
def mapId' {F : C ⥤ Type w} (f : F ⟶ F) (hf : f = 𝟙 _ := by cat_disch) :
    f.mapElements ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x ↦ Functor.Elements.isoMk (Iso.refl _))

end CategoryOfElements

open CategoryOfElements

@[simps]
def Elements.equivalenceOfIso {F G : C ⥤ Type w} (e : F ≅ G) :
    F.Elements ≌ G.Elements where
  functor := e.hom.mapElements
  inverse := e.inv.mapElements
  unitIso := (mapId' _).symm ≪≫ (mapCompIso _ _ ).symm
  counitIso := (mapCompIso _ _ ) ≪≫ mapId' _

end CategoryTheory
