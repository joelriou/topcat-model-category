module

public import TopCatModelCategory.SSet.FundamentalGroupoid
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

@[expose] public section

universe u

namespace SSet

open CategoryTheory Bicategory HomotopicalAlgebra modelCategoryQuillen

abbrev KanComplexCat := ObjectProperty.FullSubcategory (C := SSet.{u})
  (fun X ↦ IsFibrant X)

def KanComplexCat.mk (X : SSet.{u}) [IsFibrant X] : KanComplexCat := ⟨X, inferInstance⟩

namespace KanComplex

instance (X : KanComplexCat) : IsFibrant X.1 := X.2

namespace FundamentalGroupoid

lemma mapFundamentalGroupoid_associator {X Y Z T : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    [IsFibrant Z] [IsFibrant T] (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (compMapFundamentalGroupoidIso (f ≫ g) h).hom ≫
    Functor.whiskerRight (compMapFundamentalGroupoidIso f g).hom _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (compMapFundamentalGroupoidIso g h).inv ≫
          (compMapFundamentalGroupoidIso f (g ≫ h)).inv = 𝟙 _ := by
  ext x
  simp [compMapFundamentalGroupoidIso]

lemma mapFundamentalGroupoid_left_unitor {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    (compMapFundamentalGroupoidIso (𝟙 X) f).hom ≫
      Functor.whiskerRight (idMapFundamentalGroupoidIso X).hom _ ≫
        (Functor.leftUnitor (mapFundamentalGroupoid f)).hom =
      𝟙 (mapFundamentalGroupoid f) := by
  ext x
  simp [compMapFundamentalGroupoidIso, compMapFundamentalGroupoidIso']
  rfl

lemma mapFundamentalGroupoid_right_unitor {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    (compMapFundamentalGroupoidIso f (𝟙 Y)).hom ≫
      Functor.whiskerLeft _ (idMapFundamentalGroupoidIso Y).hom ≫
        (Functor.rightUnitor (mapFundamentalGroupoid f)).hom =
      𝟙 (mapFundamentalGroupoid f) := by
  ext x
  simp [compMapFundamentalGroupoidIso, compMapFundamentalGroupoidIso']
  rfl

noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete (KanComplexCat.{u})) Cat.{u, u} :=
  pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ ↦ Cat.of (FundamentalGroupoid X.1))
    (fun ⟨f⟩ ↦ mapFundamentalGroupoid f)
    (fun ⟨X⟩ ↦ idMapFundamentalGroupoidIso X.1)
    (fun ⟨f⟩ ⟨g⟩ ↦ compMapFundamentalGroupoidIso f g)
    (fun ⟨f⟩ ⟨g⟩ ⟨h⟩ ↦ mapFundamentalGroupoid_associator f g h)
    (fun ⟨f⟩ ↦ mapFundamentalGroupoid_left_unitor f)
    (fun ⟨f⟩ ↦ mapFundamentalGroupoid_right_unitor f)

end FundamentalGroupoid

end KanComplex

end SSet
