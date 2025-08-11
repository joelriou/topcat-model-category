import Mathlib.Topology.CompactOpen
import Mathlib.CategoryTheory.Closed.Monoidal
import TopCatModelCategory.TopCat.Monoidal

universe v' u' u

open CategoryTheory MonoidalCategory Limits

namespace TopCat

variable {X Y Z : TopCat.{u}}

variable (X) in
@[simps]
protected def ihom : TopCat.{u} ⥤ TopCat.{u} where
  obj Y := TopCat.of C(X, Y)
  map f := ofHom ⟨_, ContinuousMap.continuous_postcomp f.hom⟩

variable [LocallyCompactSpace X]

def ihomEquiv : (X ⊗ Y ⟶ Z) ≃ (Y ⟶ X.ihom.obj Z) where
  toFun f := ofHom (ContinuousMap.curry (((β_ _ _).hom ≫ f).hom))
  invFun g := (β_ _ _).hom ≫ ofHom (ContinuousMap.uncurry g.hom)
  left_inv _ := rfl
  right_inv _ := rfl

variable (X) in
def tensorLeftAdj :
    tensorLeft X ⊣ TopCat.ihom X :=
  Adjunction.mkOfHomEquiv { homEquiv _ _ := ihomEquiv }

instance : Closed X where
  rightAdj := _
  adj := tensorLeftAdj X

instance : (tensorLeft X).IsLeftAdjoint := ⟨_, ⟨tensorLeftAdj X⟩⟩

instance : (tensorRight X).IsLeftAdjoint :=
  ⟨_, ⟨(tensorLeftAdj X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X)⟩⟩

end TopCat
