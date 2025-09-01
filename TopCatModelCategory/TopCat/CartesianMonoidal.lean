import TopCatModelCategory.DeltaGeneratedSpace
import TopCatModelCategory.TopCat.DeltaGenerated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TopCat

def binaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk (P := .of (X × Y))
    (TopCat.ofHom ⟨Prod.fst, by continuity⟩)
    (TopCat.ofHom ⟨Prod.snd, by continuity⟩)

def isLimitBinaryFan (X Y : TopCat.{u}) : IsLimit (binaryFan X Y) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ TopCat.ofHom ⟨fun t ↦ ⟨f t, g t⟩, by continuity⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by aesop)

instance : CartesianMonoidalCategory TopCat.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨_, isLimitBinaryFan X Y⟩)

end TopCat

namespace DeltaGenerated

instance (X : DeltaGenerated.{u}): Unique (X ⟶ of PUnit) where
  default := TopCat.ofHom ⟨fun _ ↦ .unit, continuous_const⟩
  uniq a := by ext

def isTerminalPUnit : IsTerminal (of.{u} PUnit) := IsTerminal.ofUnique _

def binaryFan (X Y : DeltaGenerated.{u}) : BinaryFan X Y :=
  BinaryFan.mk (P := topToDeltaGenerated.obj (X.toTop ⊗ Y.toTop))
    (fullyFaithfulDeltaGeneratedToTop.preimage
        ((coreflectorAdjunction.homEquiv _ _).symm
        (topToDeltaGenerated.map (fst _ _))))
    (fullyFaithfulDeltaGeneratedToTop.preimage
        ((coreflectorAdjunction.homEquiv _ _).symm
        (topToDeltaGenerated.map (snd _ _))))

def isLimitBinaryFan (X Y : DeltaGenerated.{u}) :
    IsLimit (binaryFan X Y) := by
  let e : pair X Y ⋙ deltaGeneratedToTop ≅ pair X.toTop Y.toTop :=
    mapPairIso (Iso.refl _) (Iso.refl _)
  exact IsLimit.ofIsoLimit
      (isLimitOfTopCat ((IsLimit.postcomposeInvEquiv e _).2
        (TopCat.isLimitBinaryFan X.toTop Y.toTop)))
        (BinaryFan.ext (Iso.refl _) rfl rfl)

instance : CartesianMonoidalCategory DeltaGenerated.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨_, isLimitBinaryFan X Y⟩)

example {T X Y : DeltaGenerated.{u}} (f : T ⟶ X) (g : T ⟶ Y) (t : T):
    lift f g t = ⟨f t, g t⟩ := rfl

end DeltaGenerated
