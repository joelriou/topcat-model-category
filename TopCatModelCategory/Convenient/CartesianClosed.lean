import TopCatModelCategory.Convenient.HomSpace
import TopCatModelCategory.Convenient.Limits
import Mathlib.CategoryTheory.Closed.Cartesian

open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe v v' v'' t u

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

namespace ContinuousGeneratedByCat

namespace CartesianClosed

variable {X} (Y : ContinuousGeneratedByCat.{v} X)

def ihom : ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Z := of (ContinuousMapGeneratedBy X Y Z)
  map {Z₁ Z₂} p := ContinuousMapGeneratedBy.postcomp p

def ihomAdjunction : tensorLeft Y ⊣ ihom Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := ContinuousMapGeneratedBy.curryEquiv }

end CartesianClosed

instance (Y : ContinuousGeneratedByCat.{v} X) : Exponentiable Y where
  rightAdj := CartesianClosed.ihom Y
  adj := CartesianClosed.ihomAdjunction Y

instance : CartesianClosed (ContinuousGeneratedByCat.{v} X) where

end ContinuousGeneratedByCat
