import TopCatModelCategory.Convenient.GeneratedBy
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.Category.TopCat.Basic

universe t u

open CategoryTheory Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

structure ContinuousGeneratedByCat
    (X : ι → Type u) [∀ i, TopologicalSpace (X i)] where private mk ::
    carrier : Type u
    [str : TopologicalSpace carrier]

namespace ContinuousGeneratedByCat

variable {X}

instance : CoeSort (ContinuousGeneratedByCat X) (Type u) :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] str

abbrev of (Y : Type u) [TopologicalSpace Y] : ContinuousGeneratedByCat X :=
  ⟨Y⟩

lemma coe_of (Y : Type u) [TopologicalSpace Y] : (of (X := X) Y : Type u) = Y :=
  rfl

lemma of_carrier (Y : ContinuousGeneratedByCat X) : of (X := X) Y = Y := rfl

instance : Category (ContinuousGeneratedByCat X) where
  Hom Y Z := ContinuousMapGeneratedBy X Y Z
  id X := .id
  comp f g := g.comp f

instance : ConcreteCategory.{u} (ContinuousGeneratedByCat X)
    (fun Y Z => ContinuousMapGeneratedBy X Y Z) where
  hom := id
  ofHom := id

end ContinuousGeneratedByCat

@[simps obj]
def TopCat.toContinuousGeneratedByCat :
    TopCat.{u} ⥤ ContinuousGeneratedByCat X where
  obj Y := .of Y
  map f :=
    { toFun := f
      prop := f.hom.continuous.continuousGeneratedBy }

namespace ContinuousGeneratedByCat

@[simps obj]
def toTopCat : ContinuousGeneratedByCat X ⥤ TopCat.{u} where
  obj Y := TopCat.of (WithGeneratedByTopology X Y)
  map {Y₁ Y₂} f := TopCat.ofHom ⟨f, by
    have := (continuousGeneratedBy_iff _ _).1 f.prop
    exact this⟩

end ContinuousGeneratedByCat

namespace ContinuousGeneratedByCat

variable {X}

def adjUnitIso :
    𝟭 (ContinuousGeneratedByCat X) ≅ toTopCat X ⋙ TopCat.toContinuousGeneratedByCat X :=
  NatIso.ofComponents (fun Y ↦
    { hom := WithGeneratedByTopology.continuousMapGeneratedByTo X Y
      inv := WithGeneratedByTopology.continuousMapGeneratedByFrom X Y })

def adjCounit : TopCat.toContinuousGeneratedByCat X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  app Z := TopCat.ofHom (WithGeneratedByTopology.continuousMapFrom X Z)

def adj : toTopCat X ⊣ TopCat.toContinuousGeneratedByCat X where
  unit := adjUnitIso.hom
  counit := adjCounit

end ContinuousGeneratedByCat
