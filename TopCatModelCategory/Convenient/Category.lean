module

public import TopCatModelCategory.Convenient.ContinuousMapGeneratedBy
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

universe v t u

open CategoryTheory Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

def TopCat.generatedBy : ObjectProperty TopCat.{v} :=
  fun Y ↦ IsGeneratedBy X Y

lemma TopCat.generatedBy_def (Y : TopCat.{v}) :
    generatedBy X Y ↔ IsGeneratedBy X Y := Iff.rfl

abbrev GeneratedByTopCat := (TopCat.generatedBy.{v} X).FullSubcategory

namespace GeneratedByTopCat

variable {X} in
abbrev toTopCat : GeneratedByTopCat.{v} X ⥤ TopCat.{v} := ObjectProperty.ι _

instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X (toTopCat.obj Y) := Y.2

def fullyFaithfulToTopCat : (toTopCat.{v} (X := X)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {X} in
abbrev of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    GeneratedByTopCat.{v} X where
  obj := TopCat.of Y
  property := by assumption

instance : CoeSort (GeneratedByTopCat.{v} X) (Type v) where
  coe Y := (Y.obj : Type v)

instance (Y : GeneratedByTopCat.{v} X) :
    IsGeneratedBy X Y := Y.2

end GeneratedByTopCat

structure ContinuousGeneratedByCat
    (X : ι → Type u) [∀ i, TopologicalSpace (X i)] where private mk ::
    carrier : Type v
    [str : TopologicalSpace carrier]

namespace ContinuousGeneratedByCat

variable {X}

instance : CoeSort (ContinuousGeneratedByCat.{v} X) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] str

abbrev of (Y : Type v) [TopologicalSpace Y] : ContinuousGeneratedByCat.{v} X :=
  ⟨Y⟩

lemma coe_of (Y : Type v) [TopologicalSpace Y] : (of (X := X) Y : Type v) = Y :=
  rfl

lemma of_carrier (Y : ContinuousGeneratedByCat.{v} X) : of (X := X) Y = Y := rfl

instance : Category (ContinuousGeneratedByCat.{v} X) where
  Hom Y Z := ContinuousMapGeneratedBy X Y Z
  id X := .id
  comp f g := g.comp f

instance : ConcreteCategory.{v} (ContinuousGeneratedByCat.{v} X)
    (fun Y Z => ContinuousMapGeneratedBy X Y Z) where
  hom := id
  ofHom := id

end ContinuousGeneratedByCat

@[simps obj]
def TopCat.toContinuousGeneratedByCat :
    TopCat.{v} ⥤ ContinuousGeneratedByCat.{v} X where
  obj Y := .of Y
  map f :=
    { toFun := f
      prop := f.hom.continuous.continuousGeneratedBy }

namespace ContinuousGeneratedByCat

@[simps obj]
def toTopCat : ContinuousGeneratedByCat.{v} X ⥤ TopCat where
  obj Y := TopCat.of (WithGeneratedByTopology X Y)
  map {Y₁ Y₂} f := TopCat.ofHom (f.prop.continuousMap)

def fullyFaithfulToTopCat : (toTopCat.{v} X).FullyFaithful where
  preimage {Y Z} g :=
    { toFun := WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
          (WithGeneratedByTopology.equiv (X := X)).symm
      prop := by
        rw [continuousGeneratedBy_iff]
        exact g.hom.continuous }

variable {X}

def adjUnitIso :
    𝟭 (ContinuousGeneratedByCat.{v} X) ≅ toTopCat X ⋙ TopCat.toContinuousGeneratedByCat X :=
  NatIso.ofComponents (fun Y ↦
    { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y
      inv := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y })

def adjCounit : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  app Z := TopCat.ofHom (⟨_,  WithGeneratedByTopology.continuous_equiv⟩)

def adj : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where
  unit := adjUnitIso.hom
  counit := adjCounit

def fromGeneratedByTopCat : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Y := .of Y.1
  map {Y₁ Y₂} f := ⟨f, f.hom.continuous.continuousGeneratedBy⟩

def toGeneratedByTopCat : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{v} X :=
  ObjectProperty.lift _ (toTopCat X) (fun Y ↦ by
    rw [TopCat.generatedBy_def]
    dsimp
    infer_instance)

def equivalenceUnitIso :
    𝟭 (GeneratedByTopCat.{v} X) ≅ fromGeneratedByTopCat ⋙ toGeneratedByTopCat :=
  NatIso.ofComponents (fun Y ↦
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

abbrev equivalenceCounitIso :
    toGeneratedByTopCat ⋙ fromGeneratedByTopCat ≅ 𝟭 (ContinuousGeneratedByCat X) :=
  adjUnitIso.symm

def equivalence : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X where
  functor := fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso

def equivalenceFunctorIso :
    equivalence.functor ⋙ ContinuousGeneratedByCat.toTopCat X ≅ GeneratedByTopCat.toTopCat :=
  NatIso.ofComponents (fun Y ↦ TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

end ContinuousGeneratedByCat

variable {X}

def TopCat.toGeneratedByTopCat : TopCat.{v} ⥤ GeneratedByTopCat X :=
  TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

namespace GeneratedByTopCat

def adjUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedByTopCat :=
  ContinuousGeneratedByCat.equivalenceUnitIso

@[reassoc (attr := simp)]
lemma adjUnitIso_inv_naturality {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z) :
    TopCat.toGeneratedByTopCat.map f ≫ adjUnitIso.inv.app Z = adjUnitIso.inv.app Y ≫ f :=
  adjUnitIso.inv.naturality f

def adjCounit : TopCat.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 TopCat :=
  ContinuousGeneratedByCat.adjCounit

def adj : toTopCat.{v} (X := X) ⊣ TopCat.toGeneratedByTopCat where
  unit := adjUnitIso.hom
  counit := adjCounit

@[reassoc]
lemma adj_homEquiv_naturality {Y : GeneratedByTopCat.{v} X} {Z Z' : TopCat.{v}}
    (f : toTopCat.obj Y ⟶ Z) (g : Z ⟶ Z') :
    adj.homEquiv _ _ (f ≫ g) = adj.homEquiv _ _ f ≫ TopCat.toGeneratedByTopCat.map g :=
  Adjunction.homEquiv_naturality_right _ _ _

instance : (toTopCat.{v} (X := X)).IsLeftAdjoint := adj.isLeftAdjoint

instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).IsRightAdjoint := adj.isRightAdjoint

end GeneratedByTopCat
