import TopCatModelCategory.Convenient.Category
import TopCatModelCategory.ObjectPropertyLimits
import TopCatModelCategory.TopCat.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

universe v t u

open CategoryTheory Topology Limits MonoidalCategory CartesianMonoidalCategory

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

variable {J : Type*} [Category J]

namespace TopCat

variable {F : J ⥤ TopCat.{v}}

open ContinuousGeneratedByCat

def coneOfToContinuousGeneratedByCat (s : Cone (F ⋙ toContinuousGeneratedByCat X)) :
    Cone F where
  pt := (ContinuousGeneratedByCat.toTopCat X).obj s.pt
  π :=
    { app j := (adj.homEquiv _ _).symm (s.π.app j)
      naturality j₁ j₂ f := by
        have := adj.homEquiv_naturality_right_symm (s.π.app j₁) (F.map f)
        dsimp at this ⊢
        rw [Category.id_comp, ← this, ← s.w f]
        dsimp }

variable (X) in
-- do we have this for general adjunctions already?
def toContinuousGeneratedByCatPreservesIsLimit
    {c : Cone F} (hc : IsLimit c) :
    IsLimit ((toContinuousGeneratedByCat X).mapCone c) where
  lift s := adj.homEquiv _ _ (hc.lift (coneOfToContinuousGeneratedByCat s))
  fac s j := by
    have h₁ := (adj (X := X)).homEquiv_naturality_right
      (hc.lift (coneOfToContinuousGeneratedByCat s)) (c.π.app j)
    dsimp at h₁ ⊢
    rw [← h₁, hc.fac]
    rfl
  uniq s m hm := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [Equiv.symm_apply_apply]
    refine hc.hom_ext (fun j ↦ ?_)
    rw [hc.fac]
    ext x
    exact ConcreteCategory.congr_hom (hm j) x

end TopCat

namespace ContinuousGeneratedByCat

instance (Y : ContinuousGeneratedByCat.{v} X) : Unique (Y ⟶ of PUnit) where
  default :=
    { toFun _ := .unit
      prop := continuous_const.continuousGeneratedBy }
  uniq _ := by ext

def isTerminal : IsTerminal (of.{v} (X := X) PUnit) :=
  IsTerminal.ofUnique _

def binaryFan (Y Z : ContinuousGeneratedByCat.{v} X) : BinaryFan Y Z :=
  (Cones.postcompose (pairComp  _ _ _).hom).obj
    ((TopCat.toContinuousGeneratedByCat X).mapCone
    (TopCat.prodBinaryFan (TopCat.of Y.carrier) (TopCat.of Z.carrier)))

def isLimitBinaryFan (Y Z : ContinuousGeneratedByCat.{v} X) :
    IsLimit (binaryFan Y Z) := by
  refine (IsLimit.equivOfNatIsoOfIso (pairComp _ _ _) _ _ ?_).1
    (TopCat.toContinuousGeneratedByCatPreservesIsLimit X
    ((TopCat.prodBinaryFanIsLimit (TopCat.of Y.carrier) (TopCat.of Z.carrier))))
  exact BinaryFan.ext (Iso.refl _) rfl rfl

instance : CartesianMonoidalCategory (ContinuousGeneratedByCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminal⟩ (fun _ _ ↦ ⟨_, isLimitBinaryFan _ _⟩)

instance : BraidedCategory (ContinuousGeneratedByCat.{v} X) :=
  CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

section

variable {F : J ⥤ GeneratedByTopCat.{v} X}

def toTopCatReflectsIsLimit {c : Cone F} (hc : IsLimit (toTopCat.mapCone c)) : IsLimit c :=
  ObjectProperty.ιReflectsIsLimit _ hc

@[simps]
def coneOfConeTopCat (c : Cone (F ⋙ toTopCat)) : Cone F where
  pt := TopCat.toGeneratedByTopCat.obj c.pt
  π :=
    { app j := TopCat.toGeneratedByTopCat.map (c.π.app j) ≫ adjUnitIso.inv.app _
      naturality j k g := by
        have := c.w g
        dsimp at this ⊢
        simp only [Category.id_comp, Category.assoc, ← adjUnitIso_inv_naturality,
          ← Functor.map_comp_assoc, this] }

def isLimitConeOfConeTopCat (c : Cone (F ⋙ toTopCat)) (hc : IsLimit c) :
    IsLimit (coneOfConeTopCat c) where
  lift s := adj.homEquiv _ _ (hc.lift (toTopCat.mapCone s))
  fac s j := by
    have h₁ := adj_homEquiv_naturality (hc.lift (toTopCat.mapCone s)) (c.π.app j)
    dsimp at h₁ ⊢
    rw [← reassoc_of% h₁, hc.fac]
    rfl
  uniq s m hm := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [ObjectProperty.ι_obj, Equiv.symm_apply_apply]
    refine hc.hom_ext (fun j ↦ ?_)
    rw [hc.fac]
    ext x
    exact congr_fun (((toTopCat ⋙ forget _).congr_map) (hm j)) x

end

instance [HasLimitsOfShape J TopCat.{v}] :
    HasLimitsOfShape J (GeneratedByTopCat.{v} X) where
  has_limit _ := ⟨_, isLimitConeOfConeTopCat _ (limit.isLimit _)⟩

instance (Y : GeneratedByTopCat.{v} X) : Unique (Y ⟶ of PUnit) where
  default := TopCat.ofHom ⟨fun _ ↦ .unit, continuous_const⟩
  uniq _ := by ext

def isTerminal : IsTerminal (of.{v} (X := X) PUnit) :=
  IsTerminal.ofUnique _

def binaryFan (Y Z : GeneratedByTopCat.{v} X) : BinaryFan Y Z :=
  coneOfConeTopCat ((Cones.postcompose
    (pairComp Y Z toTopCat).inv).obj (TopCat.prodBinaryFan Y.obj Z.obj))

def isLimitBinaryFan (Y Z : GeneratedByTopCat.{v} X) : IsLimit (binaryFan Y Z) := by
  refine isLimitConeOfConeTopCat _
    ((IsLimit.equivOfNatIsoOfIso (pairComp _ _ _) _ _ ?_).2
    (TopCat.prodBinaryFanIsLimit Y.obj Z.obj))
  exact BinaryFan.ext (Iso.refl _) rfl rfl

instance : CartesianMonoidalCategory (GeneratedByTopCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminal⟩ (fun _ _ ↦ ⟨_, isLimitBinaryFan _ _⟩)

instance : BraidedCategory (GeneratedByTopCat.{v} X) :=
  CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

end GeneratedByTopCat
