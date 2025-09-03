import TopCatModelCategory.Convenient.Category
import TopCatModelCategory.ObjectPropertyLimits
import TopCatModelCategory.TopCat.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

universe v t u

open CategoryTheory Topology Limits MonoidalCategory CartesianMonoidalCategory

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

variable {J : Type*} [Category J]

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

end GeneratedByTopCat
