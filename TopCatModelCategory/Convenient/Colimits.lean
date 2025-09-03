import TopCatModelCategory.Convenient.Category
import TopCatModelCategory.TopCat.Colimits
import TopCatModelCategory.ObjectPropertyLimits

universe v t u

open CategoryTheory Topology Limits

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

variable {J : Type*} [Category J]

lemma Topology.isGeneratedBy.of_isColimit {F : J ⥤ TopCat.{v}}
    {c : Cocone F} (hc : IsColimit c) (h : ∀ j, IsGeneratedBy X (F.obj j)) :
    IsGeneratedBy X c.pt where
  continuous_equiv_symm := by
    rw [continuous_def]
    intro U hU
    rw [((TopCat.nonempty_isColimit_iff _).1 ⟨hc⟩).2]
    simp only [Functor.const_obj_obj, isOpen_iSup_iff, isOpen_coinduced, Set.preimage_id']
    rw [WithGeneratedByTopology.isOpen_iff] at hU
    intro j
    rw [IsGeneratedBy.isOpen_iff (X := X)]
    intro i f
    exact hU ⟨c.ι.app j ∘ f, by continuity⟩

namespace GeneratedByTopCat

variable {F : J ⥤ GeneratedByTopCat.{v} X}

def toTopCatReflectsIsColimit {c : Cocone F} (hc : IsColimit (toTopCat.mapCocone c)) :
    IsColimit c :=
  ObjectProperty.ιReflectsIsColimit _ hc

@[simps]
def coconeOfTopCat (c : Cocone (F ⋙ toTopCat)) : Cocone F where
  pt := TopCat.toGeneratedByTopCat.obj c.pt
  ι :=
    { app j := adj.homEquiv _ _ (c.ι.app j)
      naturality j₁ j₂ f := by
        have := adj.homEquiv_naturality_left (F.map f) (c.ι.app j₂)
        dsimp at this ⊢
        rw [Category.comp_id, ← c.w f, ← this]
        dsimp }

def isColimitCoconeOfTopCat (c : Cocone (F ⋙ toTopCat)) (hc : IsColimit c) :
    IsColimit (coconeOfTopCat c) :=
  have : IsGeneratedBy X c.pt :=
    Topology.isGeneratedBy.of_isColimit hc (fun j ↦ (F.obj j).property)
  toTopCatReflectsIsColimit (IsColimit.ofIsoColimit hc
    (Cocones.ext (toTopCat.mapIso (adjUnitIso.app (of c.pt)))))

def toTopCatPreservesIsColimit {c : Cocone F} (hc : IsColimit c) :
    IsColimit (toTopCat.mapCocone c) where
  desc s := (adj.homEquiv _ _).symm (hc.desc (coconeOfTopCat s))
  fac s j := by
    have := adj.homEquiv_naturality_left_symm (c.ι.app j) (hc.desc (coconeOfTopCat s))
    dsimp at this ⊢
    rw [← this, hc.fac]
    rfl
  uniq s m hm := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    refine hc.hom_ext (fun j ↦ ?_)
    rw [hc.fac]
    ext x
    exact ConcreteCategory.congr_hom (hm j) x

instance [HasColimitsOfShape J TopCat.{v}] :
    HasColimitsOfShape J (GeneratedByTopCat.{v} X) where
  has_colimit _ := ⟨_, isColimitCoconeOfTopCat _ (colimit.isColimit _)⟩

end GeneratedByTopCat
