module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

universe v u w

open CategoryTheory Limits Topology

/-namespace TopCat

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

section

variable (c : Cocone (F ⋙ forget _))

@[simps]
def coconeOfCocone : Cocone F where
  pt := ⟨c.pt, ⨆ j, (F.obj j).str.coinduced (c.ι.app j)⟩
  ι :=
    { app j := ⟨c.ι.app j, by
        rw [continuous_iff_coinduced_le]
        exact le_iSup (fun j ↦ (F.obj j).str.coinduced (c.ι.app j)) j ⟩
      naturality j j' φ := by
        ext
        apply congr_fun (c.ι.naturality φ) }

def isColimitCoconeOfCocone (hc : IsColimit c) :
    IsColimit (coconeOfCocone c) := by
  refine IsColimit.ofFaithful (forget _) (ht := by exact hc)
    (fun s ↦ ⟨hc.desc ((forget _).mapCocone s), ?_⟩) (fun s ↦ rfl)
  rw [continuous_iff_le_induced]
  dsimp
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced, induced_compose]
  convert continuous_iff_le_induced.1 (s.ι.app j).continuous
  exact hc.fac ((forget _).mapCocone s) j

end

section

variable (c : Cocone F) (hc : IsColimit c)

include hc

lemma isOpen_iff_of_isColimit_aux :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let c' := coconeOfCocone ((forget TopCat).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfCocone _ (isColimitOfPreserves (forget _) hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc j
  apply (homeoOfIso e).coinduced_eq.symm.trans
  simp only [coconeOfCocone, c', topologicalSpace_coe, coinduced_iSup]
  conv_rhs => simp only [← he]
  rfl

lemma isOpen_iff_of_isColimit (X : Set c.pt) :
    IsOpen X ↔ ∀ (j : J), IsOpen (c.ι.app j ⁻¹' X) := by
  trans (show TopologicalSpace c.pt from
      ⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← isOpen_iff_of_isColimit_aux c hc]
    rfl
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

lemma isClosed_iff_of_isColimit (X : Set c.pt) :
    IsClosed X ↔ ∀ (j : J), IsClosed (c.ι.app j ⁻¹' X) := by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]

end

end TopCat-/
