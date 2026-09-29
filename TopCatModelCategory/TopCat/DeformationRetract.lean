module

public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.UnitInterval
public import TopCatModelCategory.TopCat.Monoidal
public import TopCatModelCategory.TopCat.CompactOpen
public import TopCatModelCategory.CommSq

@[expose] public section

universe w u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

namespace TopCat

variable (X Y : TopCat.{u})

structure DeformationRetract extends Retract X Y where
  h : Y ⊗ I ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i := by aesop_cat
  h₀ : ι₀ ≫ h = r ≫ i := by aesop_cat
  h₁ : ι₁ ≫ h = 𝟙 Y := by aesop_cat

open DeformationRetract in
attribute [reassoc] hi h₀ h₁

def deformationRetracts : MorphismProperty TopCat.{u} := fun _ _ f ↦
  ∃ (h : DeformationRetract _ _), h.i = f

instance : deformationRetracts.{u}.IsStableUnderCobaseChange where
  of_isPushout := by
    rintro X₁ X₂ X₁' X₂' _ p₁ i' p₂ sq ⟨h, rfl⟩
    obtain ⟨r', i'_r', p₂_r'⟩ := sq.exists_desc (𝟙 _) (h.r ≫ p₁) (by simp)
    obtain ⟨h', h'₁, h'₂⟩ :=
      (sq.map (tensorRight I)).exists_desc (fst _ _ ≫ i') (h.h ≫ p₂) (by
        dsimp
        rw [whiskerRight_fst_assoc, h.hi_assoc, sq.w])
    dsimp at h'₁ h'₂
    exact ⟨{
      i := i'
      r := r'
      retract := i'_r'
      h := h'
      hi := h'₁
      h₀ := by
        apply sq.hom_ext
        · rw [← ι₀_comp_assoc, h'₁, ι₀_fst_assoc, reassoc_of% i'_r']
        · rw [← ι₀_comp_assoc, h'₂, reassoc_of% h.h₀,
            reassoc_of% p₂_r', sq.w]
      h₁ := by
        apply sq.hom_ext
        · rw [← ι₁_comp_assoc, h'₁, ι₁_fst_assoc, Category.comp_id]
        · dsimp
          rw [← ι₁_comp_assoc, h'₂, reassoc_of% h.h₁, Category.comp_id]
    }, rfl⟩

instance {J : Type w} (Y : J → TopCat.{u}) [HasCoproduct Y] [(tensorRight X).IsLeftAdjoint] :
    HasCoproduct (fun j ↦ (tensorRight X).obj (Y j)) :=
  ⟨⟨⟨_, isColimitOfHasCoproductOfPreservesColimit _ _⟩⟩⟩

instance {J : Type w} (Y : J → TopCat.{u}) [HasCoproduct Y] [(tensorRight X).IsLeftAdjoint] :
    HasCoproduct (fun j ↦ Y j ⊗ X) :=
  ⟨⟨⟨_, isColimitOfHasCoproductOfPreservesColimit (tensorRight X) _⟩⟩⟩

@[reassoc (attr := simp)]
lemma ι₀_preservesCoproduct_iso_hom {J : Type w} (Y : J → TopCat.{u}) [HasCoproduct Y] :
    ι₀ ≫ (PreservesCoproduct.iso (tensorRight I) Y).hom =
      Limits.Sigma.map (fun _ ↦ ι₀) := by
  rw [← cancel_mono (PreservesCoproduct.iso (tensorRight I) Y).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  ext j : 1
  have := ι_comp_sigmaComparison (tensorRight I) Y
  dsimp at this
  rw [ι_colimMap_assoc, PreservesCoproduct.inv_hom, this]
  dsimp

@[reassoc (attr := simp)]
lemma ι₁_preservesCoproduct_iso_hom {J : Type w} (Y : J → TopCat.{u}) [HasCoproduct Y] :
    ι₁ ≫ (PreservesCoproduct.iso (tensorRight I) Y).hom =
      Limits.Sigma.map (fun _ ↦ ι₁) := by
  rw [← cancel_mono (PreservesCoproduct.iso (tensorRight I) Y).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  ext j : 1
  have := ι_comp_sigmaComparison (tensorRight I) Y
  dsimp at this
  rw [ι_colimMap_assoc, PreservesCoproduct.inv_hom, this]
  dsimp

@[reassoc (attr := simp)]
lemma colimitι_whiskerRight_comp_preservesCoproduct_iso_hom
    {J : Type w} (Y : J → TopCat.{u}) [HasCoproduct Y]
    (X : TopCat.{u})
    [(tensorRight X).IsLeftAdjoint] (j : J) :
    Sigma.ι Y j ▷ X ≫ (PreservesCoproduct.iso (tensorRight X) Y).hom =
      Sigma.ι (fun j ↦ Y j ⊗ X) j := by
  rw [← cancel_mono (PreservesCoproduct.iso (tensorRight X) Y).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom]
  exact (ι_comp_sigmaComparison (tensorRight X) Y j).symm

instance : MorphismProperty.IsStableUnderCoproducts.{w} deformationRetracts.{u} where
  isStableUnderCoproductsOfShape J := by
    apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
    intro X Y _ _ f hf
    let R (j : J) : DeformationRetract (X j) (Y j) := (hf j).choose
    have hR (j : J) : (R j).i = f j := (hf j).choose_spec
    exact ⟨
      { i := Limits.Sigma.map f
        r := Limits.Sigma.map (fun j ↦ (R j).r)
        retract := by simp only [Sigma.map_comp_map, ← hR, Retract.retract, Sigma.map_id]
        h := (PreservesCoproduct.iso (tensorRight I) Y).hom ≫
          Limits.Sigma.map (fun j ↦ (R j).h)
        hi := by
          dsimp
          rw [← cancel_epi (PreservesCoproduct.iso (tensorRight I) X).inv]
          ext j : 1
          rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
            ι_comp_sigmaComparison_assoc]
          dsimp
          rw [← comp_whiskerRight_assoc, ι_colimMap,
            whiskerRight_fst_assoc, ι_colimMap]
          dsimp
          rw [comp_whiskerRight_assoc,
            colimitι_whiskerRight_comp_preservesCoproduct_iso_hom_assoc,
            ι_colimMap]
          dsimp
          rw [← hR, (R j).hi_assoc]
        h₀ := by
          ext j : 1
          simp [(R j).h₀_assoc, hR]
        h₁ := by
          ext j : 1
          simp [(R j).h₁_assoc] }, rfl⟩

end TopCat
