import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.SSet.Deformation

universe u

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  MonoidalCategory Simplicial ChosenFiniteProducts

namespace SSet

namespace MinimalFibration

lemma acyclic_fibration_retraction {E' E B : SSet.{u}} {p' : E' ⟶ B} {p : E ⟶ B}
    (h : FiberwiseDeformationRetract p' p) [Fibration p] [MinimalFibration p'] :
  I.rlp h.r := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro u v sq
  obtain ⟨l, hl₁, hl₂, hl₃⟩ :=
    homotopy_extension_property₀.{u} (i := ∂Δ[n].ι) (p := p)
      (hE := u ▷ _ ≫ h.h) (v ≫ h.i) (by simp [← sq.w_assoc]) (fst _ _ ≫ v ≫ p')
      (by simp) (by simp [← sq.w_assoc])
  exact ⟨⟨{
    l := ι₁ ≫ l
    fac_left := by
      rw [← ι₁_comp_assoc, hl₂, ι₁_comp_assoc, h.h₁, Category.comp_id]
    fac_right := by
      -- it seems there is a gap in Quillen's proof
      -- it is fixed in the books by Hovey and Goerss-Jardine
      simpa [reassoc_of% hl₁] using
        congr_ι₀_comp (p := p') (n := n) (h₁ := (ι₁ ≫ l) ▷ Δ[1] ≫ h.h ≫ h.r)
          (h₂ := l ≫ h.r) (yonedaEquiv (v ≫ p'))
          (by simp [← ι₁_comp_assoc, hl₃]) (by simpa)
          (by
            have : ∂Δ[n].ι ≫ ι₁ ≫ l = u := by
              rw [← ι₁_comp_assoc, hl₂, ι₁_comp_assoc, h.h₁, Category.comp_id]
            rw [← comp_whiskerRight_assoc, this, reassoc_of% hl₂]) (by simp)
  }⟩⟩

lemma factorization {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    ∃ (E' : SSet.{u}) (r : E ⟶ E') (p' : E' ⟶ B),
      r ≫ p' = p ∧ MinimalFibration p' ∧ I.rlp r := by
  obtain ⟨A, h, _⟩ := existence p
  exact ⟨A, h.r, h.i ≫ p, by simp, by simpa,
    acyclic_fibration_retraction h.toFiberwiseDeformationRetract⟩

end MinimalFibration

end SSet
