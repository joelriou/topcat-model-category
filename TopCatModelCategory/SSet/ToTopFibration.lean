import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.SSet.MinimalFibrationsFactorization
import TopCatModelCategory.TopCat.ToTopExact

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  TopCat.modelCategory Simplicial MonoidalCategory ChosenFiniteProducts Limits

namespace SSet

open MorphismProperty

lemma trivialBundles_fst (X₁ X₂ : SSet.{u}) :
    trivialBundles (fst X₁ X₂) := by
  simp only [trivialBundles, iSup_iff]
  exact ⟨X₂, ⟨{
    r := snd _ _
    isLimit := (ChosenFiniteProducts.product X₁ X₂).isLimit
  }⟩⟩

lemma trivialBundles_snd (X₁ X₂ : SSet.{u}) :
    trivialBundles (snd X₁ X₂) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1 (trivialBundles_fst X₂ X₁)
  exact Arrow.isoMk (β_ _ _) (Iso.refl _)

-- Gabriel-Zisman
instance {E B : SSet} (p : E ⟶ B) [MinimalFibration p] :
    Fibration (toTop.map p) := sorry

lemma fibration_toTop_map_of_trivialBundles {E B : SSet} (p : E ⟶ B)
    (hp : trivialBundles p) :
    Fibration (toTop.map p) := by
  simp only [trivialBundles, iSup_iff] at hp
  obtain ⟨F, ⟨h⟩⟩ := hp
  have hF : Fibration (toTop.map (stdSimplex.isTerminalObj₀.from F)) := by
    rw [← isFibrant_iff_of_isTerminal _
      (IsTerminal.isTerminalObj _ _ stdSimplex.isTerminalObj₀)]
    infer_instance
  have sq := (h.isPullback_of_isTerminal stdSimplex.isTerminalObj₀).map toTop
  rw [HomotopicalAlgebra.fibration_iff] at hF ⊢
  exact MorphismProperty.of_isPullback sq hF

lemma fibration_toTop_map_of_rlp_I {E B : SSet} {p : E ⟶ B} (hp : I.rlp p) :
    Fibration (toTop.map p) := by
  obtain ⟨W, k, hk, a, ha⟩ : ∃ (W : SSet) (k : E ⟶ W) (hk : Mono k) (a : W ⟶ Δ[0]), I.rlp a := by
    have h := MorphismProperty.factorizationData (monomorphisms SSet.{0})
      I.rlp (stdSimplex.isTerminalObj₀.from E)
    exact ⟨h.Z, h.i, h.hi, h.p, h.hp⟩
  have : HasLiftingProperty (lift k p) p := by
    rw [I_rlp_eq_monomorphisms_rlp] at hp
    exact hp _ (mono_of_mono_fac (lift_fst k p))
  have h : Fibration (toTop.map (snd W B)) :=
    fibration_toTop_map_of_trivialBundles _ (trivialBundles_snd W B)
  rw [HomotopicalAlgebra.fibration_iff] at h ⊢
  apply MorphismProperty.of_retract
    ((RetractArrow.ofRightLiftingProperty (lift_snd k p)).map toTop.mapArrow) h

-- Quillen
instance {E B : SSet} (p : E ⟶ B) [Fibration p] :
    Fibration (toTop.map p) := by
  obtain ⟨E', r, p', rfl, _, hr⟩ := MinimalFibration.factorization p
  simp only [Functor.map_comp]
  have := fibration_toTop_map_of_rlp_I hr
  infer_instance

end SSet
