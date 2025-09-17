import TopCatModelCategory.Convenient.Fibrations
import TopCatModelCategory.SSet.MinimalFibrationsFactorization
import TopCatModelCategory.TopCat.ToTopExact
import TopCatModelCategory.TopCat.ToTopLocTrivial
import TopCatModelCategory.SSet.FactorThruFinite
import TopCatModelCategory.SSet.SingularConnected

universe u
open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  TopCat.modelCategory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

namespace SSet

open MorphismProperty

lemma trivialBundles_fst (X₁ X₂ : SSet.{u}) :
    trivialBundles (fst X₁ X₂) := by
  simp only [trivialBundles, iSup_iff]
  exact ⟨X₂, ⟨{
    r := snd _ _
    isLimit := tensorProductIsBinaryProduct _ _
  }⟩⟩

lemma trivialBundles_snd (X₁ X₂ : SSet.{u}) :
    trivialBundles (snd X₁ X₂) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1 (trivialBundles_fst X₂ X₁)
  exact Arrow.isoMk (β_ _ _) (Iso.refl _)

lemma fibration_toTop_map_of_trivialBundles {E B : SSet.{u}} (p : E ⟶ B)
    (hp : trivialBundles p) :
    Fibration (toTop.map p) := by
  simp only [trivialBundles, iSup_iff] at hp
  obtain ⟨F, ⟨h⟩⟩ := hp
  have hF : Fibration (toTop.map (stdSimplex.isTerminalObj₀.from F)) := by
    rw [← isFibrant_iff_of_isTerminal _
      (IsTerminal.isTerminalObj _ _ stdSimplex.isTerminalObj₀)]
    infer_instance
  rw [HomotopicalAlgebra.fibration_iff] at hF ⊢
  apply MorphismProperty.of_isPullback
    (P := ((fibrations _).inverseImage DeltaGenerated'.toTopCat))
    ((h.isPullback_of_isTerminal stdSimplex.isTerminalObj₀).map SSet.toDeltaGenerated) hF

-- Gabriel-Zisman
instance {E B : SSet.{u}} (p : E ⟶ B) [MinimalFibration p] :
    Fibration (toTop.map p) := by
  wlog hB : IsFinite B ∧ IsConnected B
  · rw [TopCat.modelCategory.fibration_iff_rlp]
    intro n i
    constructor
    intro t b sq
    obtain ⟨B', _, _, s, _, j, rfl⟩ := exists_factor_thru_finite_connected_of_topCatHom b
    have := this (pullback.fst s p) ⟨inferInstance, inferInstance⟩
    obtain ⟨t', h₁ , h₂⟩ := ((IsPullback.of_hasPullback s p).map toTop).exists_lift
      (toTop.map Λ[n + 1, i].ι ≫ j) t (by simp [sq.w])
    have sq' : CommSq t' (toTop.map Λ[n + 1, i].ι) (toTop.map (pullback.fst s p)) j := ⟨h₁⟩
    exact ⟨⟨{
      l := sq'.lift ≫ toTop.map (pullback.snd _ _)
      fac_left := by rw [sq'.fac_left_assoc, h₂]
      fac_right := by
        rw [Category.assoc, ← Functor.map_comp, ← pullback.condition,
          Functor.map_comp, sq'.fac_right_assoc]
    }⟩⟩
  obtain ⟨_, _⟩ := hB
  let b₀ : B _⦋0⦌ := Classical.arbitrary _
  refine fibration_toTop_map_of_trivialBundle_over_simplices
    (F := Subcomplex.fiber p b₀) _ (fun n σ ↦ Nonempty.some ?_)
  have := MinimalFibration.isTrivialBundle_of_stdSimplex (pullback.snd p σ)
  rw [mem_trivialBundles_iff] at this
  obtain ⟨F', ⟨hσ⟩⟩ := this
  let b₁ : B _⦋0⦌ :=
    yonedaEquiv (stdSimplex.map (SimplexCategory.const _ _ 0) ≫ σ)
  obtain ⟨e⟩ := MinimalFibration.nonempty_iso_fiber p
    (Subsingleton.elim (π₀.mk b₀) (π₀.mk b₁))
  let t : (Subcomplex.fiber p b₁ : SSet) ⟶ pullback p σ :=
    pullback.lift (Subcomplex.fiber p b₁).ι
      (SSet.const (stdSimplex.obj₀Equiv.symm 0))
  have sqt : IsPullback t (stdSimplex.objZeroIsTerminal.from _) (pullback.snd _ _)
      (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback p σ)
    · convert Subcomplex.fiber_isPullback p b₁ using 1
      · simp [t]
      · exact yonedaEquiv.injective (by aesop)
    · simp [t]
      rfl
  exact ⟨{
    sq := IsPullback.of_hasPullback p σ
    h := hσ.chg (e ≪≫ (hσ.pullback sqt).isoOfIsTerminal stdSimplex.isTerminalObj₀)
  }⟩

lemma fibration_toTop_map_of_rlp_I {E B : SSet.{u}} {p : E ⟶ B} (hp : I.rlp p) :
    Fibration (toTop.map p) := by
  obtain ⟨W, k, hk, a, ha⟩ : ∃ (W : SSet) (k : E ⟶ W) (hk : Mono k) (a : W ⟶ Δ[0]), I.rlp a := by
    have h := MorphismProperty.factorizationData (monomorphisms SSet.{u})
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
