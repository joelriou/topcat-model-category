import TopCatModelCategory.SSet.Deformation
import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.SmallObject

universe u

open HomotopicalAlgebra CategoryTheory Simplicial
  SSet.modelCategoryQuillen MonoidalCategory Limits

namespace SSet

namespace horn

@[simps]
def obj₀Mk {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2))
    (hj : ∃ (k : Fin (n + 2)), k ≠ i ∧ j ≠ k):
    (horn.{u} (n + 1) i : SSet) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm j, by
    obtain ⟨k, hi, hj⟩ := hj
    refine face_le_horn _ _ hi _ ?_
    simp only [stdSimplex.obj₀Equiv_symm_apply, stdSimplex.mem_face_iff,
      Finset.mem_compl, Finset.mem_singleton]
    intro l
    fin_cases l
    simpa [stdSimplex.const]⟩

lemma exists_contractible₀ (n : ℕ) :
    ∃ (h : (horn.{u} (n + 1) 0 : SSet) ⊗ Δ[1] ⟶ horn (n + 1) 0),
      ι₀ ≫ h = SSet.const (obj₀Mk 0 0 ⟨1, by simp, by simp⟩) ∧
      ι₁ ≫ h = 𝟙 _ := by
  let r := anodyneExtensions.retractArrowHornCastSuccι.r.{u} (0 : Fin (n + 1))
  have hr₀ : ι₀ ≫ r = SSet.const (stdSimplex.obj₀Equiv.symm 0) := by
    apply yonedaEquiv.injective
    ext i
    change min _ 0 = 0
    dsimp [yonedaEquiv, BinaryFan.fst, Cones.postcomposeEquivalence]
    simp
  have hr₁ : ι₁ ≫ r = 𝟙 _ := by simp [r]
  refine ⟨Subcomplex.lift (Subcomplex.ι _ ▷ _≫ r) ?_, ?_, ?_⟩
  · apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, Subcomplex.image_top]
    rintro ⟨d⟩ _ ⟨⟨⟨y₁, hy₁⟩, y₂⟩, rfl⟩
    induction' d using SimplexCategory.rec with d
    dsimp
    rw [horn, Set.mem_setOf_eq] at hy₁ ⊢
    intro h
    refine hy₁ (subset_antisymm (by simp) ?_)
    rw [← h]
    apply anodyneExtensions.retractArrowHornCastSuccι.range_union_singleton_le
  · rw [← cancel_mono (Subcomplex.ι _)]
    exact (horn (n + 1) 0).ι ≫= hr₀
  · rw [← cancel_mono (Subcomplex.ι _)]
    exact (horn (n + 1) 0).ι ≫= hr₁

end horn

namespace KanComplex

section

variable {F : SSet.{u}} {p : F ⟶ Δ[0]} (hp : I.rlp p)

include hp
lemma nonempty_of_rlp_I : Nonempty (F _⦋0⦌) := by
  have sq : CommSq (boundary.isInitial.to F) (boundary 0).ι p (𝟙 _) :=
    ⟨boundary.isInitial.hom_ext _ _⟩
  have := hp _ ⟨0⟩
  exact ⟨yonedaEquiv sq.lift⟩

lemma subsingleton_π₀_of_rlp_I : Subsingleton (π₀ F) where
  allEq x₀ x₁ := by
    obtain ⟨x₀, rfl⟩ := x₀.mk_surjective
    obtain ⟨x₁, rfl⟩ := x₁.mk_surjective
    have sq :
      CommSq (boundary₁.desc x₀ x₁) (boundary 1).ι p
        (stdSimplex.isTerminalObj₀.from _) :=
      ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have := hp _ ⟨1⟩
    apply π₀.sound (yonedaEquiv sq.lift)
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₀_desc x₀ x₁, ← boundary₁.ι₀ ≫= sq.fac_left,
        boundary₁.ι₀_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₁_desc x₀ x₁, ← boundary₁.ι₁ ≫= sq.fac_left,
        boundary₁.ι₁_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]

lemma subsingleton_π_of_rlp_I (n : ℕ) (x : F _⦋0⦌) :
    Subsingleton (π n F x) := by
  have : Fibration p := by
    rw [fibration_iff]
    exact rlp_I_le_rlp_J _ hp
  have : IsFibrant F := by
    rwa [isFibrant_iff_of_isTerminal p stdSimplex.isTerminalObj₀]
  obtain _ | n := n
  · rw [← (π₀EquivπZero x).subsingleton_congr]
    exact subsingleton_π₀_of_rlp_I hp
  suffices ∀ (s : π (n + 1) F x), s = 1 from ⟨by aesop⟩
  intro s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  change _ = π.mk _
  rw [π.mk_eq_mk_iff]
  obtain ⟨φ, hφ₀, hφ⟩ : ∃ (φ : (boundary (n + 2) : SSet) ⟶ F), boundary.ι 0 ≫ φ = s.map ∧
      ∀ (i : Fin (n + 3)) (hi : i ≠ 0), boundary.ι i ≫ φ = const x := by
    let α (i : Fin (n + 3)) : Δ[n + 1] ⟶ F := if i = 0 then s.map else const x
    obtain ⟨φ, hφ⟩ := boundary.exists_desc α (by aesop)
    refine ⟨φ, ?_, fun i hi ↦ ?_⟩
    · simp only [hφ, α, if_pos rfl]
    · simp only [hφ, α, if_neg hi]
  have sq : CommSq φ (boundary (n + 2)).ι p (stdSimplex.isTerminalObj₀.from _) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have := hp _ ⟨n + 2⟩
  have (i : Fin (n + 3)) : stdSimplex.δ i ≫ sq.lift = boundary.ι i ≫ φ := by
    rw [← boundary.ι_ι_assoc, sq.fac_left]
  exact ⟨{ map := sq.lift }⟩

end

section

variable {E B : SSet.{u}} {p : E ⟶ B} (hp : I.rlp p)

namespace W.of_rlp_I

include hp

lemma fiber_rlp_I (b : B _⦋0⦌) :
    I.rlp (stdSimplex.isTerminalObj₀.from (Subcomplex.fiber p b)) :=
  MorphismProperty.of_isPullback (Subcomplex.fiber_isPullback p b) hp

variable [IsFibrant E] [IsFibrant B]

omit [IsFibrant E] in
lemma bijective_mapπ₀ : Function.Bijective (mapπ₀ p) := by
  constructor
  · intro e₀ e₁ h
    obtain ⟨e₀, rfl⟩ := e₀.mk_surjective
    obtain ⟨e₁, rfl⟩ := e₁.mk_surjective
    simp only [mapπ₀_mk, π₀_mk_eq_π₀_mk_iff] at h
    obtain ⟨edge⟩ := h
    have sq : CommSq (boundary₁.desc e₀ e₁) (boundary 1).ι p edge.map := ⟨by aesop⟩
    have := hp _ ⟨1⟩
    apply π₀.sound (yonedaEquiv sq.lift)
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₀_desc e₀ e₁, ← boundary₁.ι₀ ≫= sq.fac_left,
        boundary₁.ι₀_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
    · apply yonedaEquiv.symm.injective
      rw [← boundary₁.ι₁_desc e₀ e₁, ← boundary₁.ι₁ ≫= sq.fac_left,
        boundary₁.ι₁_ι_assoc, yonedaEquiv_symm_δ, Equiv.symm_apply_apply]
  · intro b
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have sq : CommSq (boundary.isInitial.to E) (boundary 0).ι p
      (yonedaEquiv.symm b) := ⟨boundary.isInitial.hom_ext _ _⟩
    have := hp _ ⟨0⟩
    refine ⟨π₀.mk (yonedaEquiv sq.lift), ?_⟩
    simp only [mapπ₀_mk]
    congr
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_comp]
    simp

lemma bijective_mapπ_succ (n : ℕ) (e : E _⦋0⦌) (b : B _⦋0⦌) (h : p.app _ e = b) :
    Function.Bijective (mapπ p (n + 1) e b h) := by
  have : Fibration p := by
    rw [fibration_iff]
    exact rlp_I_le_rlp_J _ hp
  constructor
  · suffices ∀ (y : π (n + 1) E e), mapπ p (n + 1) e b h y = 1 → y = 1 by
      intro y₁ y₂ hy
      rw [← mul_inv_eq_one]
      apply this
      rw [mapπ_mul, mapπ_inv, hy, mul_inv_cancel]
    intro y hy
    obtain ⟨x, rfl⟩ := HomotopySequence.exists_of_map₂_eq_one hy
    obtain rfl := (subsingleton_π_of_rlp_I (fiber_rlp_I hp b) _ _).elim x 1
    simp [HomotopySequence.map₁]
  · intro y
    apply HomotopySequence.exists_of_δ'_eq_one (i := 0)
    apply (subsingleton_π_of_rlp_I (fiber_rlp_I hp b) n _).elim

end W.of_rlp_I

include hp in
open W.of_rlp_I in
lemma W.of_rlp_I [IsFibrant E] [IsFibrant B] : KanComplex.W p := by
  rw [W_iff]
  exact ⟨of_rlp_I.bijective_mapπ₀ hp, bijective_mapπ_succ hp⟩

end

section

variable {E B : SSet.{u}} {p : E ⟶ B} [IsFibrant B] [Fibration p]
  (hp : KanComplex.W p)

include hp

lemma W.hasLiftingPropertyFixedTop_const (n : ℕ) (e : E _⦋0⦌) :
    HasLiftingPropertyFixedTop (boundary n).ι p (const e) := by
  intro b sq
  obtain ⟨b, rfl⟩ : ∃ (b' : B.PtSimplex n (p.app _ e)), b'.map = b := ⟨{
    map := b
    comm := by simp [← sq.w] }, rfl⟩
  obtain ⟨s, hs⟩ : ∃ (s : E.PtSimplex n e), mapπ p n e _ rfl (π.mk s) = π.mk b := by
    obtain ⟨s, hs⟩ := (hp.bijective n e _ rfl).2 (π.mk b)
    obtain ⟨s, rfl⟩ := s.mk_surjective
    exact ⟨s, hs⟩
  simp only [mapπ_mk, π.mk_eq_mk_iff] at hs
  replace hs := hs.some.homotopy
  have sq' : CommSq (const e) (∂Δ[n].ι ▷ Δ[1]) p hs.h := ⟨by simp⟩
  rw [← hasLift_iff_of_deformation (sq := sq') (t₀ := const e) (t₁ := const e) (by simp)
    (by simp) (b₁ := b.map) rfl (by simp)]
  exact ⟨⟨{ l := s.map }⟩⟩

variable [IsFibrant E]

lemma W.hasLiftingPropertyFixedTop_face {n : ℕ} (t : (∂Δ[n + 1] : SSet) ⟶ E)
    (e : E _⦋0⦌) (ht : ∀ (i : Fin (n + 2)) (_ : i ≠ 0),
      boundary.ι i ≫ t = const e) :
    HasLiftingPropertyFixedTop (boundary (n + 1)).ι p t := by
  obtain ⟨u, hu⟩ : ∃ (u : E.PtSimplex n e), u.map = boundary.ι 0 ≫ t := ⟨{
    map := boundary.ι 0 ≫ t
    comm := by
      obtain _ | n := n
      · ext
      ext i : 1
      rw [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const, comp_const]
      have : stdSimplex.{u}.δ i ≫ boundary.ι (0 : Fin (n + 3)) =
          stdSimplex.{u}.δ 0 ≫ boundary.ι i.succ := by
        simp only [← cancel_mono (Subcomplex.ι _), Category.assoc, boundary.ι_ι]
        exact (stdSimplex.δ_comp_δ (i := 0) (j := i) (by simp)).symm
      rw [reassoc_of% this, ht _ (Fin.succ_ne_zero _), comp_const]}, rfl⟩
  intro b sq
  have h : π.mk u = 1 := (hp.bijective n e _ rfl).1 (by
    simp only [mapπ_mk, mapπ_one]
    rw [π.mk_eq_one_iff]
    have (i : Fin (n + 2)) : stdSimplex.δ i ≫ b = boundary.ι i ≫ t ≫ p := by
      rw [sq.w, boundary.ι_ι_assoc]
    exact ⟨{
      map := b
      δ_succ_map := by simp [this, reassoc_of% (ht 1 (by simp))]
      δ_map_of_gt j hj := by simp [this, reassoc_of% (ht j (by aesop))]
    }⟩)
  rw [π.mk_eq_one_iff] at h
  replace h := h.some.homotopy
  obtain ⟨H, h₀, h₁⟩ : ∃ (H : (∂Δ[n + 1] : SSet) ⊗ Δ[1] ⟶ E), ι₀ ≫ H = t ∧
      ι₁ ≫ H = const e := by
    obtain _ | n := n
    · have ht₁ : boundary₁.ι₁ ≫ t = u.map := by rw [boundary₁.ι₁_eq_ι_zero, hu]
      have ht₀ : boundary₁.ι₀ ≫ t = const e := by rw [boundary₁.ι₀_eq_ι_one, ht 1 (by simp)]
      obtain ⟨H, h₀, h₁⟩ :=
        BinaryCofan.IsColimit.desc' (h := boundary₁.isColimitRightTensor Δ[1])
          (const e) h.h
      dsimp at H h₀ h₁
      refine ⟨H, ?_, ?_⟩
      · apply boundary₁.hom_ext
        · rw [← ι₀_comp_assoc, h₀, comp_const, ht₀]
        · rw [← ι₀_comp_assoc, h₁, ht₁, h.h₀]
      · apply boundary₁.hom_ext
        · rw [← ι₁_comp_assoc, h₀, comp_const, comp_const]
        · rw [← ι₁_comp_assoc, h₁, h.h₁, comp_const,
            Subcomplex.RelativeMorphism.const_map]
    · let f (i : Fin (n + 3)) : Δ[n + 1] ⊗ Δ[1] ⟶ E :=
        if i = 0 then h.h else const e
      obtain ⟨H, h'⟩ := boundary.exists_tensorRight_desc f (by
        intro j k hjk
        by_cases hj : j = 0
        · subst hj
          obtain ⟨k, rfl⟩  := Fin.eq_succ_of_ne_zero hjk.ne'
          simpa only [f, if_neg hjk.ne', Fin.pred_succ, comp_const, reduceIte,
            Subcomplex.ofSimplex_ι, comp_const, ← comp_whiskerRight_assoc,
            boundary.ι_ι] using (boundary.ι k ▷ _) ≫= h.rel
        · dsimp [f]
          rw [if_neg hj, if_neg (by rintro rfl; simp at hjk)]
          simp)
      refine ⟨H, ?_, ?_⟩
      · ext i : 1
        by_cases hi : i = 0
        · subst hi
          simp only [← ι₀_comp_assoc, h', f, if_pos, h.h₀, hu]
        · simp only [← ι₀_comp_assoc, h', f, if_neg hi, comp_const, ht i hi]
      · ext i : 1
        by_cases hi : i = 0
        · subst hi
          simp only [← ι₁_comp_assoc, h', f, if_pos, h.h₁,
            Subcomplex.RelativeMorphism.const_map, comp_const]
        · simp only [← ι₁_comp_assoc, h', f, if_neg hi, comp_const]
  apply (hasLiftingPropertyFixedTop_iff_of_deformation p H h₀ h₁).2
    (hp.hasLiftingPropertyFixedTop_const (n + 1) e)


lemma W.hasLiftingPropertyFixedTop {n : ℕ} (t : (∂Δ[n] : SSet) ⟶ E) :
    HasLiftingPropertyFixedTop (boundary n).ι p t := by
  obtain _ | n := n
  · intro b sq
    have : Nonempty (E _⦋0⦌) := (by
      obtain ⟨b, _⟩ := hp.bijective_mapπ₀.2 (π₀.mk (yonedaEquiv b))
      exact ⟨b.mk_surjective.choose⟩)
    obtain rfl : t = const (Classical.arbitrary _) := by ext
    apply hp.hasLiftingPropertyFixedTop_const
  · obtain ⟨h, h₀, h₁⟩ := horn.exists_contractible₀.{u} n
    let i : (horn.{u} (n + 1) 0 : SSet) ⟶ boundary (n + 1) :=
      Subcomplex.homOfLE (horn_le_boundary 0)
    let e : E _⦋0⦌  := (i ≫ t).app _ (horn.obj₀Mk 0 0 ⟨1, by simp, by simp⟩)
    obtain ⟨φ, hφ, hφ', _⟩ := homotopy_extension_property₁ i (terminal.from E) (h ≫ i ≫ t) t
      (by rw [reassoc_of% h₁]) (terminal.from _) (by simp) (by simp)
    rw [← hasLiftingPropertyFixedTop_iff_of_deformation p φ rfl hφ]
    exact hp.hasLiftingPropertyFixedTop_face _ e (fun j hj ↦ by
      replace hφ' := (horn.ι 0 j hj ▷ _) ≫= hφ'
      rw [← comp_whiskerRight_assoc,
        show horn.ι 0 j hj ≫ i = boundary.ι j from rfl] at hφ'
      rw [← ι₀_comp_assoc, hφ', ι₀_comp_assoc, reassoc_of% h₀, const_comp, comp_const])

end

lemma weakEquivalence_iff_of_fibration {E B : SSet.{u}} (p : E ⟶ B)
    [IsFibrant E] [IsFibrant B] [Fibration p] :
    I.rlp p ↔ KanComplex.W p :=
  ⟨fun hp ↦ W.of_rlp_I hp, fun hp ↦ by
    rintro _ _ _ ⟨n⟩
    exact ⟨fun _ ↦ hp.hasLiftingPropertyFixedTop _ _ _⟩⟩

end KanComplex

end SSet
