import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Nonempty
import TopCatModelCategory.SSet.Boundary
import TopCatModelCategory.SSet.NonDegenerateSimplices
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Finite.Card

universe u

open CategoryTheory Simplicial

namespace SSet

section

variable {X : SSet.{u}}

lemma Subcomplex.strictMono_card_n [X.IsFinite] :
    StrictMono (fun (A : X.Subcomplex) ↦ Nat.card A.toSSet.N) := by
  intro A B h
  dsimp
  let φ : A.toSSet.N → B.toSSet.N := mapN (Subcomplex.homOfLE h.le)
  have hφ : Function.Injective φ := N.mapN_injective_of_mono _
  cases (Nat.card_le_card_of_injective _ hφ).lt_or_eq
  · assumption
  · replace hφ : Function.Bijective φ := by
      rw [Nat.bijective_iff_injective_and_card]
      tauto
    refine (h.not_ge ?_).elim
    rw [le_iff_contains_nonDegenerate]
    rintro n ⟨x, hx⟩ hb
    dsimp at hb ⊢
    obtain ⟨a, ha⟩ := hφ.2 (N.mk ⟨x, hb⟩ (by rwa [Subcomplex.mem_nonDegenerate_iff]))
    obtain ⟨m, ⟨⟨x', h₁⟩, h₂⟩, rfl⟩ := a.mk_surjective
    dsimp [φ] at ha
    rw [N.ext_iff, toS_mapN_of_mono] at ha
    obtain rfl : m = n := S.dim_eq_of_eq ha
    obtain rfl : x' = x := by simpa [S.ext_iff', Subtype.ext_iff] using ha
    exact h₁

lemma Subcomplex.natCard_n_lt_of_ne_top [X.IsFinite] (A : X.Subcomplex)
    (hA : A ≠ ⊤) : Nat.card A.toSSet.N < Nat.card X.N :=
  lt_of_lt_of_eq (Subcomplex.strictMono_card_n hA.lt_top) (Nat.card_eq_of_bijective _
    ((N.functor ⋙ CategoryTheory.forget PartOrd).mapIso
      (Subcomplex.topIso X)).toEquiv.bijective)

instance [X.IsFinite] : WellFoundedLT X.Subcomplex where
  wf := by
    rw [WellFounded.wellFounded_iff_no_descending_seq]
    exact ⟨fun ⟨f, hf⟩ ↦
      not_strictAnti_of_wellFoundedLT (fun n ↦ Nat.card (f n).toSSet.N)
        (strictAnti_nat_of_succ_lt (fun n ↦ Subcomplex.strictMono_card_n (hf n)))⟩

end

variable (P : SSet.{u} → Prop)

lemma finite_induction
    (hP₀ : ∀ (X : SSet.{u}) [X.HasDimensionLT 0], P X)
    (hP : ∀ ⦃X₀ X : SSet.{u}⦄ (i : X₀ ⟶ X) ⦃n : ℕ⦄ ⦃a : (∂Δ[n] : SSet) ⟶ X₀⦄
      ⦃b : Δ[n] ⟶ X⦄ (_ : IsPushout a ∂Δ[n].ι i b) [X.IsFinite], P X₀ → P X)
    (X : SSet.{u}) [X.IsFinite] : P X := by
  generalize hd : Nat.card X.N = d
  induction' d using Nat.strong_induction_on with d hd' generalizing X
  have hX (A : X.Subcomplex) (hA : A ≠ ⊤) : P A := by
    subst hd
    exact hd' _ (A.natCard_n_lt_of_ne_top hA) _ rfl
  clear d hd' hd
  obtain ⟨n, hn⟩ := X.hasDimensionLT_of_isFinite
  induction' n using Nat.strong_induction_on with n hn'
  obtain _ | n := n
  · apply hP₀
  · by_cases hn : X.HasDimensionLT n
    · exact hn' n (by omega) hn
    · obtain ⟨x, hx⟩ : Nonempty (X.nonDegenerate n) := by
        by_contra!
        simp only [nonempty_subtype, not_exists] at this
        apply hn
        constructor
        intro d hd
        obtain hd | rfl := hd.lt_or_eq
        · exact X.degenerate_eq_top_of_hasDimensionLT (n + 1) d (by omega)
        · ext x
          simpa [mem_degenerate_iff_notMem_nonDegenerate] using this x
      let A : X.Subcomplex := ⨆ (s : ({N.mk x hx}ᶜ : Set _)), s.1.subcomplex
      have hA' : x ∉ A.obj _ := fun hA' ↦ by
        simp only [A, Subpresheaf.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
          Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at hA'
        obtain ⟨s, hs, hx'⟩ := hA'
        have hs : N.mk x hx < s := by
          refine lt_of_le_of_ne ?_ (Ne.symm hs)
          rwa [N.le_iff, Subpresheaf.ofSection_le_iff]
        have := N.lt_of_lt hs
        dsimp at this
        have := X.dim_lt_of_nondegenerate ⟨_, s.nonDegenerate⟩ (n + 1)
        omega
      have hA : A ≠ ⊤ := fun hA ↦ by simp [hA] at hA'
      obtain ⟨B, lt, d, t, b, sq⟩ := boundary.exists_isPushout_of_ne_top _ hA
      have hB : x ∈ B.obj _ := by
        obtain ⟨s, hs₁, hs₂⟩ : ∃ (s : X.N), s.simplex ∈ B.obj _ ∧ s.simplex ∉ A.obj _:= by
          by_contra!
          apply lt.not_ge
          rw [Subcomplex.le_iff_contains_nonDegenerate]
          intro e x hB
          exact this (N.mk _ x.2) hB
        obtain rfl : s = N.mk _ hx := by
          by_contra!
          apply hs₂
          simp only [Subpresheaf.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
            Set.mem_singleton_iff, Set.mem_iUnion, exists_prop, A]
          exact ⟨s, this, Subcomplex.mem_ofSimplex_obj _⟩
        exact hs₁
      obtain rfl : B = ⊤ := by
        rw [Subcomplex.eq_top_iff_contains_nonDegenerate]
        intro e y hy
        by_cases hxy : N.mk y hy = N.mk x hx
        · obtain rfl : e = n := by
            rw [N.ext_iff] at hxy
            exact S.dim_eq_of_eq hxy
          obtain rfl : y = x := by
            simpa [N.ext_iff, S.ext_iff'] using hxy
          exact hB
        · apply lt.le
          simp only [Subpresheaf.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
            Set.mem_singleton_iff, Set.mem_iUnion, exists_prop, A]
          exact ⟨N.mk y hy, hxy, Subcomplex.mem_ofSimplex_obj _⟩
      exact hP A.ι (a := t) (b := b ≫ (Subcomplex.topIso _).hom)
        (sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Subcomplex.topIso _)
        rfl rfl rfl rfl) (hX _ hA)

end SSet
