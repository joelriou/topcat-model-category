import TopCatModelCategory.SSet.Fiber
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.HomotopyGroup

universe u

open HomotopicalAlgebra CategoryTheory Simplicial SSet.modelCategoryQuillen
  MonoidalCategory ChosenFiniteProducts Limits Opposite

namespace SSet

namespace KanComplex

open Subcomplex
namespace HomotopySequence

variable {E B : SSet.{u}} (p : E ⟶ B) {b : B _⦋0⦌}
  {e : E _⦋0⦌} (he : p.app _ e = b)

def map₁ (n : ℕ) : π n (Subcomplex.fiber p b) (fiber.basePoint p he) → π n E e :=
  mapπ (Subcomplex.fiber p b).ι n (fiber.basePoint p he) e (by simp)

def map₂ (n : ℕ) : π n E e → π n B b := mapπ p n e b he

variable {p he}

structure DeltaStruct {n : ℕ} (s : B.PtSimplex (n + 1) b)
    (t : PtSimplex _ n (fiber.basePoint p he)) (i : Fin (n + 2)) where
  map : Δ[n + 1] ⟶ E
  map_p : map ≫ p = s.map := by aesop_cat
  δ_map : stdSimplex.δ i ≫ map = t.map ≫ (Subcomplex.fiber p b).ι := by aesop_cat
  δ_map_eq_const (j : Fin (n + 2)) (hi : j ≠ i) :
    stdSimplex.δ j ≫ map = const e := by aesop_cat

namespace DeltaStruct

attribute [reassoc (attr := simp)] map_p δ_map
attribute [reassoc] δ_map_eq_const

def relStructOfCastSucc {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (fiber.basePoint p he)} {i : Fin (n + 1)}
    (h : DeltaStruct s t i.castSucc) :
      PtSimplex.RelStruct (t.pushforward (Subpresheaf.ι _) e (by simp)) .const i where
  map := h.map
  δ_succ_map := h.δ_map_eq_const _ (by simp [Fin.ext_iff])
  δ_map_of_lt j hj := h.δ_map_eq_const j hj.ne
  δ_map_of_gt j hj := h.δ_map_eq_const j (by
    rintro rfl
    simp [Fin.lt_iff_val_lt_val] at hj)

def relStructOfSucc {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (fiber.basePoint p he)} {i : Fin (n + 1)}
    (h : DeltaStruct s t i.succ) :
      PtSimplex.RelStruct .const (t.pushforward (Subpresheaf.ι _) e (by simp))  i where
  map := h.map
  δ_succ_map := by simp
  δ_castSucc_map := h.δ_map_eq_const _ (by simp [Fin.ext_iff])
  δ_map_of_lt j hj := h.δ_map_eq_const j (by
    rintro rfl
    simp [Fin.lt_iff_val_lt_val] at hj)
  δ_map_of_gt j hj := h.δ_map_eq_const j hj.ne'

noncomputable def relStruct₀ {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : PtSimplex _ n (fiber.basePoint p he)} {i : Fin (n + 2)} [IsFibrant E]
    (h : DeltaStruct s t i) :
      PtSimplex.RelStruct₀ (t.pushforward (Subpresheaf.ι _) e (by simp)) .const := by
  apply Nonempty.some
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · exact ⟨(relStructOfCastSucc h).relStruct₀⟩
  · exact ⟨(relStructOfSucc (i := Fin.last n) h).relStruct₀.symm⟩

end DeltaStruct

section

variable (he) {n : ℕ}

lemma exists_deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    ∃ (t : PtSimplex _ n (fiber.basePoint p he)),
          Nonempty (DeltaStruct s t i) := by
  have sq : CommSq (const e) (horn (n + 1) i).ι p s.map := ⟨by
    have := Subcomplex.homOfLE (horn_le_boundary i) ≫= s.comm
    simp only [Subcomplex.homOfLE_ι_assoc, Subcomplex.ofSimplex_ι] at this
    rw [this, const_comp, comp_const, comp_const, he]⟩
  refine ⟨⟨Subcomplex.lift
      (stdSimplex.δ i ≫ sq.lift) ?_, ?_⟩, ⟨{
    map := sq.lift
    map_p := by simp
    δ_map := rfl
    δ_map_eq_const j hj := horn.ι _ _ hj ≫= sq.fac_left }⟩⟩
  · apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, Subcomplex.image_top,
      Subcomplex.range_le_fiber_iff,
      Category.assoc, sq.fac_right, PtSimplex.δ_map]
  · rw [← cancel_mono (Subpresheaf.ι _),
      Subcomplex.ofSimplex_ι, comp_const, const_comp, Subpresheaf.ι_app, fiber.basePoint_coe,
      Category.assoc, Subcomplex.lift_ι]
    obtain _ | n := n
    · ext x hx
      simp at hx
      exact ((Set.mem_empty_iff_false _).1 hx.2).elim
    · apply boundary.hom_ext
      intro j
      rw [boundary.ι_ι_assoc, comp_const]
      have fac (k : Fin (n + 3)) (hk : k ≠ i) := horn.ι i k hk ≫= sq.fac_left
      simp only [comp_const, horn.ι_ι_assoc] at fac
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · have := stdSimplex.{u}.δ_comp_δ (n := n) (i := 0) (j := j) (by simp)
        dsimp at this
        rw [← reassoc_of% this, fac _ (fun h ↦ by
          rw [Fin.ext_iff] at h
          simp at h), comp_const]
      · by_cases hj : j ≤ i
        · rw [stdSimplex.δ_comp_δ_assoc hj, fac, comp_const]
          rintro h
          rw [← Fin.succ_le_succ_iff, ← h] at hj
          simp at hj
        · simp only [not_le] at hj
          obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
          simp only [Fin.succ_castSucc]
          rw [← stdSimplex.δ_comp_δ_assoc hj, fac, comp_const]
          simp only [ne_eq, Fin.succ_inj]
          rintro rfl
          simp at hj

noncomputable def δ'' [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    PtSimplex _ n (fiber.basePoint p he) :=
  (exists_deltaStruct he s i).choose

noncomputable def deltaStruct [Fibration p] (s : B.PtSimplex (n + 1) b) (i : Fin (n + 2)) :
    DeltaStruct s (δ'' he s i) i :=
  (exists_deltaStruct he s i).choose_spec.some

variable {he} in
noncomputable def uniqueδ'' [Fibration p] {s s' : B.PtSimplex (n + 1) b} {i : Fin (n + 2)}
    {t t' : PtSimplex _ n (fiber.basePoint p he)} (hst : DeltaStruct s t i)
    (hst' : DeltaStruct s' t' i) (hs : s.Homotopy s') :
    t.Homotopy t' := Nonempty.some (by
  obtain ⟨α, hα₀, hα₁⟩ : ∃ (α : Δ[n + 1] ⊗ ∂Δ[1] ⟶ E),
    _ ◁ boundary₁.ι₀ ≫ α = fst _ _ ≫ hst.map ∧
    _ ◁ boundary₁.ι₁ ≫ α = fst _ _ ≫ hst'.map := by
      obtain ⟨α', hα'₀, hα'₁⟩ :=
        BinaryCofan.IsColimit.desc' (boundary₁.isColimitLeftTensor Δ[n + 1])
          (fst _ _ ≫ hst.map) (fst _ _ ≫ hst'.map)
      exact ⟨α', by simpa, by simpa⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ := (Subcomplex.unionProd.isPushout Λ[n + 1, i] ∂Δ[1]).exists_desc α
    (const e) (by
      apply boundary₁.hom_ext_leftTensor
      · rw [MonoidalCategory.whisker_exchange_assoc, hα₀,
          ← cancel_epi (stdSimplex.rightUnitor _).inv,
          whiskerRight_fst_assoc, stdSimplex.rightUnitor_inv_fst_assoc, comp_const,
          comp_const]
        exact horn.hom_ext' (fun j hj ↦ by simpa using hst.δ_map_eq_const j hj)
      · rw [MonoidalCategory.whisker_exchange_assoc, hα₁,
          ← cancel_epi (stdSimplex.rightUnitor _).inv,
          whiskerRight_fst_assoc, stdSimplex.rightUnitor_inv_fst_assoc, comp_const,
          comp_const]
        exact horn.hom_ext' (fun j hj ↦ by simpa using hst'.δ_map_eq_const j hj))
  have := (anodyneExtensions.subcomplex_unionProd_mem_of_left _ (boundary 1)
    (anodyneExtensions.horn_ι_mem n i)).hasLeftLiftingProperty p
  have sq : CommSq φ ((horn (n + 1) i).unionProd (boundary 1)).ι p hs.h := ⟨by
    apply (Subcomplex.unionProd.isPushout _ _).hom_ext
    . rw [reassoc_of% hφ₁]
      apply boundary₁.hom_ext_leftTensor
      · rw [reassoc_of% hα₀, hst.map_p, Subcomplex.unionProd.ι₁_ι_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, boundary₁.ι₀_ι, ← hs.h₀,
          ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
          stdSimplex.fst_rightUnitor_inv_assoc]
      · rw [reassoc_of% hα₁, hst'.map_p, Subcomplex.unionProd.ι₁_ι_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, boundary₁.ι₁_ι, ← hs.h₁,
          ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
          stdSimplex.fst_rightUnitor_inv_assoc]
    · have := Subcomplex.homOfLE (horn_le_boundary i) ▷ Δ[1] ≫= hs.rel.symm
      rw [Subcomplex.ofSimplex_ι, comp_const] at this
      rwa [reassoc_of% hφ₂, const_comp, he, Subcomplex.unionProd.ι₂_ι_assoc]⟩
  have hsq₀ : ι₀ ≫ sq.lift = hst.map := by
    rw [← cancel_epi (stdSimplex.rightUnitor _).hom, stdSimplex.rightUnitor_hom, ← hα₀, ← hφ₁]
    conv_rhs => rw [← sq.fac_left]
    rfl
  have hsq₁ : ι₁ ≫ sq.lift = hst'.map := by
    rw [← cancel_epi (stdSimplex.rightUnitor _).hom, stdSimplex.rightUnitor_hom, ← hα₁, ← hφ₁]
    conv_rhs => rw [← sq.fac_left]
    rfl
  refine ⟨{
      h := Subcomplex.lift (stdSimplex.δ i ▷ _ ≫ sq.lift) (by
        have := boundary.ι i ▷ Δ[1] ≫= hs.rel
        rw [← MonoidalCategory.comp_whiskerRight_assoc, boundary.ι_ι,
          Subcomplex.ofSimplex_ι, comp_const, comp_const, comp_const] at this
        rwa [Subcomplex.preimage_eq_top_iff, Subcomplex.range_le_fiber_iff,
          Category.assoc, sq.fac_right])
      h₀ := by
        rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι,
          ι₀_comp_assoc, hsq₀, hst.δ_map]
      h₁ := by
        rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι,
          ι₁_comp_assoc, hsq₁, hst'.δ_map]
      rel := by
        rw [← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.lift_ι, Subpresheaf.toPresheaf_obj,
          Subcomplex.ofSimplex_ι, comp_const, const_comp, Subpresheaf.ι_app, fiber.basePoint_coe]
        obtain _ | n := n
        · ext
        have (k : Fin (n + 3)) (hki : k ≠ i) : stdSimplex.δ k ▷ _ ≫ sq.lift = const e := by
          have := (horn.ι i k hki ▷ _ ≫ Subcomplex.unionProd.ι₂ _ _) ≫= sq.fac_left
          rwa [Category.assoc, Category.assoc, hφ₂, comp_const] at this
        apply boundary.hom_ext_tensorRight
        intro j
        obtain ⟨k, hki, l, fac⟩ : ∃ (k : Fin (n + 3)) (hki : k ≠ i) (l : Fin (n + 2)),
          stdSimplex.{u}.δ j ≫ stdSimplex.δ i = stdSimplex.δ l ≫ stdSimplex.δ k := by
            by_cases hj : j.castSucc < i
            · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
              exact ⟨j.castSucc, hj.ne, _, stdSimplex.δ_comp_δ (Fin.succ_le_succ_iff.1 hj)⟩
            · simp only [not_lt] at hj
              obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
                (Fin.ne_last_of_lt (Fin.le_castSucc_iff.1 hj))
              exact ⟨_, fun h ↦ by simp [← h] at hj, _,
                (stdSimplex.δ_comp_δ (Fin.castSucc_le_castSucc_iff.1 hj)).symm⟩
        rw [comp_const, ← comp_whiskerRight_assoc, boundary.ι_ι, ← comp_whiskerRight_assoc,
          fac, comp_whiskerRight_assoc, this k hki, comp_const]
  }⟩)

variable {he} in
noncomputable def deltaStructOfHomotopy
    [Fibration p] {s : B.PtSimplex (n + 1) b} {i : Fin (n + 2)}
    {t t' : PtSimplex _ n (fiber.basePoint p he)} (hst : DeltaStruct s t i) (h : t.Homotopy t') :
    DeltaStruct s t' i := Nonempty.some (by
  obtain ⟨α, hα₀, hα⟩ : ∃ (α : (boundary (n + 1) : SSet) ⊗ Δ[1] ⟶ E),
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), (boundary.ι j ▷ Δ[1]) ≫ α = const e) ∧
      (boundary.ι i ▷ Δ[1] ≫ α = h.h ≫ Subcomplex.ι _) := by
    obtain _ | n := n
    · fin_cases i
      · obtain ⟨α, hα₀, hα₁⟩ := BinaryCofan.IsColimit.desc'
          (boundary₁.isColimitRightTensor.{u} Δ[1]) (const e) (h.h ≫ Subcomplex.ι _)
        dsimp at hα₀ hα₁ ⊢
        refine ⟨α, ?_, ?_⟩
        · intro j hj
          fin_cases j
          · simp at hj
          · rw [← hα₀]
            congr
            simp [← cancel_mono (Subcomplex.ι _)]
        · rw [← hα₁]
          congr
          simp [← cancel_mono (Subcomplex.ι _)]
      · obtain ⟨α, hα₀, hα₁⟩ := BinaryCofan.IsColimit.desc'
          (boundary₁.isColimitRightTensor.{u} Δ[1]) (h.h ≫ Subcomplex.ι _) (const e)
        dsimp at hα₀ hα₁ ⊢
        refine ⟨α, ?_, ?_⟩
        · intro j hj
          fin_cases j
          · rw [← hα₁]
            congr
            simp [← cancel_mono (Subcomplex.ι _)]
          · simp at hj
        · rw [← hα₀]
          congr
          simp [← cancel_mono (Subcomplex.ι _)]
    · let f (j : Fin (n + 3)) : Δ[n + 1] ⊗ Δ[1] ⟶ E :=
        if j = i then h.h ≫ Subcomplex.ι _ else const e
      have hf (j : Fin (n + 3)) (k : Fin (n + 2)) :
          stdSimplex.δ k ▷ _ ≫ f j = const e := by
        dsimp [f]
        split_ifs with hj
        · subst hj
          have := boundary.ι k ▷ _ ≫= h.rel
          rw [← comp_whiskerRight_assoc, boundary.ι_ι, const_comp, comp_const, comp_const,
            Subcomplex.ofSimplex_ι, const_app, SimplexCategory.const_eq_id,
            op_id, FunctorToTypes.map_id_apply] at this
          rw [reassoc_of% this, const_comp, Subpresheaf.ι_app, fiber.basePoint_coe]
        · simp
      obtain ⟨α, hα⟩ := boundary.exists_tensorRight_desc f (by simp [hf])
      dsimp [f] at hα
      refine ⟨α, fun j hj ↦ by rw [hα, if_neg hj], by rw [hα, if_pos rfl]⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ := (Subcomplex.unionProd.isPushout (boundary (n + 1))
    (stdSimplex.face {(0 : Fin 2)})).exists_desc (fst _ _ ≫ hst.map) α (by
      rw [← cancel_epi (_ ◁ (stdSimplex.faceSingletonIso (0 : Fin 2)).hom),
        whiskerRight_fst_assoc, whiskerLeft_fst_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc,
        stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
      refine boundary.hom_ext_tensorRight (fun j ↦ ?_)
      rw [whiskerRight_fst_assoc, boundary.ι_ι_assoc, ← whisker_exchange_assoc]
      by_cases hj : j = i
      · subst hj
        rw [hα, hst.δ_map, ← h.h₀, Category.assoc,
          ← stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
        rfl
      · rw [hα₀ j hj, hst.δ_map_eq_const j hj, comp_const, comp_const])
  have sq : CommSq φ (Subcomplex.ι _) p (fst _ _ ≫ s.map) := ⟨by
    apply (Subcomplex.unionProd.isPushout _ _).hom_ext
    · simp [reassoc_of% hφ₁]
    · simp only [reassoc_of% hφ₂, Subcomplex.unionProd.ι₂_ι_assoc,
        whiskerRight_fst_assoc, Subcomplex.RelativeMorphism.comm,
        Subcomplex.ofSimplex_ι, comp_const]
      refine boundary.hom_ext_tensorRight (fun j ↦ ?_)
      rw [comp_const]
      by_cases hj : j = i
      · subst hj
        rw [reassoc_of% hα, Subcomplex.fiber_ι_comp, comp_const]
      · rw [reassoc_of% (hα₀ j hj), const_comp, he]⟩
  have := (anodyneExtensions.subcomplex_unionProd_mem_of_right (boundary (n + 1))
    _ (anodyneExtensions.face 0)).hasLeftLiftingProperty p
  have fac (j) := (ι₁ ≫ boundary.ι j ▷ _ ≫ Subcomplex.unionProd.ι₂ _ _) ≫= sq.fac_left
  simp only [Category.assoc, hφ₂, Subcomplex.unionProd.ι₂_ι_assoc,
    ← comp_whiskerRight_assoc, boundary.ι_ι, ι₁_comp_assoc (Y := Δ[n + 1])] at fac
  refine ⟨{
    map := ι₁ ≫ sq.lift
    map_p := by simp
    δ_map := by rw [fac, hα, h.h₁_assoc]
    δ_map_eq_const j hj := by rw [fac, hα₀ _ hj, comp_const] }⟩
  )

end

variable (p he n) in
noncomputable def δ' (n : ℕ) [Fibration p] [IsFibrant E] [IsFibrant B] (i : Fin (n + 2)) :
    π (n + 1) B b → π n (Subcomplex.fiber p b) (fiber.basePoint p he) :=
  Quot.lift (fun s ↦ (δ'' he s i).homotopyClass) (fun s s' hs ↦
    Quot.sound ⟨uniqueδ'' (deltaStruct he s i) (deltaStruct he s' i) hs.some⟩)

lemma δ'_mk_eq_of_deltaStruct {n : ℕ} [Fibration p] [IsFibrant E] [IsFibrant B]
    {i : Fin (n + 2)} {x : B.PtSimplex (n + 1) b}
    {t : SSet.PtSimplex (Subcomplex.fiber p b) n (fiber.basePoint p he)}
    (h : DeltaStruct x t i) :
    δ' p he n i (π.mk x) = π.mk t :=
  Quot.sound ⟨uniqueδ'' (deltaStruct he x i) h (.refl x)⟩

lemma δ'_mk_iff_nonempty_deltaStruct {n : ℕ} [Fibration p] [IsFibrant E] [IsFibrant B]
    {i : Fin (n + 2)} (s : B.PtSimplex (n + 1) b)
    {t : SSet.PtSimplex (Subcomplex.fiber p b) n (fiber.basePoint p he)} :
    δ' p he n i (π.mk s) = π.mk t ↔ Nonempty (DeltaStruct s t i) := by
  refine ⟨fun h ↦ ?_, fun ⟨hst⟩ ↦ δ'_mk_eq_of_deltaStruct hst⟩
  replace h : (δ'' he s i).Homotopy t := by
    rw [δ'_mk_eq_of_deltaStruct (deltaStruct he s i), π.mk_eq_mk_iff] at h
    exact h.some.homotopy
  exact ⟨deltaStructOfHomotopy (deltaStruct he s i) h⟩

variable (he) in
lemma δ'_naturality [Fibration p] [IsFibrant E] [IsFibrant B]
    {E' B' : SSet.{u}} {p' : E' ⟶ B'} {e' : E' _⦋0⦌} {b' : B' _⦋0⦌} (he' : p'.app _ e' = b')
    [Fibration p'] [IsFibrant E'] [IsFibrant B'] (n : ℕ) (i : Fin (n + 2))
    (x : π (n + 1) B b) (α : E ⟶ E') (β : B ⟶ B') (fac : α ≫ p' = p ≫ β)
    (h : α.app _ e = e') :
    δ' p' he' n i (mapπ β (n + 1) b b' (by
      rw [← he', ← he, ← h]
      apply congr_fun (congr_app fac (op ⦋0⦌)).symm) x) =
    mapπ (Subcomplex.mapFiber p p' α β fac b b' (by
        rw [← he', ← he, ← h]
        apply congr_fun (congr_app fac (op ⦋0⦌)).symm)) n (fiber.basePoint p he)
      (fiber.basePoint p' he') (by aesop) (δ' p he n i x) := by
  obtain ⟨s, rfl⟩ := x.mk_surjective
  obtain ⟨t, ⟨hst⟩⟩ : ∃ (t : SSet.PtSimplex (Subcomplex.fiber p b) n (fiber.basePoint p he)),
    Nonempty (DeltaStruct s t i) := ⟨_, ⟨deltaStruct he s i⟩⟩
  rw [δ'_mk_eq_of_deltaStruct hst, mapπ_mk, mapπ_mk, δ'_mk_iff_nonempty_deltaStruct]
  exact ⟨{
      map := hst.map ≫ α
      δ_map_eq_const j hj := by
        rw [hst.δ_map_eq_const_assoc j hj, ← h, const_comp]
  }⟩

variable [IsFibrant B]

@[simp]
lemma map₂_map₁_apply {n : ℕ} (x : π n (Subcomplex.fiber p b) (fiber.basePoint p he)) :
    map₂ p he n (map₁ p he n x) = 1 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  dsimp only [map₁, map₂]
  rw [mapπ_mapπ, mapπ_mk, π.mk_eq_one_iff]
  refine ⟨PtSimplex.RelStruct₀.ofEq ?_⟩
  ext : 1
  dsimp
  rw [Subcomplex.fiber_ι_comp, comp_const]

variable [Fibration p] [IsFibrant E] (he)

@[simp]
lemma δ'_map₂_apply {n : ℕ} (x : π (n + 1) E e) (i : Fin (n + 2)) :
    δ' p he n i (map₂ p he (n + 1) x) = 1 := by
  obtain ⟨s, rfl⟩ := x.mk_surjective
  exact δ'_mk_eq_of_deltaStruct { map := s.map }

@[simp]
lemma map₁_δ'_apply {n : ℕ} (x : π (n + 1) B b) (i : Fin (n + 2)) :
    map₁ p he n (δ' p he n i x) = 1 := by
  obtain ⟨s, rfl⟩ := x.mk_surjective
  dsimp [map₁]
  have h := deltaStruct he s i
  rw [δ'_mk_eq_of_deltaStruct h, mapπ_mk, π.mk_eq_one_iff]
  exact ⟨h.relStruct₀⟩

variable {he} in
lemma exists_of_δ'_eq_one {n : ℕ} {x : π (n + 1) B b} {i : Fin (n + 2)}
    (hx : δ' p he n i x = 1) :
    ∃ (y : π (n + 1) E e), map₂ p he (n + 1) y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change _ = π.mk _ at hx
  rw [δ'_mk_iff_nonempty_deltaStruct] at hx
  obtain ⟨h⟩ := hx
  refine ⟨π.mk (.mk h.map (fun j ↦ ?_)), ?_⟩
  · by_cases hj : j = i
    · subst hj
      simp
    · exact h.δ_map_eq_const j hj
  · simp only [map₂, mapπ_mk]
    congr
    ext : 1
    exact h.map_p

lemma δ'_eq_one_iff {n : ℕ} (x : π (n + 1) B b) (i : Fin (n + 2))  :
    δ' p he n i x = 1 ↔ ∃ (y : π (n + 1) E e), map₂ p he (n + 1) y = x :=
  ⟨exists_of_δ'_eq_one, by rintro ⟨y, rfl⟩; simp⟩

@[simp]
lemma δ'_one (n : ℕ) (i : Fin (n + 2)) :
    δ' p he n i 1 = 1 := by
  rw [δ'_eq_one_iff]
  exact ⟨1, by simp [map₂]⟩

variable {he}

lemma exists_of_map₁_eq_one {n : ℕ} {x : π n (Subcomplex.fiber p b) (fiber.basePoint p he)}
    (hx : map₁ p he n x = 1) (i : Fin (n + 2)):
    ∃ (y : π (n + 1) B b), δ' p he n i y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨s, hs, hs₀⟩ : ∃ (s : Δ[n + 1] ⟶ E),
        (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ s = const e) ∧
          stdSimplex.δ i ≫ s = x.map ≫ Subcomplex.ι _ := by
    change _ = π.mk _ at hx
    simp only [map₁, mapπ_mk] at hx
    rw [π.mk_eq_mk_iff] at hx
    by_cases hi : i = 0
    · subst hi
      replace hx := hx.some
      refine ⟨hx.map, fun j hj ↦ ?_, hx.δ_castSucc_map⟩
      obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      by_cases hj : j = 0
      · subst hj
        exact hx.δ_succ_map
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        exact hx.δ_map_of_gt _ (by simp only [Fin.succ_lt_succ_iff, Fin.succ_pos])
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
      replace hx := hx.some.symm.relStruct i
      refine ⟨hx.map, fun j hj ↦ ?_, by simp⟩
      obtain hj | rfl | hj := lt_trichotomy j i.succ
      · obtain hj | rfl := (Fin.le_castSucc_iff.2 hj).lt_or_eq
        · apply hx.δ_map_of_lt j hj
        · simp
      · simp at hj
      · apply hx.δ_map_of_gt j hj
  refine ⟨π.mk (.mk (s ≫ p) ?_), ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj
      simp [reassoc_of% hs₀]
    · rw [reassoc_of% (hs j hj), const_comp, he]
  · rw [δ'_mk_iff_nonempty_deltaStruct]
    exact ⟨{ map := s }⟩

lemma map₁_eq_one_iff {n : ℕ} (x : π n (Subcomplex.fiber p b)
    (fiber.basePoint p he)) (i : Fin (n + 2)) :
    map₁ p he n x = 1 ↔ ∃ (y : π (n + 1) B b), δ' p he n i y = x :=
  ⟨fun hx ↦ exists_of_map₁_eq_one hx i, by rintro ⟨y, rfl⟩; simp⟩

lemma exists_of_map₂_eq_one {n : ℕ} {x : π n E e} (hx : map₂ p he n x = 1) :
    ∃ (y : π n (Subcomplex.fiber p b) (fiber.basePoint p he)), map₁ p he n y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change _ = π.mk _ at hx
  simp only [map₂, mapπ_mk, π.mk_eq_mk_iff] at hx
  replace hx := hx.some.homotopy
  obtain ⟨φ, hφ₁, hφ₂⟩ := (Subcomplex.unionProd.isPushout (boundary n)
    (stdSimplex.face {(0 : Fin 2)})).exists_desc (fst _ _ ≫ x.map) (const e) (by simp)
  have := (anodyneExtensions.subcomplex_unionProd_mem_of_right (boundary n)
    _ (anodyneExtensions.face 0)).hasLeftLiftingProperty p
  have sq : CommSq φ (Subcomplex.ι _) p hx.h := ⟨by
    apply (Subcomplex.unionProd.isPushout _ _).hom_ext
    · rw [reassoc_of% hφ₁, Subcomplex.unionProd.ι₁_ι_assoc,
        ← cancel_epi (_ ◁ (stdSimplex.faceSingletonIso (0 : Fin 2)).hom),
        ← MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_fst_assoc,
        stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ,
        ← cancel_epi (stdSimplex.rightUnitor _).inv,
        stdSimplex.rightUnitor_inv_fst_assoc,
        stdSimplex.rightUnitor_inv_map_δ_one_assoc,
        hx.h₀, PtSimplex.pushforward_map]
    · rw [reassoc_of% hφ₂, Subcomplex.unionProd.ι₂_ι_assoc, hx.rel, const_comp,
        Subcomplex.ofSimplex_ι, he, comp_const, comp_const]⟩
  refine ⟨π.mk { map := Subcomplex.lift (ι₁ ≫ sq.lift) ?_, comm := ?_ }, ?_⟩
  · rw [Subcomplex.preimage_eq_top_iff, Subcomplex.range_le_fiber_iff, Category.assoc,
        sq.fac_right, hx.h₁, Subcomplex.RelativeMorphism.const_map]
  · obtain _ | n := n
    · ext
    · refine boundary.hom_ext (fun i ↦ ?_)
      have := ι₁ ≫= boundary.ι i ▷ _ ≫= (Subcomplex.unionProd.ι₂ _ _ ≫= sq.fac_left)
      rw [Subcomplex.unionProd.ι₂_ι_assoc, ← comp_whiskerRight_assoc,
        boundary.ι_ι, ι₁_comp_assoc, hφ₂, comp_const, comp_const] at this
      rwa [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, Subcomplex.lift_ι,
        boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const, comp_const, const_comp,
        Subpresheaf.ι_app, fiber.basePoint_coe]
  · symm
    simp only [map₁, mapπ_mk, π.mk_eq_mk_iff]
    refine ⟨PtSimplex.Homotopy.relStruct₀ ?_⟩
    exact {
      h := sq.lift
      h₀ := by
        have := Subcomplex.unionProd.ι₁ _ _ ≫= sq.fac_left
        rwa [Subcomplex.unionProd.ι₁_ι_assoc, hφ₁,
          ← cancel_epi (_ ◁ (stdSimplex.faceSingletonIso (0 : Fin 2)).hom),
          ← cancel_epi (stdSimplex.rightUnitor _).inv,
          whiskerLeft_fst_assoc, stdSimplex.rightUnitor_inv_fst_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc,
          stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ,
          stdSimplex.rightUnitor_inv_map_δ_one_assoc] at this
      h₁ := by simp
      rel := by
        have := Subcomplex.unionProd.ι₂ _ _ ≫= sq.fac_left
        rw [Subcomplex.unionProd.ι₂_ι_assoc, hφ₂] at this
        rwa [const_comp, comp_const, Subcomplex.ofSimplex_ι, const_app,
          SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]
    }

variable (he) in
lemma map₂_eq_one_iff {n : ℕ} (x : π n E e) :
    map₂ p he n x = 1 ↔
      ∃ (y : π n (Subcomplex.fiber p b) (fiber.basePoint p he)), map₁ p he n y = x :=
  ⟨fun hx ↦ exists_of_map₂_eq_one hx, by rintro ⟨y, rfl⟩; simp⟩

end HomotopySequence

end KanComplex

end SSet
