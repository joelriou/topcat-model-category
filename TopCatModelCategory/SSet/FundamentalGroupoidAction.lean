module

public import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
public import TopCatModelCategory.SSet.FundamentalGroupoid
public import TopCatModelCategory.SSet.HomotopyGroup

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
  SSet.modelCategoryQuillen

namespace SSet

namespace PtSimplex.Homotopy

open KanComplex

variable {X : SSet.{u}} (x₀ : X _⦋0⦌) {s t : X _⦋0⦌}

noncomputable def equiv₀ :
    ((PtSimplex.equiv₀ x₀).symm s).Homotopy ((PtSimplex.equiv₀ x₀).symm t) ≃
      FundamentalGroupoid.Edge { pt := s } { pt := t } where
  toFun h := FundamentalGroupoid.Edge.mk ((stdSimplex.leftUnitor _).inv ≫ h.h)
    (by rw [← ι₀_stdSimplex_zero_assoc, h.h₀, PtSimplex.equiv₀_symm_apply_map,
      yonedaEquiv_symm_zero])
    (by rw [← ι₁_stdSimplex_zero_assoc, h.h₁, PtSimplex.equiv₀_symm_apply_map,
      yonedaEquiv_symm_zero])
  invFun e :=
    { h := snd _ _ ≫ e.map
      h₀ := by
        rw [ι₀_snd_assoc, const_comp, e.comm₀', PtSimplex.equiv₀_symm_apply_map,
          yonedaEquiv_symm_zero]
      h₁ := by
        rw [ι₁_snd_assoc, const_comp, e.comm₁', PtSimplex.equiv₀_symm_apply_map,
          yonedaEquiv_symm_zero] }
  left_inv _ := by simp
  right_inv _ := rfl

end PtSimplex.Homotopy

namespace KanComplex

namespace FundamentalGroupoid

structure ActionStruct {X : SSet.{u}} {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}
    (p : Edge x₀ x₁) (s : X.PtSimplex n x₀.pt) (t : X.PtSimplex n x₁.pt) where
  map : Δ[n] ⊗ Δ[1] ⟶ X
  whiskerRight_ι_comp_map : (boundary n).ι ▷ Δ[1] ≫ map = snd _ _ ≫ p.map := by aesop_cat
  ι₀_map : ι₀ ≫ map = s.map := by aesop_cat
  ι₁_map : ι₁ ≫ map = t.map := by aesop_cat

namespace ActionStruct

attribute [reassoc (attr := simp)] ι₀_map ι₁_map whiskerRight_ι_comp_map

variable {X : SSet.{u}} {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}
    {p : Edge x₀ x₁}

section

variable {s : PtSimplex X n x₀.pt} {t : PtSimplex X n x₁.pt}
  (h : ActionStruct p s t)

@[reassoc (attr := simp)]
lemma δ_one_map :
    _ ◁ stdSimplex.δ 1 ≫ h.map = (stdSimplex.rightUnitor _).hom ≫ s.map := by
  rw [← h.ι₀_map, ← stdSimplex.rightUnitor_inv_map_δ_one_assoc,
    Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma δ_zero_map :
    _ ◁ stdSimplex.δ 0 ≫ h.map = (stdSimplex.rightUnitor _).hom ≫ t.map := by
  rw [← h.ι₁_map, ← stdSimplex.rightUnitor_inv_map_δ_zero_assoc,
    Iso.hom_inv_id_assoc]

noncomputable def pushforward {Y : SSet.{u}} (f : X ⟶ Y) :
    ActionStruct (p.pushforward f) (s.pushforward f _ rfl)
      (t.pushforward f _ rfl) where
  map := h.map ≫ f

noncomputable def id (s : X.PtSimplex n x₀.pt) : ActionStruct (Edge.id x₀) s s where
  map := fst _ _ ≫ s.map

end

variable (p) in
noncomputable def equiv₀ {s t : X _⦋0⦌} :
    ActionStruct p ((PtSimplex.equiv₀ _).symm s) ((PtSimplex.equiv₀ _).symm t) ≃
      Edge { pt := s } { pt := t } where
  toFun h := Edge.mk ((stdSimplex.leftUnitor _).inv ≫ h.map)
    (by rw [← ι₀_stdSimplex_zero_assoc, h.ι₀_map, PtSimplex.equiv₀_symm_apply_map,
        yonedaEquiv_symm_zero])
    (by rw [← ι₁_stdSimplex_zero_assoc, h.ι₁_map, PtSimplex.equiv₀_symm_apply_map,
        yonedaEquiv_symm_zero])
  invFun e :=
    { map := snd _ _ ≫ e.map
      ι₀_map := by
        rw [ι₀_snd_assoc, const_comp, e.comm₀', PtSimplex.equiv₀_symm_apply_map,
          yonedaEquiv_symm_zero]
      ι₁_map := by
        rw [ι₁_snd_assoc, const_comp, e.comm₁', PtSimplex.equiv₀_symm_apply_map,
          yonedaEquiv_symm_zero] }
  left_inv _ := by simp
  right_inv _ := rfl

end ActionStruct

namespace action

variable {X : SSet.{u}} [IsFibrant X] {x₀ x₁ : FundamentalGroupoid X} {n : ℕ}

lemma exists_actionStruct (p : Edge x₀ x₁) (s : X.PtSimplex n x₀.pt) :
    ∃ t, Nonempty (ActionStruct p s t) := by
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    (Subcomplex.unionProd.isPushout ∂Δ[n] (stdSimplex.face {(0 : Fin 2)})).exists_desc
      (fst _ _ ≫ s.map) (snd _ _ ≫ p.map) (by
        rw [whiskerRight_fst_assoc, s.comm, Subcomplex.ofSimplex_ι, comp_const, comp_const,
          whiskerLeft_snd_assoc, p.comm₀'', comp_const])
  obtain ⟨l, hl⟩ := anodyneExtensions.exists_lift_of_isFibrant φ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} ∂Δ[n] _
    (anodyneExtensions.face 0))
  refine ⟨{
    map := ι₁ ≫ l
    comm := by
      have := Subcomplex.unionProd.ι₂ _ _ ≫= hl
      rw [Subcomplex.unionProd.ι₂_ι_assoc, hφ₂] at this
      rw [Subcomplex.ofSimplex_ι, comp_const, ← ι₁_comp_assoc, this,
        ι₁_snd_assoc, const_comp, p.comm₁']
  }, ⟨{
      map := l
      ι₀_map := by
        have := Subcomplex.unionProd.ι₁ _ _ ≫= hl
        rw [hφ₁, ← cancel_epi (Δ[n] ◁ (stdSimplex.faceSingletonIso.{u} (0 : Fin 2)).hom),
          ← cancel_epi (stdSimplex.rightUnitor _).inv] at this
        exact this
      ι₁_map := rfl
      whiskerRight_ι_comp_map := by rw [← hφ₂, ← hl]; rfl
  }⟩⟩

noncomputable def uniqueActionStruct₁ {p : Edge x₀ x₁}
    {s : X.PtSimplex n x₀.pt} {t t' : X.PtSimplex n x₁.pt}
    (ht : ActionStruct p s t) (ht' : ActionStruct p s t') :
    t.Homotopy t' := by
  apply Nonempty.some
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    (horn₂₀.isPushout.{u}.map (tensorLeft Δ[n])).exists_desc ht.map ht'.map
      (by simp)
  dsimp at φ hφ₁ hφ₂
  obtain ⟨ψ, hψ₁, hψ₂⟩ :=
    (Subcomplex.unionProd.isPushout ∂Δ[n] (horn 2 0)).exists_desc φ
      (snd _ _ ≫ stdSimplex.σ 1 ≫ p.map) (by
        apply (horn₂₀.isPushout.{u}.map (tensorLeft (∂Δ[n] : SSet))).hom_ext
        · apply ((∂Δ[n].ι ▷ Δ[1]) ≫= hφ₁).trans
          have := stdSimplex.{u}.δ_comp_σ_succ (n := 1) (i := 1)
          dsimp at this ⊢
          rw [ht.whiskerRight_ι_comp_map, whiskerLeft_snd_assoc,
            whiskerLeft_snd_assoc, horn.ι_ι_assoc, reassoc_of% this]
        · apply ((∂Δ[n].ι ▷ Δ[1]) ≫= hφ₂).trans
          have := stdSimplex.{u}.δ_comp_σ_self (n := 1) (i := 1)
          dsimp at this ⊢
          rw [ht'.whiskerRight_ι_comp_map, whiskerLeft_snd_assoc,
            whiskerLeft_snd_assoc, horn.ι_ι_assoc, reassoc_of% this])
  obtain ⟨l, hl⟩ := anodyneExtensions.exists_lift_of_isFibrant ψ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} _ _
    (anodyneExtensions.horn_ι_mem 1 0))
  refine ⟨{
      h := _ ◁ stdSimplex.δ 0 ≫ l
      h₀ := by
        have eq₁ := (_ ◁ horn₂₀.ι₀₁ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= hl
        rw [Category.assoc, Category.assoc, Subcomplex.unionProd.ι₁_ι_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, horn.ι_ι] at eq₁
        have eq₂ := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 1) (by simp)
        dsimp at eq₂
        rw [← cancel_epi (stdSimplex.rightUnitor _).hom,
          stdSimplex.rightUnitor_hom_ι₀_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, ← eq₂,
          MonoidalCategory.whiskerLeft_comp_assoc, eq₁,
          hψ₁, hφ₁, ht.δ_zero_map]
      h₁ := by
        have eq₁ := (_ ◁ horn₂₀.ι₀₂ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= hl
        rw [Category.assoc, Category.assoc, Subcomplex.unionProd.ι₁_ι_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, horn.ι_ι] at eq₁
        have eq₂ := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 0) (by simp)
        dsimp at eq₂
        rw [← cancel_epi (stdSimplex.rightUnitor _).hom,
          stdSimplex.rightUnitor_hom_ι₁_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, ← eq₂,
          MonoidalCategory.whiskerLeft_comp_assoc, eq₁,
          hψ₁, hφ₂, ht'.δ_zero_map]
      rel := by
        have h₁ := (_ ◁ stdSimplex.δ 0 ≫ Subcomplex.unionProd.ι₂ _ _) ≫= hl
        rw [Category.assoc, Category.assoc, Subcomplex.unionProd.ι₂_ι_assoc,
          whisker_exchange_assoc, hψ₂] at h₁
        have h₂ := stdSimplex.{u}.δ_comp_σ_of_le (n := 0) (i := 0) (j := 0) (by rfl)
        dsimp at h₂
        rw [Subcomplex.ofSimplex_ι, comp_const, comp_const, h₁,
          whiskerLeft_snd_assoc, reassoc_of% h₂, p.comm₁, comp_const, comp_const]
  }⟩

noncomputable def compActionStruct {x₂ : FundamentalGroupoid X} {p₀₁ : Edge x₀ x₁}
    {p₁₂ : Edge x₁ x₂} {p₀₂ : Edge x₀ x₂} (hp : Edge.CompStruct p₀₁ p₁₂ p₀₂)
    {s₀ : X.PtSimplex n x₀.pt} {s₁ : X.PtSimplex n x₁.pt} {s₂ : X.PtSimplex n x₂.pt}
    (h₀₁ : ActionStruct p₀₁ s₀ s₁) (h₁₂ : ActionStruct p₁₂ s₁ s₂) :
    ActionStruct p₀₂ s₀ s₂ := by
  apply Nonempty.some
  obtain ⟨φ, hφ₁, hφ₂⟩ := (horn₂₁.isPushout.{u}.map (tensorLeft Δ[n])).exists_desc
    h₀₁.map h₁₂.map (by simp)
  dsimp at φ hφ₁ hφ₂
  obtain ⟨ψ, hψ₁, hψ₂⟩ := (Subcomplex.unionProd.isPushout ∂Δ[n] (horn 2 1)).exists_desc φ
    (snd _ _ ≫ hp.map) (by
      apply (horn₂₁.isPushout.{u}.map (tensorLeft (∂Δ[n] : SSet))).hom_ext
      · simp [whisker_exchange_assoc, hφ₁]
      · simp [whisker_exchange_assoc, hφ₂])
  obtain ⟨l, hl⟩ := anodyneExtensions.exists_lift_of_isFibrant ψ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} _ _
    (anodyneExtensions.horn_ι_mem 1 1))
  exact ⟨{
    map := _ ◁ stdSimplex.δ 1 ≫ l
    ι₀_map := by
      have := (_ ◁ horn₂₁.ι₀₁ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= hl
      rw [Category.assoc, Category.assoc, Subcomplex.unionProd.ι₁_ι_assoc,
        hψ₁, hφ₁] at this
      rw [← h₀₁.ι₀_map, ← this]
      rfl
    ι₁_map := by
      have := (_ ◁ horn₂₁.ι₁₂ ≫ Subcomplex.unionProd.ι₁ _ _) ≫= hl
      rw [Category.assoc, Category.assoc, Subcomplex.unionProd.ι₁_ι_assoc,
        hψ₁, hφ₂] at this
      rw [← h₁₂.ι₁_map, ← this]
      rfl
    whiskerRight_ι_comp_map := by
      have := Subcomplex.unionProd.ι₂ _ _ ≫= hl
      rw [Subcomplex.unionProd.ι₂_ι_assoc, hψ₂] at this
      rw [← whisker_exchange_assoc, this, whiskerLeft_snd_assoc, hp.h₀₂]
  }⟩

noncomputable def uniqueActionStruct₂ {p : Edge x₀ x₁}
    {s : X.PtSimplex n x₀.pt} {t t' : X.PtSimplex n x₁.pt}
    (ht : ActionStruct p s t) (h : t.Homotopy t') :
    ActionStruct p s t' :=
  compActionStruct.{u} (Edge.CompStruct.compId p) ht { map := h.h }

noncomputable def mulActionStruct'
    {s₁ s₂ s₁₂ : X.PtSimplex n x₀.pt} {i : Fin n}
    (h : PtSimplex.MulStruct s₁ s₂ s₁₂ i) {p : Edge x₀ x₁}
    {t₁ t₂ t₁₂ : X.PtSimplex n x₁.pt}
    (h₁ : ActionStruct p s₁ t₁) (h₂ : ActionStruct p s₂ t₂)
    (h₁₂ : ActionStruct p s₁₂ t₁₂) :
    PtSimplex.MulStruct t₁ t₂ t₁₂ i := by
  apply Nonempty.some
  obtain _ | n := n
  · fin_cases i
  let α (j : Fin (n + 3)) : Δ[n + 1] ⊗ Δ[1] ⟶ X :=
    if j = i.castSucc.castSucc then h₂.map
    else if j = i.succ.castSucc then h₁₂.map
      else if j = i.succ.succ then h₁.map
        else snd _ _ ≫ p.map
  have hα₂ : α i.castSucc.castSucc = h₂.map := if_pos rfl
  have hα₁₂ : α i.succ.castSucc = h₁₂.map := by
    dsimp only [α]
    rw [if_neg (fun h ↦ by simp [Fin.ext_iff] at h), if_pos rfl]
  have hα₁ : α i.succ.succ = h₁.map := by
    dsimp only [α]
    rw [if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega),
      if_neg (fun h ↦ by simp [Fin.ext_iff] at h), if_pos rfl]
  have hα_lt (j : Fin (n + 3)) (hj : j < i.castSucc.castSucc) :
      α j = snd _ _ ≫ p.map := by
    dsimp only [α]
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hj
    rw [if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega),
      if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega),
      if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega)]
  have hα_gt (j : Fin (n + 3)) (hj : i.succ.succ < j) :
      α j = snd _ _ ≫ p.map := by
    dsimp only [α]
    simp only [Fin.lt_iff_val_lt_val, Fin.val_succ] at hj
    rw [if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega),
      if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega),
      if_neg (fun h ↦ by simp [Fin.ext_iff] at h; omega)]
  have hα (j : Fin (n + 3)) : ∂Δ[n + 1].ι ▷ _ ≫ α j = snd _ _ ≫ p.map := by
    dsimp only [α]; split_ifs <;> simp
  have hα' (j : Fin (n + 3)) (k : Fin (n + 2)) :
      stdSimplex.δ k ▷ _ ≫ α j = snd _ _ ≫ p.map := by
    simpa using boundary.ι k ▷ _ ≫= hα j
  obtain ⟨φ, hφ⟩ := boundary.exists_tensorRight_desc α (fun j k hjk ↦ by simp [hα'])
  obtain ⟨ψ, hψ₁, hψ₂⟩ := (Subcomplex.unionProd.isPushout ∂Δ[n + 2]
    (stdSimplex.face {(0 : Fin 2)})).exists_desc (fst _ _ ≫ h.map) φ (by
    ext j : 1
    rw [whiskerRight_fst_assoc, whiskerRight_fst_assoc, boundary.ι_ι_assoc,
      ← cancel_epi (_ ◁ (stdSimplex.faceSingletonIso (0 : Fin 2)).hom),
      ← cancel_epi (stdSimplex.rightUnitor _).inv, whiskerLeft_fst_assoc,
      stdSimplex.rightUnitor_inv_fst_assoc,
      ← whisker_exchange_assoc, hφ, ← MonoidalCategory.whiskerLeft_comp_assoc,
      stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ,
      stdSimplex.rightUnitor_inv_map_δ_one_assoc]
    by_cases hj : j < i.castSucc.castSucc
    · rw [hα_lt j hj, h.δ_map_of_lt j hj, ι₀_snd_assoc, const_comp, p.comm₀']
    · simp only [not_lt] at hj
      obtain hj | rfl := hj.lt_or_eq; swap
      · rw [h.δ_castSucc_castSucc_map, hα₂, h₂.ι₀_map]
      · rw [Fin.castSucc_lt_iff_succ_le] at hj
        obtain hj | rfl := hj.lt_or_eq; swap
        · rw [h.δ_succ_castSucc_map, Fin.succ_castSucc, hα₁₂, h₁₂.ι₀_map]
        · rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj
          obtain hj | rfl := hj.lt_or_eq; swap
          · rw [h.δ_succ_succ_map, hα₁, h₁.ι₀_map]
          · rw [hα_gt j hj, h.δ_map_of_gt j hj, ι₀_snd_assoc, const_comp, p.comm₀'])
  obtain ⟨l, hl⟩ := anodyneExtensions.exists_lift_of_isFibrant ψ
    (anodyneExtensions.subcomplex_unionProd_mem_of_right.{u} ∂Δ[n + 2] _
      (anodyneExtensions.face 0))
  have δ_l (j : Fin (n + 3)) : stdSimplex.δ j ≫ ι₁ ≫ l = ι₁ ≫ α j := by
    have := (ι₁ ≫ boundary.ι j ▷ _ ≫ Subcomplex.unionProd.ι₂ _ _) ≫= hl
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, hψ₂, hφ,
      Subcomplex.unionProd.ι₂_ι_assoc, ι₁_comp_assoc, ι₁_comp_assoc, boundary.ι_ι_assoc] at this
    exact this
  refine ⟨{
    map := ι₁ ≫ l
    δ_castSucc_castSucc_map := by rw [δ_l, hα₂, h₂.ι₁_map]
    δ_castSucc_succ_map := by rw [δ_l, hα₁₂, h₁₂.ι₁_map]
    δ_succ_succ_map := by rw [δ_l, hα₁, h₁.ι₁_map]
    δ_map_of_lt j hj := by rw [δ_l, hα_lt j hj, ι₁_snd_assoc, const_comp, p.comm₁']
    δ_map_of_gt j hj := by rw [δ_l, hα_gt j hj, ι₁_snd_assoc, const_comp, p.comm₁']
  }⟩

noncomputable def mulActionStruct {s₁ s₂ s₁₂ : X.PtSimplex n x₀.pt} {i : Fin n}
    (h : PtSimplex.MulStruct s₁ s₂ s₁₂ i) {p : Edge x₀ x₁}
    {t₁ t₂ t₁₂ : X.PtSimplex n x₁.pt}
    (h₁ : ActionStruct p s₁ t₁) (h₂ : ActionStruct p s₂ t₂)
    (ht : PtSimplex.MulStruct t₁ t₂ t₁₂ i) :
    ActionStruct p s₁₂ t₁₂ := by
  apply Nonempty.some
  obtain _ | n := n
  · fin_cases i
  obtain ⟨t₁₂', ⟨h₁₂'⟩⟩ := exists_actionStruct p s₁₂
  exact ⟨uniqueActionStruct₂ h₁₂'
    ((PtSimplex.MulStruct.unique (mulActionStruct' h h₁ h₂ h₁₂') ht
      (.refl _) (.refl _)).homotopy)⟩

noncomputable def uniqueActionStruct {p p' : Edge x₀ x₁} (hp : p.Homotopy p')
    {s s' : X.PtSimplex n x₀.pt} (hs : s.Homotopy s')
    {t t' : X.PtSimplex n x₁.pt}
    (ht : ActionStruct p s t) (ht' : ActionStruct p' s' t') :
    t.Homotopy t' := by
  obtain _ | n := n
  · apply Nonempty.some
    obtain ⟨s, rfl⟩ := (PtSimplex.equiv₀ _).symm.surjective s
    obtain ⟨s', rfl⟩ := (PtSimplex.equiv₀ _).symm.surjective s'
    obtain ⟨t, rfl⟩ := (PtSimplex.equiv₀ _).symm.surjective t
    obtain ⟨t', rfl⟩ := (PtSimplex.equiv₀ _).symm.surjective t'
    exact ⟨(PtSimplex.Homotopy.equiv₀ _).symm
      ((((ActionStruct.equiv₀ _) ht).inv.comp
      ((PtSimplex.Homotopy.equiv₀ _) hs)).comp ((ActionStruct.equiv₀ _) ht'))⟩
  · replace ht := compActionStruct hp.homotopyL ht (.id t)
    replace ht : ActionStruct p' s' t :=
      mulActionStruct.{u}
        (PtSimplex.relStructCastSuccEquivMulStruct (i := 0) hs.relStruct₀) (
          { map := snd _ _ ≫ p'.map
            ι₀_map := by
              simp only [ι₀_snd_assoc, const_comp, Subcomplex.RelativeMorphism.const_map,
                p'.comm₀']
            ι₁_map := by
              simp only [ι₁_snd_assoc, const_comp, Subcomplex.RelativeMorphism.const_map,
                p'.comm₁'] }) ht
        (ht := PtSimplex.MulStruct.oneMul t 0)
    exact uniqueActionStruct₁ ht ht'

noncomputable def map' (p : Edge x₀ x₁)
    (s : X.PtSimplex n x₀.pt) : X.PtSimplex n x₁.pt :=
  (exists_actionStruct p s).choose

noncomputable def actionStruct (p : Edge x₀ x₁)
    (s : X.PtSimplex n x₀.pt) :
    ActionStruct p s (map' p s) :=
  (exists_actionStruct p s).choose_spec.some

noncomputable def map : ∀ (_p : x₀ ⟶ x₁), π n X x₀.pt → π n X x₁.pt :=
  Quot.lift₂ (fun p s ↦ (map' p s).homotopyClass) (by
    rintro (p : Edge _ _) s s' ⟨hs⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact uniqueActionStruct (.refl p) hs
      (actionStruct p s) (actionStruct p s')) (by
    rintro (p p' : Edge _ _) s ⟨hp⟩
    apply Subcomplex.RelativeMorphism.Homotopy.eq
    exact uniqueActionStruct hp (.refl s)
      (actionStruct p s) (actionStruct p' s))

lemma map_eq {p : Edge x₀ x₁}
    {s : X.PtSimplex n x₀.pt}
    {t : X.PtSimplex n x₁.pt}
    (h : ActionStruct p s t) :
    map (FundamentalGroupoid.homMk p) (π.mk s) = (π.mk t) := by
  apply Subcomplex.RelativeMorphism.Homotopy.eq
  exact uniqueActionStruct (.refl p) (.refl s) (actionStruct p s) h

variable (n) in
@[simp]
lemma map_id (x : FundamentalGroupoid X) :
    action.map (n := n) (𝟙 x) = id := by
  ext s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  exact map_eq (.id s)

@[simp]
lemma map_comp_apply {x₂ : FundamentalGroupoid X} (p : x₀ ⟶ x₁) (q : x₁ ⟶ x₂)
    (s : π n X x₀.pt) :
    action.map (p ≫ q) s = action.map q (action.map p s) := by
  obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
  obtain ⟨q, rfl⟩ := FundamentalGroupoid.homMk_surjective q
  obtain ⟨s, rfl⟩ := s.mk_surjective
  have pif := compActionStruct.{u} (hp := p.compStruct q)
    (h₀₁ := actionStruct p s) (h₁₂ := actionStruct q (map' p s))
  rw [(p.compStruct q).fac, map_eq (actionStruct p s),
    map_eq (compActionStruct (p.compStruct q) (actionStruct p s)
      (actionStruct q (map' p s))),
    map_eq (actionStruct _ _)]

lemma map_comp {x₂ : FundamentalGroupoid X} (p : x₀ ⟶ x₁) (q : x₁ ⟶ x₂) :
    action.map (n := n) (p ≫ q) =
      (action.map q).comp (action.map p) := by
  aesop

lemma map_mul (p : x₀ ⟶ x₁) (s t : π (n + 1) X x₀.pt) (i : Fin (n + 1)) :
    map p (π.mul i s t) = π.mul i (map p s) (map p t) := by
  obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
  obtain ⟨s, rfl⟩ := s.mk_surjective
  obtain ⟨t, rfl⟩ := t.mk_surjective
  rw [π.mul_eq_of_mulStruct (π.mulStruct s t i),
    map_eq (actionStruct p s), map_eq (actionStruct p t),
    π.mul_eq_of_mulStruct (π.mulStruct (map' p s) (map' p t) i)]
  exact map_eq (mulActionStruct (π.mulStruct s t i)
    (actionStruct p s) (actionStruct p t) (π.mulStruct (map' p s) (map' p t) i))

end action

@[simps]
noncomputable def action (X : SSet.{u}) [IsFibrant X] (n : ℕ) :
    FundamentalGroupoid X ⥤ Type u where
  obj x := π n X x.pt
  map {x y} p := action.map p

lemma action.bijective_map (n : ℕ) {X : SSet.{u}} {x y : FundamentalGroupoid X} [IsFibrant X]
    (p : x ⟶ y) :
    Function.Bijective (action.map (n := n) p) := by
  rw [← isIso_iff_bijective]
  exact inferInstanceAs (IsIso ((action X n).map p))

@[simps]
noncomputable def actionMap {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (n : ℕ) :
    action X n ⟶ mapFundamentalGroupoid f ⋙ action Y n where
  app x := mapπ f n x.pt _ rfl
  naturality x y p := by
    ext s
    obtain ⟨s, rfl⟩ := s.mk_surjective
    obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
    have h := action.actionStruct p s
    dsimp
    erw [action.map_eq h, mapπ_mk, action.map_eq (h.pushforward f)]
    rfl

end FundamentalGroupoid

end KanComplex

end SSet
