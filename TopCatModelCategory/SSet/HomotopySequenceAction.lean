import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

universe u

open CategoryTheory SSet.modelCategoryQuillen HomotopicalAlgebra
  Simplicial Opposite

namespace SSet

namespace KanComplex.FundamentalGroupoid

variable {E B : SSet.{u}} (p : E ⟶ B)
  {b₀ b₁ : B _⦋0⦌} (f : Edge (.mk b₀) (.mk b₁))

structure FiberActionStruct (e₀ e₁ : E _⦋0⦌) where
  map : Δ[1] ⟶ E
  map_p : map ≫ p = f.map := by aesop_cat
  δ₁_map : stdSimplex.δ 1 ≫ map = const e₀ := by aesop_cat
  δ₀_map : stdSimplex.δ 0 ≫ map = const e₁ := by aesop_cat

namespace FiberActionStruct

attribute [reassoc (attr := simp)] map_p δ₁_map δ₀_map

section

variable {p f} {e₀ e₁ : E _⦋0⦌} (h : FiberActionStruct p f e₀ e₁)

include h in
lemma app_zero : p.app _ e₀ = b₀ := by
  have := h.δ₁_map =≫ p
  rw [Category.assoc, map_p, const_comp] at this
  apply yonedaEquiv.symm.injective
  simp only [yonedaEquiv_symm_zero, ← this, f.comm₀]

include h in
lemma app_one : p.app _ e₁ = b₁ := by
  have := h.δ₀_map =≫ p
  rw [Category.assoc, map_p, const_comp] at this
  apply yonedaEquiv.symm.injective
  simp only [yonedaEquiv_symm_zero, ← this, f.comm₁]

end

@[simps]
protected def const {e₀ : E _⦋0⦌} (h₀ : p.app _ e₀ = b₀) :
    FiberActionStruct p (.id (.mk b₀)) e₀ e₀ where
  map := SSet.const e₀
  map_p := by simp [h₀]
  δ₀_map := by simp
  δ₁_map := by simp

def ofEdge {b₀ : B _⦋0⦌} {e₀ e₁ : (Subcomplex.fiber p b₀ : SSet) _⦋0⦌}
    (e : Edge (.mk e₀) (.mk e₁)) :
    FiberActionStruct p (.id (.mk b₀)) e₀ e₁ := by
  obtain ⟨e₀, he₀⟩ := e₀
  obtain ⟨e₁, he₁⟩ := e₁
  simp only [Subcomplex.mem_fiber_obj_zero_iff] at he₀ he₁
  refine {
    map := e.map ≫ Subcomplex.ι _
    map_p := by
      simp
    δ₀_map := by simp [e.comm₁_assoc]
    δ₁_map := by simp [e.comm₀_assoc]
  }

noncomputable def ofπ₀Rel {b₀ : B _⦋0⦌} {e₀ e₁ : (Subcomplex.fiber p b₀ : SSet) _⦋0⦌}
    (h : π₀Rel e₀ e₁) :
    FiberActionStruct p (.id (.mk b₀)) e₀ e₁ := Nonempty.some (by
  obtain ⟨c, hc₀, hc₁⟩ := h
  refine ⟨ofEdge _ (Edge.mk (yonedaEquiv.symm c) ?_ ?_)⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, hc₀, yonedaEquiv_symm_eq_const]
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, hc₁, yonedaEquiv_symm_eq_const])

section

variable {p} {e₀ e₁ : E _⦋0⦌} (h : FiberActionStruct p (.id (.mk b₀)) e₀ e₁)

def toFibreOneSimplex : (Subcomplex.fiber p b₀ : SSet) _⦋1⦌ :=
  yonedaEquiv (Subcomplex.lift h.map (by simp))

@[simp]
lemma δ_one_toFibreOneSimplex :
    (Subcomplex.fiber p b₀ : SSet).δ 1 h.toFibreOneSimplex = ⟨e₀, by simp [h.app_zero]⟩ := by
  dsimp
  ext
  change E.map (SimplexCategory.δ 1).op (yonedaEquiv h.map) = e₀
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_symm_map, Equiv.symm_apply_apply, yonedaEquiv_symm_zero]
  exact h.δ₁_map

@[simp]
lemma δ_zero_toFibreOneSimplex :
    (Subcomplex.fiber p b₀ : SSet).δ 0 h.toFibreOneSimplex = ⟨e₁, by simp [h.app_one]⟩ := by
  dsimp
  ext
  change E.map (SimplexCategory.δ 0).op (yonedaEquiv h.map) = e₁
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_symm_map, Equiv.symm_apply_apply, yonedaEquiv_symm_zero]
  exact h.δ₀_map

end

variable [Fibration p]

lemma nonempty (e₀ : E _⦋0⦌) (h₀ : p.app _ e₀ = b₀) :
    ∃ (e₁ : E _⦋0⦌), Nonempty (FiberActionStruct p f e₀ e₁) := by
  have := (anodyneExtensions.δ_mem 1).hasLeftLiftingProperty p
  have sq : CommSq (const e₀) (stdSimplex.δ 1) p f.map := ⟨by simp [f.comm₀, h₀]⟩
  exact ⟨yonedaEquiv (stdSimplex.δ 0 ≫ sq.lift), ⟨{
    map := sq.lift
    δ₀_map := yonedaEquiv.injective (by simp)
  }⟩⟩

lemma nonempty' (e₁ : E _⦋0⦌) (h₁ : p.app _ e₁ = b₁) :
    ∃ (e₀ : E _⦋0⦌), Nonempty (FiberActionStruct p f e₀ e₁) := by
  have := (anodyneExtensions.δ_mem 0).hasLeftLiftingProperty p
  have sq : CommSq (const e₁) (stdSimplex.δ 0) p f.map := ⟨by simp [f.comm₁, h₁]⟩
  exact ⟨yonedaEquiv (stdSimplex.δ 1 ≫ sq.lift), ⟨{
    map := sq.lift
    δ₁_map := yonedaEquiv.injective (by simp)
  }⟩⟩

variable {p f}

noncomputable def comp {b₂ : B _⦋0⦌} {f₀₁ : Edge (.mk b₀) (.mk b₁)}
    {e₀ e₁ e₂ : E _⦋0⦌} (h₀₁ : FiberActionStruct p f₀₁ e₀ e₁)
    {f₁₂ : Edge (.mk b₁) (.mk b₂)}
    (h₁₂ : FiberActionStruct p f₁₂ e₁ e₂)
    {f₀₂ : Edge (.mk b₀) (.mk b₂)}
    (h : Edge.CompStruct f₀₁ f₁₂ f₀₂) :
    FiberActionStruct p f₀₂ e₀ e₂ := Nonempty.some (by
  obtain ⟨φ, hφ₁, hφ₂⟩ := horn₂₁.isPushout.exists_desc h₀₁.map h₁₂.map (by simp)
  have sq : CommSq φ Λ[2,1].ι p h.map := ⟨by
    apply horn₂₁.isPushout.hom_ext
    · simp [reassoc_of% hφ₁]
    · simp [reassoc_of% hφ₂]⟩
  exact ⟨{
    map := stdSimplex.δ 1 ≫ sq.lift
    δ₀_map := by
      have h₁ := stdSimplex.{u}.δ_comp_δ_self (n := 0) (i := 0)
      dsimp at h₁
      have h₂ := horn₂₁.ι₁₂ ≫= sq.fac_left
      rw [horn.ι_ι_assoc, hφ₂] at h₂
      rw [← reassoc_of% h₁, h₂, δ₀_map]
    δ₁_map := by
      have h₁ := stdSimplex.{u}.δ_comp_δ_self (n := 0) (i := 1)
      dsimp at h₁
      have h₂ := horn₂₁.ι₀₁ ≫= sq.fac_left
      rw [horn.ι_ι_assoc, hφ₁] at h₂
      rw [reassoc_of% h₁, h₂, δ₁_map]
  }⟩)

noncomputable def symm {e₀ e₁ : E _⦋0⦌} (h : FiberActionStruct p f e₀ e₁)
    {f' : Edge (.mk b₁) (.mk b₀)} (hff' : Edge.CompStruct f' f (.id (.mk b₁))) :
    FiberActionStruct p f' e₁ e₀ := Nonempty.some (by
  obtain ⟨φ, hφ₁, hφ₂⟩ := horn₂₂.isPushout.exists_desc (const e₁) h.map (by simp)
  have sq : CommSq φ Λ[2,2].ι p hff'.map := ⟨by
    apply horn₂₂.isPushout.hom_ext
    · simp [reassoc_of% hφ₁, h.app_one]
    · simp [reassoc_of% hφ₂]⟩
  exact ⟨{
    map := stdSimplex.δ 2 ≫ sq.lift
    δ₀_map := by
      have h₁ := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 1) (by simp)
      dsimp at h₁
      have h₂ := horn₂₂.ι₁₂ ≫= sq.fac_left
      rw [horn.ι_ι_assoc] at h₂
      rw [reassoc_of% h₁, h₂, hφ₂, δ₁_map]
    δ₁_map := by
      have h₁ := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 1) (j := 1) (by simp)
      dsimp at h₁
      have h₂ := horn₂₂.ι₀₂ ≫= sq.fac_left
      rw [horn.ι_ι_assoc] at h₂
      rw [reassoc_of% h₁, h₂, hφ₁, comp_const]
  }⟩)

noncomputable def unique
    [IsFibrant B] {e₀ e₀' e₁ e₁' : E _⦋0⦌} (h : FiberActionStruct p f e₀ e₁)
    {f' : Edge (.mk b₀) (.mk b₁)} (h' : FiberActionStruct p f' e₀' e₁')
    (hff' : f.Homotopy f')
    (he : FiberActionStruct p (.id (.mk b₀)) e₀ e₀') :
    FiberActionStruct p (.id (.mk b₁)) e₁ e₁' :=
  Nonempty.some (by
    obtain ⟨g, ⟨hg⟩⟩ := Edge.CompStruct.left_inverse f
    exact ⟨comp (comp (h.symm hg) he (Edge.CompStruct.compId g))
      h' (hg.assoc' hff'.homotopyL (.idComp _))⟩)

end FiberActionStruct

section

variable [Fibration p]

noncomputable def fiberAction (e₀ : E _⦋0⦌) (h₀ : p.app _ e₀ = b₀) : E _⦋0⦌ :=
  (FiberActionStruct.nonempty p f e₀ h₀).choose

noncomputable def fiberActionStruct (e₀ : E _⦋0⦌) (h₀ : p.app _ e₀ = b₀) :
    FiberActionStruct p f e₀ (fiberAction p f e₀ h₀) :=
  (FiberActionStruct.nonempty p f e₀ h₀).choose_spec.some

variable [IsFibrant B]

noncomputable def π₀FiberAction {b₀ b₁ : FundamentalGroupoid B} :
    (b₀ ⟶ b₁) → π₀ (Subcomplex.fiber p b₀.pt) → π₀ (Subcomplex.fiber p b₁.pt) :=
  Quot.lift₂
    (fun q e₀ ↦ π₀.mk ⟨fiberAction p q e₀
      (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2), by
        simpa only [Subcomplex.mem_fiber_obj_zero_iff] using
          (fiberActionStruct p q e₀ _).app_one⟩)
    (fun q e₀ e₀' c ↦
      π₀.sound (FiberActionStruct.unique
        (fiberActionStruct p q e₀
          (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2))
        (fiberActionStruct p q e₀'
          (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀'.2))
        (.refl q) (.ofπ₀Rel p c)).toFibreOneSimplex (by simp) (by simp))
    (fun q q' e₀ ⟨h⟩ ↦
      π₀.sound (FiberActionStruct.unique
        (fiberActionStruct p q e₀
          (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2))
        (fiberActionStruct p q' e₀
          (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2))
        h (.const p
          (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2))).toFibreOneSimplex
        (by simp) (by simp))

variable {p} in
lemma FiberActionStruct.π₀FiberAction_eq
    {b₀ b₁ : FundamentalGroupoid B} {f : b₀.Edge b₁}
    {e₀ e₁ : E _⦋0⦌}
    (h : FiberActionStruct p f e₀ e₁) :
    π₀FiberAction p (FundamentalGroupoid.homMk f) (π₀.mk ⟨e₀, by
      simp only [Subcomplex.mem_fiber_obj_zero_iff, h.app_zero]⟩) =
    π₀.mk (X := Subcomplex.fiber p b₁.pt) ⟨e₁, by
      simp only [Subcomplex.mem_fiber_obj_zero_iff, h.app_one]⟩ :=
  π₀.sound
    (FiberActionStruct.unique (fiberActionStruct p f e₀ h.app_zero) h (.refl _)
        (.const _ h.app_zero)).toFibreOneSimplex
      (by simp) (by simp)

lemma π₀FiberAction_mk_eq_iff
    {b₀ b₁ : FundamentalGroupoid B} (f : b₀.Edge b₁)
    (e₀ : (Subcomplex.fiber p b₀.pt : SSet) _⦋0⦌)
    (e₁ : (Subcomplex.fiber p b₁.pt : SSet) _⦋0⦌) :
    π₀FiberAction p (FundamentalGroupoid.homMk f) (π₀.mk e₀) = π₀.mk e₁ ↔
      Nonempty (FiberActionStruct p f e₀ e₁) := by
  constructor
  · intro h
    change π₀.mk _ = _ at h
    rw [KanComplex.π₀_mk_eq_π₀_mk_iff] at h
    obtain ⟨h⟩ := h
    exact ⟨FiberActionStruct.comp (fiberActionStruct p f e₀
      (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2))
      (FiberActionStruct.ofEdge p h) (.compId _)⟩
  · rintro ⟨h⟩
    exact h.π₀FiberAction_eq

lemma π₀FiberAction_id (b₀ : FundamentalGroupoid B)
    (s : π₀ (Subcomplex.fiber p b₀.pt)) :
    π₀FiberAction p (𝟙 b₀) s = s := by
  obtain ⟨e₀, rfl⟩ := s.mk_surjective
  apply FiberActionStruct.π₀FiberAction_eq
  exact .const _ (by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e₀.2)

lemma π₀FiberAction_comp {b₀ b₁ b₂ : FundamentalGroupoid B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (s : π₀ (Subcomplex.fiber p b₀.pt)) :
    π₀FiberAction p (f ≫ g) s = π₀FiberAction p g (π₀FiberAction p f s) := by
  obtain ⟨⟨e₀, he₀⟩, rfl⟩ := s.mk_surjective
  obtain ⟨f₀₁, rfl⟩ := homMk_surjective f
  obtain ⟨f₁₂, rfl⟩ := homMk_surjective g
  obtain ⟨f₀₂, ⟨h⟩⟩ := Edge.exists_compStruct f₀₁ f₁₂
  obtain ⟨e₁, ⟨h₀₁⟩⟩ := FiberActionStruct.nonempty p f₀₁ e₀ (by simpa using he₀)
  obtain ⟨e₂, ⟨h₁₂⟩⟩ := FiberActionStruct.nonempty p f₁₂ e₁ (h₀₁.app_one)
  rw [h₀₁.π₀FiberAction_eq, h₁₂.π₀FiberAction_eq, h.fac, (h₀₁.comp h₁₂ h).π₀FiberAction_eq]

end

end KanComplex.FundamentalGroupoid

namespace Subcomplex

open KanComplex.FundamentalGroupoid

lemma neq_bot_iff {X : SSet.{u}} (A : X.Subcomplex) :
    A ≠ ⊥ ↔ (A.obj (op ⦋0⦌)).Nonempty := by
  constructor
  · rintro h
    by_contra! h'
    refine h (le_antisymm ?_ (by simp))
    rintro ⟨n⟩ a ha
    simpa [h'] using A.map (SimplexCategory.const ⦋0⦌ n 0).op ha
  · rintro h rfl
    simp at h

lemma fiber_neq_bot_iff_of_edge {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] {b₀ b₁ : B _⦋0⦌}
    (edge : Edge (.mk b₀) (.mk b₁)) :
    (fiber p b₀ ≠ ⊥) ↔ (fiber p b₁ ≠ ⊥) := by
  simp only [neq_bot_iff]
  constructor
  · rintro ⟨e₀, he₀⟩
    simp only [mem_fiber_obj_zero_iff] at he₀
    obtain ⟨e₁, ⟨h⟩⟩ := FiberActionStruct.nonempty p edge e₀ he₀
    exact ⟨e₁, by simp only [mem_fiber_obj_zero_iff, h.app_one]⟩
  · rintro ⟨e₁, he₁⟩
    simp only [mem_fiber_obj_zero_iff] at he₁
    obtain ⟨e₀, ⟨h⟩⟩ := FiberActionStruct.nonempty' p edge e₁ he₁
    exact ⟨e₀, by simp only [mem_fiber_obj_zero_iff, h.app_zero]⟩

end Subcomplex

end SSet
