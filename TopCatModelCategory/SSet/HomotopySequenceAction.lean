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
