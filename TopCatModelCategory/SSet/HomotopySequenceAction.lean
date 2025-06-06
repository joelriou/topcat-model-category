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

/-def comp [IsFibrant B] {b₂ : B _⦋0⦌} {f₀₁ : Edge (.mk b₀) (.mk b₁)}
    {e₀ e₁ e₂ : E _⦋0⦌} (h₀₁ : FiberActionStruct p f₀₁ e₀ e₁)
    {f₁₂ : Edge (.mk b₁) (.mk b₂)}
    (h₁₂ : FiberActionStruct p f₁₂ e₁ e₂)
    {f₀₂ : Edge (.mk b₀) (.mk b₂)}
    (h : Edge.CompStruct f₀₁ f₁₂ f₀₂) :
    FiberActionStruct p f₀₂ e₀ e₂ := sorry

def symm [IsFibrant B] {e₀ e₁ : E _⦋0⦌} (h : FiberActionStruct p f e₀ e₁)
    {f' : Edge (.mk b₁) (.mk b₀)} (hff' : Edge.CompStruct f' f (.id (.mk b₁))) :
    FiberActionStruct p f' e₁ e₀ := sorry

noncomputable def unique
    [IsFibrant B] {e₀ e₀' e₁ e₁' : E _⦋0⦌} (h : FiberActionStruct p f e₀ e₁)
    {f' : Edge (.mk b₀) (.mk b₁)} (h' : FiberActionStruct p f' e₀' e₁')
    (hff' : f.Homotopy f')
    (he : FiberActionStruct p (.id (.mk b₀)) e₀ e₀') :
    FiberActionStruct p (.id (.mk b₁)) e₁ e₁' :=
  Nonempty.some (by
    obtain ⟨g, ⟨hg⟩⟩ := Edge.CompStruct.left_inverse f
    exact ⟨comp (comp (h.symm hg) he (Edge.CompStruct.compId g))
      h' (hg.assoc' hff'.homotopyL (.idComp _))⟩)-/

end FiberActionStruct

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
