import TopCatModelCategory.TrivialBundle
import TopCatModelCategory.CommSq
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory

open MorphismProperty MonoidalCategory
  CartesianMonoidalCategory

variable {C : Type*} [Category C]

namespace MorphismProperty.TrivialBundleWithFiber

section

variable {F Y Y' X X' : C} {f : Y ⟶ X} (hf : TrivialBundleWithFiber F f)
  {f' : Y' ⟶ X'} (hf' : TrivialBundleWithFiber F f')
  {t : Y' ⟶ Y} {b : X' ⟶ X} (sq : IsPullback t f' f b)

include hf in
lemma exists_of_splitMono (hb : SplitMono b) :
    ∃ (h : TrivialBundleWithFiber F f), h.pullback sq = hf' := by
  obtain ⟨u, hu₁, hu₂⟩ :
      ∃ (u : Y ⟶ Y'), u ≫ f' = f ≫ hb.retraction ∧ u ≫ hf'.r = hf.r := by
    have := Limits.BinaryFan.IsLimit.lift' hf'.isLimit (f ≫ hb.retraction) hf.r
    aesop
  have squ : IsPullback u f f' hb.retraction :=
    { isLimit' := ⟨sorry⟩ }
  exact ⟨hf'.pullback squ, sorry⟩

end

section

variable {F Y X : C} {f : Y ⟶ X} (hf : TrivialBundleWithFiber F f)

section

variable {c : Limits.BinaryFan X F} (hc : Limits.IsLimit c)

def isoOfIsLimit : Y ≅ c.pt := hf.isLimit.conePointUniqueUpToIso hc

@[reassoc (attr := simp)]
lemma isoOfIsLimit_hom_fst : (hf.isoOfIsLimit hc).hom ≫ c.fst = f :=
  hf.isLimit.conePointUniqueUpToIso_hom_comp hc ⟨.left⟩

@[reassoc (attr := simp)]
lemma isoOfIsLimit_hom_snd : (hf.isoOfIsLimit hc).hom ≫ c.snd = hf.r :=
  hf.isLimit.conePointUniqueUpToIso_hom_comp hc ⟨.right⟩

end

section

variable [CartesianMonoidalCategory C]

def isoTensor : Y ≅ X ⊗ F := hf.isoOfIsLimit (tensorProductIsBinaryProduct _ _)

@[reassoc (attr := simp)]
lemma isoTensor_hom_fst : hf.isoTensor.hom ≫ fst _ _ = f :=
  isoOfIsLimit_hom_fst _ _

@[reassoc (attr := simp)]
lemma isoTensor_hom_snd : hf.isoTensor.hom ≫ snd _ _ = hf.r :=
  isoOfIsLimit_hom_snd _ _

end

end

variable [CartesianMonoidalCategory C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ F : C}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
  {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
  (sq : IsPushout t l r b) (sq' : IsPushout t' l' r' b')
  {p₁ : Y₁ ⟶ X₁} {p₂ : Y₂ ⟶ X₂} {p₃ : Y₃ ⟶ X₃} {p₄ : Y₄ ⟶ X₄}
  (sq₁₂ : IsPullback t' p₁ p₂ t) (sq₂₄ : IsPullback r' p₂ p₄ r)
  (sq₁₃ : IsPullback l' p₁ p₃ l) (sq₃₄ : IsPullback b' p₃ p₄ b)
  (h₂ : TrivialBundleWithFiber F p₂) (h₃ : TrivialBundleWithFiber F p₃)
  [Limits.PreservesColimit (Limits.span t l) (tensorRight F)]

include sq sq' in
lemma exists_gluing (h₁ : h₂.pullback sq₁₂ = h₃.pullback sq₁₃) :
    ∃ (h₄ : TrivialBundleWithFiber F p₄),
      h₄.pullback sq₂₄ = h₂ ∧ h₄.pullback sq₃₄ = h₃ := by
  simp only [ext_iff, pullback_r] at h₁
  obtain ⟨f, hf₂, hf₃⟩ := sq'.exists_desc h₂.r h₃.r h₁
  obtain ⟨e₄, comm₁, comm₂⟩ :=
    IsPushout.exists_iso_of_isos sq' (sq.map (tensorRight F))
      (h₂.pullback sq₁₂).isoTensor h₂.isoTensor h₃.isoTensor
        (by dsimp; ext <;> simp [sq₁₂.w])
        (by dsimp; ext <;> simp [sq₁₃.w, h₁])
  refine ⟨⟨f, Limits.IsLimit.ofIsoLimit (tensorProductIsBinaryProduct X₄ F)
      ((Limits.Fan.ext e₄ ?_).symm)⟩,
    by ext; assumption, by ext; assumption⟩
  rintro (_ | _)
  · apply sq'.hom_ext <;> dsimp [Limits.Fan.proj]
    · simpa [reassoc_of% comm₁] using sq₂₄.w
    · simpa [reassoc_of% comm₂] using sq₃₄.w
  · apply sq'.hom_ext <;> dsimp [Limits.Fan.proj]
    · simpa [reassoc_of% comm₁]
    · simpa [reassoc_of% comm₂]

end MorphismProperty.TrivialBundleWithFiber

end CategoryTheory
