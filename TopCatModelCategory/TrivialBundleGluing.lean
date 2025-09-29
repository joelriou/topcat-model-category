import TopCatModelCategory.TrivialBundle
import TopCatModelCategory.MorphismPropertyLocally
import TopCatModelCategory.CommSq
import TopCatModelCategory.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory

open MorphismProperty MonoidalCategory
  CartesianMonoidalCategory Limits

variable {C : Type*} [Category C]

namespace MorphismProperty

namespace TrivialBundleWithFiber

section

variable {F Y Y' X X' : C} {f : Y ⟶ X} (hf : TrivialBundleWithFiber F f)
  {f' : Y' ⟶ X'} (hf' : TrivialBundleWithFiber F f')
  {t : Y' ⟶ Y} {b : X' ⟶ X} (sq : IsPullback t f' f b)

include hf in
lemma exists_of_splitMono [IsSplitMono b] :
    ∃ (h : TrivialBundleWithFiber F f), h.pullback sq = hf' := by
  obtain ⟨u, h₁, h₂, h₃⟩ : ∃ (u : Y ⟶ Y'), u ≫ t ≫ hf.r = hf.r ∧
      u ≫ t ≫ f = f ≫ retraction b ≫ b ∧ u ≫ f' = f ≫ retraction b := by
    obtain ⟨φ, h₁, h₂⟩ :=
      BinaryFan.IsLimit.exists_lift hf.isLimit (f ≫ retraction b ≫ b) hf.r
    dsimp at φ h₁ h₂
    obtain ⟨u, rfl, h₄⟩ := sq.exists_lift φ (f ≫ retraction b) (by simpa)
    simp only [Category.assoc] at h₁ h₂
    exact ⟨u, h₂, h₁, h₄⟩
  have sq' : IsPullback (u ≫ t) f f (retraction b ≫ b) :=
    hf.isPullback hf _ _ (by simpa) (by simpa)
  have sq'' : IsPullback u f f' (retraction b) := IsPullback.of_right sq' h₃ sq
  have htut : t ≫ u ≫ t = t := by
    apply BinaryFan.IsLimit.hom_ext hf.isLimit <;> dsimp
    · rw [Category.assoc, Category.assoc, h₂, ← sq''.w_assoc, reassoc_of% h₃,
        sq.w_assoc, IsSplitMono.id_assoc, sq.w]
    · rw [Category.assoc, Category.assoc, h₁]
  have htu : t ≫ u = 𝟙 Y' := by
    apply sq.hom_ext
    · simpa
    · dsimp
      rw [Category.id_comp, Category.assoc, ← cancel_mono b,
        Category.assoc, Category.assoc, ← sq.w, reassoc_of% htut]
  refine ⟨hf'.pullback sq'', ?_⟩
  ext
  simp [reassoc_of% htu]

end

section

variable {F Y X : C} {f : Y ⟶ X} (hf : TrivialBundleWithFiber F f)

section

variable {c : BinaryFan X F} (hc : IsLimit c)

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
  [PreservesColimit (span t l) (tensorRight F)]

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
  refine ⟨⟨f, IsLimit.ofIsoLimit (tensorProductIsBinaryProduct X₄ F)
      ((Fan.ext e₄ ?_).symm)⟩,
    by ext; assumption, by ext; assumption⟩
  rintro (_ | _)
  · apply sq'.hom_ext <;> dsimp [Fan.proj]
    · simpa [reassoc_of% comm₁] using sq₂₄.w
    · simpa [reassoc_of% comm₂] using sq₃₄.w
  · apply sq'.hom_ext <;> dsimp [Fan.proj]
    · simpa [reassoc_of% comm₁]
    · simpa [reassoc_of% comm₂]

include sq sq' sq₁₂ sq₁₃ sq₃₄ h₃ in
lemma exists_gluing_of_isSplitMono [IsSplitMono l] :
    ∃ (h₄ : TrivialBundleWithFiber F p₄),
      h₄.pullback sq₂₄ = h₂ := by
  obtain ⟨h₃', h⟩ := h₃.exists_of_splitMono (h₂.pullback sq₁₂) sq₁₃
  obtain ⟨h₄, eq, _⟩ := exists_gluing sq sq' sq₁₂ sq₂₄ sq₁₃ sq₃₄ h₂ h₃' h.symm
  exact ⟨h₄, eq⟩

end TrivialBundleWithFiber

namespace TrivialBundleWithFiberOver

lemma nonempty_of_isPushout_of_isSplitMono [HasPullbacks C]
    [CartesianMonoidalCategory C] {B : C} {X₁ X₂ X₃ X₄ : CategoryTheory.Over B}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) [IsSplitMono l.left]
    {E : C} (p : E ⟶ B) {F : C}
    (h₂ : TrivialBundleWithFiberOver F p X₂.hom)
    (h₃ : TrivialBundleWithFiberOver F p X₃.hom)
    [PreservesColimit (span t.left l.left) (tensorRight F)]
    [PreservesColimit (span t l) (CategoryTheory.Over.pullback p)] :
    Nonempty (TrivialBundleWithFiberOver F p X₄.hom) := by
  have : PreservesColimit (span ((Over.forget B).map t)
      ((Over.forget B).map l)) (tensorRight F) := by
    assumption
  have : IsSplitMono ((Over.forget B).map l) := by assumption
  obtain ⟨h₄, _⟩ := TrivialBundleWithFiber.exists_gluing_of_isSplitMono
    (sq.map (Over.forget _)) (sq.map (CategoryTheory.Over.pullback p ⋙ Over.forget _))
    (Over.isPullback_map_left p _) (Over.isPullback_map_left p _)
    (Over.isPullback_map_left p _) (Over.isPullback_map_left p _)
    (h₂.trivialBundleWithFiber (IsPullback.of_hasPullback _ _).flip)
    (h₃.trivialBundleWithFiber (IsPullback.of_hasPullback _ _).flip)
  exact ⟨{
    sq := (IsPullback.of_hasPullback _ _).flip
    h := h₄
  }⟩

end TrivialBundleWithFiberOver

end MorphismProperty


end CategoryTheory
