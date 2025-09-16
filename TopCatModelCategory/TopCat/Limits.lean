import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits

namespace TopCat

lemma isPullbackRestrictPreimage {E B : TopCat.{u}} (p : E ⟶ B) (U : Set B) :
    IsPullback (ofHom ⟨_, continuous_subtype_val⟩) (ofHom (p.hom.restrictPreimage U)) p
      (ofHom ⟨_, continuous_subtype_val⟩) where
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ ofHom ⟨fun x ↦ ⟨s.fst x, by
      simp only [Set.mem_preimage]
      have := ConcreteCategory.congr_hom s.condition x
      convert (s.snd x).2⟩, by continuity⟩)
    (fun s ↦ rfl)
    (fun s ↦ by
      ext x
      exact ConcreteCategory.congr_hom s.condition x)
    (fun s m hm₁ hm₂ ↦ by
      ext x
      exact ConcreteCategory.congr_hom hm₁ x)⟩

end TopCat
