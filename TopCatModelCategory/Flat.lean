import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.LeftKanExtensionAlongUliftYoneda

universe w w' v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Presheaf

variable {F : C ⥤ Type max w w'} (G : (Cᵒᵖ ⥤ Type max w v) ⥤ Type max w w')
  (τ : F ⟶ uliftYoneda.{w} ⋙ G) [IsCofiltered F.Elements]

end Presheaf

end CategoryTheory
