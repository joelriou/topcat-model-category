import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Comma.Over.Pullback

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type t} [Category.{w} C] [HasPullbacks C]
    {X S X' S' : C} {f : X ⟶ S} {f' : X' ⟶ S'}
    (e : Arrow.mk f ≅ Arrow.mk f')

instance [IsIso f] : (Over.pullback f).IsEquivalence :=
  (Equivalence.mk (Over.pullback f) (Over.pullback (inv f))
    (pullbackId.symm ≪≫ eqToIso (by simp) ≪≫ pullbackComp (inv f) f)
    ((pullbackComp f (inv f)).symm ≪≫ eqToIso (by simp) ≪≫ pullbackId)).isEquivalence_functor

noncomputable def pullbackIsoOfArrowIso :
    Over.pullback f' ≅ Over.pullback e.hom.right ⋙ Over.pullback f ⋙
      Over.pullback e.inv.left :=
  eqToIso (by simp) ≪≫ pullbackComp _ _ ≪≫ Functor.isoWhiskerLeft _ (pullbackComp _ _)

variable {D : Type t'} [Category.{w'} D] (F : C ⥤ D) {S T : C} (f : S ⟶ T)
  [HasPullbacks D] [∀ {A : C} (g : A ⟶ T), PreservesLimit (cospan g f) F]

noncomputable def pullbackPostIso :
    Over.pullback f ⋙ Over.post F ≅ Over.post F ⋙ Over.pullback (F.map f) :=
  NatIso.ofComponents (fun Z ↦  isoMk (asIso (pullbackComparison _ _ _)))

end Over

end CategoryTheory
