import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Comma.Over.Pullback

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type t} [Category.{w} C] [HasPullbacks C]

section

variable {S' S : C} {p : S' ⟶ S} {X : Over S} {X' : C} {t : X' ⟶ X.left} {l : X' ⟶ S'}
  (sq : IsPullback t l X.hom p)

@[simps!]
noncomputable def pullbackObjIsoOfIsPullback :
    Over.mk l ≅ (Over.pullback p).obj X :=
  Over.isoMk sq.isoPullback

end

section

variable {X S X' S' : C} {f : X ⟶ S} {f' : X' ⟶ S'}
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

end

section

variable {E' E B' B : C} {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
  (sq : IsPullback t l r b)

noncomputable def pullbackCompForgetOfIsPullback :
    Over.pullback l ⋙ Over.forget _ ≅
      Over.map b ⋙ Over.pullback r ⋙ Over.forget _ :=
  NatIso.ofComponents (fun Z ↦
    ((IsPullback.of_hasPullback Z.hom l).paste_vert sq.flip).isoPullback)

end

lemma isPullback_map_left {B' B : C} (b : B' ⟶ B) {X Y : Over B} (f : X ⟶ Y) :
    IsPullback ((Over.pullback b).map f).left (pullback.fst _ _) (pullback.fst _ _) f.left :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback X.hom b).flip)
    (by simp) (IsPullback.of_hasPullback Y.hom b).flip

end Over

end CategoryTheory
