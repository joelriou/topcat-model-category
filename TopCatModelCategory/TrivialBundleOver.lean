import TopCatModelCategory.TrivialBundle
import TopCatModelCategory.CommSq

namespace CategoryTheory

variable {C : Type*} [Category C]
open Limits

namespace MorphismProperty

variable (F : C) {E B B' : C} (p : E ⟶ B) (f : B' ⟶ B)

structure TrivialBundleWithFiberOver where
  {E' : C}
  {p' : E' ⟶ B'}
  {t : E' ⟶ E}
  sq : IsPullback t p' p f
  h : TrivialBundleWithFiber F p'

namespace TrivialBundleWithFiberOver

variable {F p f} (hp : TrivialBundleWithFiberOver F p f)

include hp in
lemma hasPullback : HasPullback p f := hp.sq.hasPullback

noncomputable def trivialBundleWithFiber {E'' : C} {p'' : E'' ⟶ B'} {t'' : E'' ⟶ E}
    (sq'' : IsPullback t'' p'' p f) :
    TrivialBundleWithFiber F p'' :=
  hp.h.ofIso (IsPullback.isoOfIsos sq'' hp.sq (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)) (by simp)

def id (h : TrivialBundleWithFiber F p) :
    TrivialBundleWithFiberOver F p (𝟙 B) :=
  .mk IsPullback.of_id_fst h


end TrivialBundleWithFiberOver

lemma nonempty_trivialBundleWithFiberOver_iff_of_isPullback
    {E' : C} {p' : E' ⟶ B'} {t' : E' ⟶ E} (sq : IsPullback t' p' p f) :
    Nonempty (TrivialBundleWithFiberOver F p f) ↔
      Nonempty (TrivialBundleWithFiber F p') := by
  constructor
  · rintro ⟨hp⟩
    exact ⟨hp.trivialBundleWithFiber sq⟩
  · rintro ⟨hp'⟩
    exact ⟨{ sq := sq, h := hp' }⟩

end MorphismProperty

end CategoryTheory
