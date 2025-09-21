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

noncomputable def map {D : Type*} [Category D] (G : C ⥤ D) [PreservesLimit (cospan p f) G]
    [PreservesLimit (pair B' F) G] :
    TrivialBundleWithFiberOver (G.obj F) (G.map p) (G.map f) where
  sq := hp.sq.map G
  h := hp.h.map G

noncomputable def pullback {B'' E'' : C} {t : E'' ⟶ hp.E'} {p'' : E'' ⟶ B''} {g : B'' ⟶ B'}
    (sq : IsPullback t p'' hp.p' g) :
    TrivialBundleWithFiberOver F p (g ≫ f) where
  E' := E''
  p' := p''
  t := t ≫ hp.t
  sq := sq.paste_horiz hp.sq
  h := hp.h.pullback sq

noncomputable def pullback' {B'' : C} (g : B'' ⟶ B') [HasPullback hp.p' g] :
    TrivialBundleWithFiberOver F p (g ≫ f) :=
  hp.pullback (IsPullback.of_hasPullback _ _)

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
