import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace CategoryTheory

variable {C : Type*} [Category C]
open Limits


namespace MorphismProperty

variable (W : MorphismProperty C) [W.IsStableUnderBaseChange]

structure Over {X S : C} (f : X ⟶ S) {S' : C} (i : S' ⟶ S) where
  {obj : C}
  {t : obj ⟶ X}
  {l : obj ⟶ S'}
  sq : IsPullback t l f i
  hl : W l

namespace Over

variable {W} {X S : C} {f : X ⟶ S} {S' : C} {i : S' ⟶ S} (h : W.Over f i)

def pullback {S'' : C} (φ : S'' ⟶ S')
    {X'' : C} {t : X'' ⟶ h.obj} {l : X'' ⟶ S''}
    (sq : IsPullback t l h.l φ): W.Over f (φ ≫ i) where
  sq := sq.paste_horiz h.sq
  hl := of_isPullback sq h.hl

end Over

variable (J : GrothendieckTopology C) [HasPullbacks C]

def sieveLocally {X S : C} (f : X ⟶ S) : Sieve S where
  arrows S' i := Nonempty (W.Over f i)
  downward_closed  := by
    rintro S' S'' i ⟨h⟩ l
    exact ⟨h.pullback  l (IsPullback.of_hasPullback _ _)⟩

def locally : MorphismProperty C := fun _ S f ↦ W.sieveLocally f ∈ J S

end MorphismProperty

end CategoryTheory
