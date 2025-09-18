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
  downward_closed := by
    rintro S' S'' i ⟨h⟩ l
    exact ⟨h.pullback  l (IsPullback.of_hasPullback _ _)⟩

lemma mem_sieveLocally_iff {X S : C} (f : X ⟶ S) {S' : C} (i : S' ⟶ S):
    W.sieveLocally f i ↔ Nonempty (W.Over f i) := Iff.rfl

def locally : MorphismProperty C := fun _ S f ↦ W.sieveLocally f ∈ J S

lemma le_locally : W ≤ W.locally J := by
  intro S' S f hf
  refine J.superset_covering ?_ (J.top_mem S)
  dsimp [locally]
  rw [top_le_iff, ← Sieve.id_mem_iff_eq_top, mem_sieveLocally_iff]
  exact ⟨{
    obj := S'
    t := 𝟙 _
    l := f
    sq := IsPullback.of_id_fst
    hl := hf
  }⟩

instance : (W.locally J).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf
  refine J.superset_covering ?_ (J.pullback_stable (f := e.inv.right) hf)
  intro Z a h
  rw [Sieve.pullback_apply, mem_sieveLocally_iff] at h
  obtain ⟨h⟩ := h
  rw [mem_sieveLocally_iff]
  exact ⟨{
    obj := h.obj
    t := h.t ≫ e.hom.left
    l := h.l
    sq := IsPullback.of_iso h.sq (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
        (Arrow.rightFunc.mapIso e) (by simp) (by simp) (by simp) (by simp)
    hl := h.hl
  }⟩

lemma locally_monotone {W₁ W₂ : MorphismProperty C}
    [W₁.IsStableUnderBaseChange] [W₂.IsStableUnderBaseChange] (hW : W₁ ≤ W₂)
    (J : GrothendieckTopology C) : W₁.locally J ≤ W₂.locally J := by
  rintro X Y f hf
  refine J.superset_covering ?_ hf
  rintro S' i ⟨h⟩
  exact ⟨{
    sq := h.sq
    hl := hW _ h.hl
  }⟩

end MorphismProperty

end CategoryTheory
