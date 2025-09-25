import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

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

variable {W}

def pullback {X S : C} {f : X ⟶ S} {S' : C} {i : S' ⟶ S} (h : W.Over f i) {S'' : C} (φ : S'' ⟶ S')
    {X'' : C} {t : X'' ⟶ h.obj} {l : X'' ⟶ S''}
    (sq : IsPullback t l h.l φ): W.Over f (φ ≫ i) where
  sq := sq.paste_horiz h.sq
  hl := of_isPullback sq h.hl

variable (W) in
noncomputable def equivOfIsPullback
    {X S X₀ S₀ : C} {t : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {b : S ⟶ S₀}
    (sq : IsPullback t f f₀ b) {S' : C} (i : S' ⟶ S) :
    W.Over f₀ (i ≫ b) ≃ W.Over f i where
  toFun h :=
    { obj := h.obj
      t := sq.lift h.t (h.l ≫ i) (by simp [h.sq.w])
      l := h.l
      sq := IsPullback.of_right (by simpa using h.sq) (by simp) sq
      hl := h.hl }
  invFun h :=
    { obj := h.obj
      t := h.t ≫ t
      l := h.l
      sq := h.sq.paste_horiz sq
      hl := h.hl }
  left_inv h := by
    cases h
    simp
  right_inv h := by
    obtain ⟨sq', _⟩ := h
    simp only [mk.injEq, heq_eq_eq, and_true, true_and]
    apply sq.hom_ext <;> simp [sq'.w]


end Over

variable (J : GrothendieckTopology C) [HasPullbacks C]

@[simps]
def sieveLocallyTarget {X S : C} (f : X ⟶ S) : Sieve S where
  arrows S' i := Nonempty (W.Over f i)
  downward_closed := by
    rintro S' S'' i ⟨h⟩ l
    exact ⟨h.pullback  l (IsPullback.of_hasPullback _ _)⟩

lemma mem_sieveLocallyTarget_iff {X S : C} (f : X ⟶ S) {S' : C} (i : S' ⟶ S):
    W.sieveLocallyTarget f i ↔ Nonempty (W.Over f i) := Iff.rfl

def locallyTarget : MorphismProperty C := fun _ S f ↦ W.sieveLocallyTarget f ∈ J S

lemma le_locallyTarget : W ≤ W.locallyTarget J := by
  intro S' S f hf
  refine J.superset_covering ?_ (J.top_mem S)
  dsimp [locallyTarget]
  rw [top_le_iff, ← Sieve.id_mem_iff_eq_top, mem_sieveLocallyTarget_iff]
  exact ⟨{
    obj := S'
    t := 𝟙 _
    l := f
    sq := IsPullback.of_id_fst
    hl := hf
  }⟩

instance : (W.locallyTarget J).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf
  refine J.superset_covering ?_ (J.pullback_stable (f := e.inv.right) hf)
  intro Z a h
  rw [Sieve.pullback_apply, mem_sieveLocallyTarget_iff] at h
  obtain ⟨h⟩ := h
  rw [mem_sieveLocallyTarget_iff]
  exact ⟨{
    obj := h.obj
    t := h.t ≫ e.hom.left
    l := h.l
    sq := IsPullback.of_iso h.sq (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
        (Arrow.rightFunc.mapIso e) (by simp) (by simp) (by simp) (by simp)
    hl := h.hl
  }⟩

lemma locallyTarget_monotone {W₁ W₂ : MorphismProperty C}
    [W₁.IsStableUnderBaseChange] [W₂.IsStableUnderBaseChange] (hW : W₁ ≤ W₂)
    (J : GrothendieckTopology C) : W₁.locallyTarget J ≤ W₂.locallyTarget J := by
  rintro X Y f hf
  refine J.superset_covering ?_ hf
  rintro S' i ⟨h⟩
  exact ⟨{
    sq := h.sq
    hl := hW _ h.hl
  }⟩

section

variable {E B : C} (p : E ⟶ B)

def objectPropertyOver :
    ObjectProperty (CategoryTheory.Over B) :=
  fun X ↦ Nonempty (W.Over p X.hom)

variable {W p}

lemma objectPropertyOver.precomp
    {X Y : CategoryTheory.Over B} (hY : W.objectPropertyOver p Y)
    (g : X ⟶ Y) :
    W.objectPropertyOver p X :=
  let h := hY.some
  ⟨{
    obj := pullback h.l g.left
    t := pullback.fst _ _ ≫ h.t
    l := pullback.snd _ _
    sq := by simpa using IsPullback.paste_horiz (IsPullback.of_hasPullback h.l g.left) h.sq
    hl := of_isPullback (IsPullback.of_hasPullback h.l g.left) h.hl
  }⟩

end

omit [W.IsStableUnderBaseChange] [HasPullbacks C] in
lemma objectPropertyOver_iff_map_of_isPullback {E' E B' B : C} {t : E' ⟶ E} {p' : E' ⟶ B'}
    {p : E ⟶ B} {b : B'⟶ B} (sq : IsPullback t p' p b) (X : CategoryTheory.Over B') :
    W.objectPropertyOver p' X ↔ W.objectPropertyOver p ((Over.map b).obj X) :=
  (Over.equivOfIsPullback W sq X.hom).symm.nonempty_congr

end MorphismProperty

namespace ObjectProperty

class IsStableByPrecomp (P : ObjectProperty C) where
  of_precomp (P) {X Y : C} (f : X ⟶ Y) : P Y → P X

export IsStableByPrecomp (of_precomp)

instance (P : ObjectProperty C) [P.IsStableByPrecomp] :
    P.IsClosedUnderIsomorphisms where
  of_iso e hX := P.of_precomp e.inv hX

variable {B : C} (P : ObjectProperty (Over B)) [P.IsStableByPrecomp] (J : GrothendieckTopology C)

@[simps]
def sieveOverLocally (X : Over B) : Sieve X.left where
  arrows {Y} g := P (Over.mk (g ≫ X.hom))
  downward_closed {Y Z f} hZ g := P.of_precomp (Over.homMk (by exact g) (by simp)) hZ

def overLocally : ObjectProperty (Over B) :=
  fun X ↦ P.sieveOverLocally X ∈ J X.left

instance : (P.overLocally J).IsStableByPrecomp where
  of_precomp {X Y} f hY := by
    refine J.superset_covering ?_ (J.pullback_stable f.left hY)
    intro Z g hg
    simpa using hg

end ObjectProperty

namespace MorphismProperty

variable (W : MorphismProperty C) {E B : C} (p : E ⟶ B)

instance [HasPullbacks C] [W.IsStableUnderBaseChange] :
    (W.objectPropertyOver p).IsStableByPrecomp where
  of_precomp := by
    rintro X Y f ⟨hY⟩
    constructor
    rw [← Over.w f]
    exact hY.pullback _ (IsPullback.of_hasPullback _ _)

variable [HasPullbacks C] [W.IsStableUnderBaseChange]

lemma sieveOverLocally_objectPropertyOver_of_isPullback (X : CategoryTheory.Over B)
    {Y : C} {t : Y ⟶ E} {l : Y ⟶ X.left} (sq : IsPullback t l p X.hom) :
    (W.objectPropertyOver p).sieveOverLocally X = W.sieveLocallyTarget l := by
  ext Z f
  exact Equiv.nonempty_congr (Over.equivOfIsPullback W sq f)

variable (J : GrothendieckTopology C)

lemma overLocally_objectPropertyOver_iff_locallyTarget (X : CategoryTheory.Over B)
    {Y : C} {t : Y ⟶ E} {l : Y ⟶ X.left} (sq : IsPullback t l p X.hom) :
    ((W.objectPropertyOver p).overLocally J) X ↔ W.locallyTarget J l := by
  dsimp [locallyTarget, ObjectProperty.overLocally]
  rw [sieveOverLocally_objectPropertyOver_of_isPullback _ _ _ sq]

variable {p} in
lemma overLocally_objectPropertyOver_over_map_obj_iff {E' B' : C} {t : E' ⟶ E}
    {p' : E' ⟶ B'} {b : B' ⟶ B} (sq : IsPullback t p' p b) (X' : CategoryTheory.Over B') :
  ((W.objectPropertyOver p).overLocally J) ((Over.map b).obj X') ↔
    ((W.objectPropertyOver p').overLocally J) X' := by
  have sq' := IsPullback.of_hasPullback p' X'.hom
  rw [overLocally_objectPropertyOver_iff_locallyTarget _ _ _ _ (sq'.paste_horiz sq),
    overLocally_objectPropertyOver_iff_locallyTarget _ _ _ _ sq']

end MorphismProperty

end CategoryTheory
