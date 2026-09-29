module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Order.SuccPred.InitialSeg

@[expose] public section

universe w w' v u

open CategoryTheory Category Limits

/-namespace InitialSeg

variable {J J' : Type*} [PartialOrder J] [PartialOrder J'] (h : J' ≤i J)

def monotone_iio (m : J') :
    Monotone (fun (⟨i, hi⟩ : Set.Iio m) ↦
      (⟨h i, by simpa using hi⟩ : Set.Iio (h m))) :=
  fun _ _ _ ↦ by simpa

abbrev functorIio (h : J' ≤i J) (m : J') : Set.Iio m ⥤ Set.Iio (h m) :=
  (h.monotone_iio m).functor

instance : (h.functorIio m).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : (h.functorIio m).Full where
  map_surjective := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ f
    exact ⟨homOfLE (by simpa using leOfHom f), Subsingleton.elim _ _⟩

instance : (h.functorIio m).EssSurj where
  mem_essImage := fun ⟨i, hi⟩ ↦ by
    obtain ⟨j, rfl⟩ := h.mem_range_of_rel hi
    exact ⟨⟨j, by simpa using hi⟩, ⟨Iso.refl _⟩⟩

instance : (h.functorIio m).IsEquivalence where

@[simps! functor]
noncomputable def equivalenceIio (h : J' ≤i J) (m : J') : Set.Iio m ≌ Set.Iio (h m) :=
  (h.functorIio m).asEquivalence

@[simp]
lemma isMin_iff (m : J') :
    IsMin (h m) ↔ IsMin m := by
  refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
  · intro i hi
    rw [← h.toOrderEmbedding.le_iff_le] at hi ⊢
    exact hm hi
  · intro i hi
    obtain ⟨i, rfl⟩ := h.mem_range_of_le hi
    simp only [le_iff_le] at hi ⊢
    exact hm hi

@[simp]
lemma isSuccPrelimit_iff (m : J') :
    Order.IsSuccPrelimit (h m) ↔ Order.IsSuccPrelimit m := by
  refine ⟨fun hm i hi ↦ ?_, fun hm i hi ↦ ?_⟩
  · have := hm (h i)
    simp only [apply_covBy_apply_iff] at this
    tauto
  · obtain ⟨i, rfl⟩ := h.mem_range_of_le hi.lt.le
    exact hm i (by simpa using hi)

@[simp]
lemma isSuccLimit_iff (m : J') :
    Order.IsSuccLimit (h m) ↔ Order.IsSuccLimit m := by
  simp [Order.IsSuccLimit]

end InitialSeg

namespace PrincipalSeg

variable {J J' : Type*} [PartialOrder J] [PartialOrder J'] (h : J' <i J)
  {C : Type*} [Category C]
  (F : J ⥤ C)

@[simps]
def cocone : Cocone (h.monotone.functor ⋙ F) where
  pt := F.obj h.top
  ι :=
    { app i := F.map (homOfLE (h.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [comp_id, ← F.map_comp]
        rfl }


def monotone_to_iio_top :
    Monotone (fun i ↦ (⟨h i, h.lt_top i⟩ : Set.Iio h.top)) :=
  fun _ _ _ ↦ by simpa

abbrev functorToIioTop (h : J' <i J) : J' ⥤ Set.Iio h.top :=
  h.monotone_to_iio_top.functor

instance : h.functorToIioTop.Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : h.functorToIioTop.Full where
  map_surjective f := ⟨homOfLE (by simpa using leOfHom f), Subsingleton.elim _ _⟩

instance : h.functorToIioTop.EssSurj where
  mem_essImage := fun ⟨i, hi⟩ ↦ by
    simp at hi
    obtain ⟨j, rfl⟩ := h.mem_range_of_rel_top hi
    exact ⟨j, ⟨Iso.refl _⟩⟩

instance : h.functorToIioTop.IsEquivalence where

@[simps! functor]
noncomputable def equivalenceIioTop (h : J' <i J) : J' ≌ Set.Iio h.top :=
  h.functorToIioTop.asEquivalence

end PrincipalSeg

@[simps]
def Set.Iio.principalSeg {α : Type*} [PartialOrder α] (a : α) :
    Set.Iio a <i α where
  top := a
  toFun := fun ⟨i, _⟩ ↦ i
  inj' := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by simp

@[simps]
def Set.Iic.initialSeg {α : Type*} [PartialOrder α] (a : α) :
    Set.Iic a ≤i α where
  toFun := fun ⟨i, _⟩ ↦ i
  inj' := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' i j hj := by simpa using hj.le.trans i.2

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J] (F : J ⥤ C)
  [F.IsWellOrderContinuous]

noncomputable def isWellOrderContinuousOfPrincipalSeg
    {J' : Type w'} [PartialOrder J'] (h : J' <i J) (htop : Order.IsSuccLimit h.top) :
    IsColimit (h.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous h.top htop).whiskerEquivalence (h.equivalenceIioTop)

namespace IsWellOrderContinuous

instance {J' : Type w'} [PartialOrder J'] (h : J' ≤i J) :
    (h.monotone.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm :=
    ⟨(F.isColimitOfIsWellOrderContinuous (h m)
      (by simpa using hm)).whiskerEquivalence (h.equivalenceIio m)⟩

instance {J' : Type w'} [PartialOrder J'] (h : J' <i J) :
    (h.monotone.functor ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs ((h : J' ≤i J).monotone.functor ⋙ F).IsWellOrderContinuous

example (j : J) :
    ((Set.Iio.principalSeg j).monotone.functor ⋙ F).IsWellOrderContinuous := by
  infer_instance

example (j : J) :
    ((Set.Iic.initialSeg j).monotone.functor ⋙ F).IsWellOrderContinuous := by
  infer_instance

end IsWellOrderContinuous

end Functor

end CategoryTheory-/
