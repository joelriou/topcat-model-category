import TopCatModelCategory.MorphismProperty

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace MorphismProperty

structure TrivialBundleWithFiber (F : C) {E B : C} (p : E ⟶ B) where
  r : E ⟶ F
  isLimit : IsLimit (BinaryFan.mk p r)

namespace TrivialBundleWithFiber

variable {F E B : C} {p : E ⟶ B} (h : TrivialBundleWithFiber F p)

noncomputable def pullback {E' B' : C} {p' : E' ⟶ B'} {f : B' ⟶ B} {f' : E' ⟶ E}
    (sq : IsPullback f' p' p f) :
    TrivialBundleWithFiber F p' where
  r := f' ≫ h.r
  isLimit :=
    BinaryFan.isLimitMk
      (fun s ↦ sq.lift (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).1 s.fst
        (BinaryFan.IsLimit.lift' _ _ _).2.1)
      (fun s ↦ by simp)
      (fun s ↦ by simpa using (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.2)
      (fun s m hm₁ hm₂ ↦ by
        apply sq.hom_ext
        · apply BinaryFan.IsLimit.hom_ext h.isLimit
          · dsimp
            rw [Category.assoc, IsPullback.lift_fst, sq.w, reassoc_of% hm₁]
            exact (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.1.symm
          · dsimp
            rw [Category.assoc, IsPullback.lift_fst, hm₂]
            exact (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.2.symm
        · simp [hm₁])

variable (p) in
def ofIsTerminal (hB : IsTerminal B) : TrivialBundleWithFiber E p where
  r := 𝟙 E
  isLimit :=
    BinaryFan.isLimitMk (fun s ↦ s.snd) (fun s ↦ hB.hom_ext _ _)
      (fun s ↦ by simp)
      (fun s m _ hm ↦ by simpa using hm)

@[simps hom]
def isoOfIsTerminal (h : TrivialBundleWithFiber F p) (hB : IsTerminal B) : E ≅ F where
  hom := h.r
  inv := (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).1
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext h.isLimit
    · apply hB.hom_ext
    · have := (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).2.2
      dsimp at this ⊢
      simp [this]
  inv_hom_id := (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).2.2

end TrivialBundleWithFiber

def trivialBundlesWithFiber (F : C) : MorphismProperty C :=
  fun _ _ p ↦ Nonempty (TrivialBundleWithFiber F p)

instance (F : C) : (trivialBundlesWithFiber F).IsStableUnderBaseChange where
  of_isPullback sq h := ⟨h.some.pullback sq⟩

def trivialBundles : MorphismProperty C :=
  ⨆ F, trivialBundlesWithFiber F

instance : (trivialBundles (C := C)).IsStableUnderBaseChange := by
  dsimp only [trivialBundles]
  infer_instance

lemma trivialBundles.of_isPullback_of_fac {E E' B B' : C} {p' : E' ⟶ B'} {p : E ⟶ B}
    {f : B' ⟶ B} {f' : E' ⟶ E} (sq : IsPullback f' p' p f)
    {T : C} (hT : IsTerminal T) (a : B' ⟶ T) (b : T ⟶ B) (fac : a ≫ b = f)
    [HasPullback p b] :
    trivialBundles p' := by
  have sq : IsPullback (pullback.lift f' (p' ≫ a) (by rw [Category.assoc, fac, sq.w]))
      p' (pullback.snd p b) a := IsPullback.of_right (by aesop) (by simp)
      (IsPullback.of_hasPullback p b)
  refine MorphismProperty.of_isPullback sq ?_
  simp only [trivialBundles, iSup_iff]
  exact ⟨_, ⟨TrivialBundleWithFiber.ofIsTerminal (pullback.snd p b) hT⟩⟩

end MorphismProperty

end CategoryTheory
