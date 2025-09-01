import TopCatModelCategory.MorphismProperty

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

namespace Limits.BinaryFan.IsLimit

variable {X₁ X₂ : C} {c : BinaryFan X₁ X₂} (hc : IsLimit c)
  {T : C} (f₁ : T ⟶ X₁) (f₂ : T ⟶ X₂)

def lift : T ⟶ c.pt :=
  (Limits.BinaryFan.IsLimit.lift' hc f₁ f₂).1

@[reassoc (attr := simp)]
lemma lift_fst : lift hc f₁ f₂ ≫ c.fst = f₁ :=
  (Limits.BinaryFan.IsLimit.lift' hc f₁ f₂).2.1

@[reassoc (attr := simp)]
lemma lift_snd : lift hc f₁ f₂ ≫ c.snd = f₂ :=
  (Limits.BinaryFan.IsLimit.lift' hc f₁ f₂).2.2

lemma exists_lift
    {X₁ X₂ : C} {c : BinaryFan X₁ X₂} (hc : IsLimit c)
    {T : C} (f₁ : T ⟶ X₁) (f₂ : T ⟶ X₂) :
    ∃ φ, φ ≫ c.fst = f₁ ∧ φ ≫ c.snd = f₂ :=
  ⟨lift hc f₁ f₂, by simp, by simp⟩

end Limits.BinaryFan.IsLimit

namespace MorphismProperty

structure TrivialBundleWithFiber (F : C) {E B : C} (p : E ⟶ B) where
  r : E ⟶ F
  isLimit : IsLimit (BinaryFan.mk p r)

namespace TrivialBundleWithFiber

variable {F E B : C} {p : E ⟶ B} (h : TrivialBundleWithFiber F p)

lemma ext_iff {h₁ h₂ : TrivialBundleWithFiber F p} :
    h₁ = h₂ ↔ h₁.r = h₂.r := by
  constructor
  · rintro rfl
    rfl
  · obtain ⟨r₁, h₁⟩ := h₁
    obtain ⟨r₂, h₂⟩ := h₂
    rintro rfl
    obtain rfl : h₁ = h₂ := by subsingleton
    rfl

@[ext]
lemma ext {h₁ h₂ : TrivialBundleWithFiber F p} (eq : h₁.r = h₂.r) : h₁ = h₂ := by
  rwa [ext_iff]

@[simps]
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

lemma isPullback_of_isTerminal {T : C} (hT : IsTerminal T) :
    IsPullback h.r p (hT.from _) (hT.from _) where
  w := by simp
  isLimit' := ⟨
    PullbackCone.IsLimit.mk _
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).1)
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.2)
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.1)
      (fun s m hm₁ hm₂ ↦ by
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · exact hm₂.trans (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.1.symm
        · exact hm₁.trans (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.2.symm)⟩

lemma exists_iso {E' : C} {p' : E' ⟶ B} (h' : TrivialBundleWithFiber F p') :
    ∃ (e : E ≅ E'), e.hom ≫ p' = p ∧ e.hom ≫ h'.r = h.r := by
  obtain ⟨hom, h₁, h₂⟩ := BinaryFan.IsLimit.exists_lift h'.isLimit p h.r
  obtain ⟨inv, h₃, h₄⟩ := BinaryFan.IsLimit.exists_lift h.isLimit p' h'.r
  dsimp at h₁ h₂ h₃ h₄
  refine ⟨
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_, ?_⟩
  · apply BinaryFan.IsLimit.hom_ext h.isLimit <;> aesop
  · apply BinaryFan.IsLimit.hom_ext h'.isLimit <;> aesop
  · aesop
  · aesop

@[simps]
def ofIso {E' : C} (e : E' ≅ E) {p' : E' ⟶ B} (hp' : e.hom ≫ p = p') :
    TrivialBundleWithFiber F p' where
  r := e.hom ≫ h.r
  isLimit := IsLimit.ofIsoLimit h.isLimit (BinaryFan.ext e (by aesop) (by simp)).symm

lemma isPullback {E' B' : C} {p' : E' ⟶ B'} (h' : TrivialBundleWithFiber F p')
    (t : E' ⟶ E) (b : B' ⟶ B) (h₁ : t ≫ p = p' ≫ b) (h₂ : t ≫ h.r = h'.r) :
    IsPullback t p' p b where
  isLimit' :=
    ⟨Limits.PullbackCone.IsLimit.mk _
      (fun s ↦ BinaryFan.IsLimit.lift h'.isLimit s.snd (s.fst ≫ h.r))
      (fun s ↦ by
        have h₃ := BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r)
        have h₄ := BinaryFan.IsLimit.lift_snd h'.isLimit s.snd (s.fst ≫ h.r)
        dsimp at h₃ h₄
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · dsimp
          rw [Category.assoc, h₁, reassoc_of% h₃, s.condition]
        · dsimp
          rw [Category.assoc, h₂, h₄])
      (fun s ↦ BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r))
      (fun s m hm₁ hm₂ ↦ by
        have h₃ := BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r)
        have h₄ := BinaryFan.IsLimit.lift_snd h'.isLimit s.snd (s.fst ≫ h.r)
        dsimp at h₃ h₄
        apply BinaryFan.IsLimit.hom_ext h'.isLimit
        · dsimp
          rw [hm₂, h₃]
        · dsimp
          rw [h₄, ← h₂, reassoc_of% hm₁])⟩

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
