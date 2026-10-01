module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Set
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
public import TopCatModelCategory.Multiequalizer

@[expose] public section

universe w v u

open CategoryTheory Limits

/-namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

structure BicartSq : Prop where
  max_eq : x₂ ⊔ x₃ = x₄
  min_eq : x₂ ⊓ x₃ = x₁

namespace BicartSq

variable {x₁ x₂ x₃ x₄ : T} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq
lemma le₁₂ : x₁ ≤ x₂ := by rw [← sq.min_eq]; exact inf_le_left
lemma le₁₃ : x₁ ≤ x₃ := by rw [← sq.min_eq]; exact inf_le_right
lemma le₂₄ : x₂ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_left
lemma le₃₄ : x₃ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_right

-- the associated commutative square in `T`
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice-/

namespace CompleteLattice.MulticoequalizerDiagram

variable {T : Type*} [CompleteLattice T] {ι : Type w} {A : T} {U : ι → T} {V : ι → ι → T}

lemma le (h : MulticoequalizerDiagram A U V) (i : ι) : U i ≤ A := by
  rw [← h.iSup_eq]
  exact le_iSup U i

lemma le₁ (h : MulticoequalizerDiagram A U V) (i j : ι) : V i j ≤ U i := by
  rw [h.eq_inf]
  exact inf_le_left

lemma le₂ (h : MulticoequalizerDiagram A U V) (i j : ι) : V i j ≤ U j := by
  rw [h.eq_inf]
  exact inf_le_right

end CompleteLattice.MulticoequalizerDiagram


@[deprecated (since := "2025-03-18")] alias Set.toTypes := Set.functorToTypes

namespace CategoryTheory.Limits.Types

section Pushouts

section

variable {X X' : Type u} (f : X' → X) (A B : Set X) (A' B' : Set X')
  (hA' : A' = f ⁻¹' A ⊓ B') (hB : B = A ⊔ f '' B')

def pushoutCoconeOfPullbackSets :
    PushoutCocone
      (↾fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩ : _ ⟶ (A : Type u))
      (Set.functorToTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B') :=
  PushoutCocone.mk (W := (B : Type u))
    (Set.functorToTypes.map (homOfLE (by rw [hB]; exact le_sup_left)) : (A : Type u) ⟶ B)
    (↾fun ⟨b', hb'⟩ ↦ ⟨f b', by rw [hB]; exact Or.inr (by aesop)⟩) rfl

variable (T : Set X)

open Classical in
noncomputable def isColimitPushoutCoconeOfPullbackSets
    (hf : Function.Injective (fun (b : (A'ᶜ : Set _)) ↦ f b)) :
    IsColimit (pushoutCoconeOfPullbackSets f A B A' B' hA' hB) := by
  let g₁ : (A' : Type u) ⟶ A := ↾fun ⟨a', ha'⟩ ↦ ⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩
  let g₂ : (A' : Type u) ⟶ B' :=
    (Set.functorToTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B')
  have imp {b : X} (hb : b ∈ B) (hb' : b ∉ A) : b ∈ f '' B' := by
    simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
    tauto
  let desc (s : PushoutCocone g₁ g₂) : (B : Type u) ⟶ s.pt := ↾fun ⟨b, hb⟩ ↦
    if hb' : b ∈ A then
      s.inl ⟨b, hb'⟩
    else
      s.inr ⟨(imp hb hb').choose, (imp hb hb').choose_spec.1⟩
  have inl_desc_apply (s) (a : A) : desc s ⟨a, by
    rw [hB]
    exact Or.inl a.2⟩ = s.inl a := dite_eq_left a.2
  have inr_desc_apply (s) (b' : B') : desc s ⟨f b', by
      rw [hB]
      exact Or.inr ⟨b'.1, b'.2, rfl⟩⟩ = s.inr b' := by
    obtain ⟨b', hb'⟩ := b'
    dsimp [desc]
    split_ifs with hb''
    · exact ConcreteCategory.congr_hom s.condition ⟨b', by rw [hA']; exact ⟨hb'', hb'⟩⟩
    · apply congr_arg
      ext
      have hb''' : f b' ∈ B := by
        rw [hB]
        exact Or.inr ⟨b', hb', rfl⟩
      dsimp
      subst hA'
      refine congr_arg Subtype.val (@hf ⟨(imp hb''' hb'').choose, ?_⟩ ⟨b', ?_⟩
        (imp hb''' hb'').choose_spec.2)
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        refine fun h _ ↦ hb'' ?_
        rw [← (imp hb''' hb'').choose_spec.2]
        exact h
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        exact fun h ↦ (hb'' h).elim
  refine PushoutCocone.IsColimit.mk _ desc
    (fun s ↦ by ext; apply inl_desc_apply)
    (fun s ↦ by ext; apply inr_desc_apply)
    (fun s m h₁ h₂ ↦ ?_)
  ext ⟨b, hb⟩
  dsimp
  by_cases hb' : b ∈ f '' B'
  · obtain ⟨b', hb', rfl⟩ := hb'
    exact (ConcreteCategory.congr_hom h₂ ⟨b', hb'⟩).trans (inr_desc_apply s ⟨b', hb'⟩ ).symm
  · have hb : b ∈ A := by
      simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
      tauto
    exact (ConcreteCategory.congr_hom h₁ ⟨b, hb⟩).trans (inl_desc_apply s ⟨b, hb⟩).symm

end

section

variable {X : Type u} {A₁ A₂ A₃ A₄ : Set X} (sq : Lattice.BicartSq A₁ A₂ A₃ A₄)

def pushoutCoconeOfBicartSqOfSets :
    PushoutCocone (Set.functorToTypes.map (homOfLE sq.le₁₂))
      (Set.functorToTypes.map (homOfLE sq.le₁₃)) :=
  PushoutCocone.mk _ _ (sq.commSq.map Set.functorToTypes).w

noncomputable def isColimitPushoutCoconeOfBicartSqOfSets :
    IsColimit (pushoutCoconeOfBicartSqOfSets sq) :=
  isColimitPushoutCoconeOfPullbackSets id A₂ A₄ A₁ A₃
    sq.inf_eq.symm (by simpa using sq.sup_eq.symm)
      (by rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl)

end

end Pushouts

end CategoryTheory.Limits.Types

/-namespace CompleteLattice

variable {T : Type*} [CompleteLattice T] {ι : Type*} (X : T) (U : ι → T) (V : ι → ι → T)

structure MulticoequalizerDiagram : Prop where
  hX : X = ⨆ (i : ι), U i
  hV (i j : ι) : V i j = U i ⊓ U j

namespace MulticoequalizerDiagram

variable {X U V} (d : MulticoequalizerDiagram X U V)

@[simps]
def multispanIndex : MultispanIndex T where
  L := ι × ι
  R := ι
  fstFrom := Prod.fst
  sndFrom := Prod.snd
  left := fun ⟨i, j⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)

variable [Preorder ι]

@[simps]
def multispanIndex' : MultispanIndex T where
  L := { (i, j) : ι × ι | i < j }
  R := ι
  fstFrom := fun ⟨⟨i, j⟩, _⟩ ↦ i
  sndFrom := fun ⟨⟨i, j⟩, _⟩ ↦ j
  left := fun ⟨⟨i, j⟩, _⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork' : Multicofork d.multispanIndex' :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)


end MulticoequalizerDiagram

end CompleteLattice-/

namespace CategoryTheory.Limits

namespace MultispanIndex

variable {J : MultispanShape} (d : MultispanIndex J (Type u))

abbrev MulticoforkTypes := d.multispan.CoconeTypes

namespace MulticoforkTypes

variable {d}

def π (c : d.MulticoforkTypes) (b : J.R) : d.right b → c.pt := c.ι (.right b)

lemma ι_left_eq_π_comp_fst (c : d.MulticoforkTypes) (a : J.L) :
    c.ι (.left a) = c.π (J.fst a) ∘ d.fst a :=
  (c.ι_naturality (.fst a)).symm

lemma ι_left_eq_π_comp_snd (c : d.MulticoforkTypes) (a : J.L) :
    c.ι (.left a) = c.π (J.snd a) ∘ d.snd a :=
  (c.ι_naturality (.snd a)).symm

lemma condition (c : d.MulticoforkTypes) (b : J.L) :
    c.π (J.fst b) ∘ d.fst b = c.π (J.snd b) ∘ d.snd b := by
  rw [← ι_left_eq_π_comp_fst, ι_left_eq_π_comp_snd]

section

variable (P : Type v) (π : ∀ (b : J.R), d.right b → P)
  (h : ∀ (a : J.L), π (J.fst a) ∘ d.fst a = π (J.snd a) ∘ d.snd a)

def ofπ : d.MulticoforkTypes where
  pt := P
  ι j := match j with
    | .left a => π (J.fst a) ∘ d.fst a
    | .right b => π b
  ι_naturality := by
    rintro (a | _) (_ | _) (_ | _ | _)
    · rfl
    · rfl
    · exact (h _).symm
    · rfl

@[simp]
lemma π_ofπ (b : J.R) : (ofπ P π h).π b = π b := rfl

end

variable {c : d.MulticoforkTypes} (hc : c.IsColimit)

namespace IsColimit

variable {P : Type v}

include hc in
set_option backward.isDefEq.respectTransparency false in
lemma funext {f g : c.pt → P} (h : ∀ (b : J.R), f ∘ c.π b = g ∘ c.π b) : f = g := by
  apply hc.funext
  rintro (a | b)
  · rw [ι_left_eq_π_comp_fst, ← Function.comp_assoc, ← Function.comp_assoc, h]
  · apply h

variable (π : ∀ (b : J.R), d.right b → P)
    (h : ∀ (a : J.L), π (J.fst a) ∘ d.fst a = π (J.snd a) ∘ d.snd a)

include hc h in
lemma exists_desc : ∃ (φ : c.pt → P), ∀ (b : J.R), φ ∘ c.π b = π b := by
  obtain ⟨f, hf⟩ := hc.exists_desc (ofπ P π h)
  exact ⟨f, fun b ↦ hf (.right b)⟩

noncomputable def desc : c.pt → P := (exists_desc hc π h).choose

@[simp]
lemma fac (b : J.R) : (desc hc π h) ∘ c.π b = π b :=
  (exists_desc hc π h).choose_spec b

@[simp]
lemma fac_apply {b : J.R} (x : d.right b) :
    (desc hc π h) (c.π b x) = π b x :=
  congr_fun (fac hc π h b) x

end IsColimit

end MulticoforkTypes

end MultispanIndex

namespace Types

section

variable {T : Type u} {ι : Type v} {X : Set T} {U : ι → Set T} {V : ι → ι → Set T}
  (d : CompleteLattice.MulticoequalizerDiagram X U V)

namespace isColimitMulticoforkMapSetToTypes

include d in
lemma exists_index (x : X) : ∃ (i : ι), x.1 ∈ U i := by
  obtain ⟨x, hx⟩ := x
  rw [← d.iSup_eq] at hx
  aesop

noncomputable def index (x : X) : ι := (exists_index d x).choose

lemma mem (x : X) : x.1 ∈ U (index d x) := (exists_index d x).choose_spec

section

variable {d} (s : Multicofork (d.multispanIndex.map Set.functorToTypes))

noncomputable def desc (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma fac_apply (i : ι) (u : U i) :
    desc s ⟨u, by simp only [← d.iSup_eq]; aesop⟩ = s.π i u :=
  ConcreteCategory.congr_hom (s.condition ⟨index d _, i⟩) ⟨u, by
    dsimp
    simp only [d.eq_inf, Set.inf_eq_inter, Set.mem_inter_iff, Subtype.coe_prop, and_true]
    apply mem⟩

end

/-section

variable [LinearOrder ι] {d} (s : Multicofork (d.multispanIndex'.map Set.functorToTypes))

noncomputable def desc' (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

lemma condition'_apply (x : T) (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j) :
    s.π i ⟨x, hi⟩ = s.π j ⟨x, hj⟩ := by
  obtain hij | rfl | hij := lt_trichotomy i j
  · refine congr_fun (s.condition ⟨⟨i, j⟩, hij⟩) ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hi, hj⟩
  · rfl
  · refine congr_fun (s.condition ⟨⟨j, i⟩, hij⟩).symm ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hj, hi⟩

lemma fac'_apply (i : ι) (u : U i) :
    desc' s ⟨u, by simp only [d.hX]; aesop⟩ = s.π i u := by
  apply condition'_apply

end-/

end isColimitMulticoforkMapSetToTypes

open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes :
    IsColimit (d.multicofork.map Set.functorToTypes) := by
  refine Multicofork.IsColimit.mk _ (fun s ↦ ↾(desc s))
    (fun s i ↦ by ext x; apply fac_apply) (fun s m hm ↦ by
      ext x
      exact ConcreteCategory.congr_hom (hm (index d x)) ⟨x.1, mem d x⟩)

abbrev multicoforkTypesMapSetToTypes :
    (d.multispanIndex.map Set.functorToTypes).MulticoforkTypes :=
  (Functor.coconeTypesEquiv _).symm (d.multicofork.map Set.functorToTypes)

lemma isColimit_multicoforkTypesMapSetToTypes :
    (multicoforkTypesMapSetToTypes d).IsColimit :=
  (isColimit_iff_coconeTypesIsColimit _).1
    ⟨isColimitMulticoforkMapSetToTypes d⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes' [LinearOrder ι] :
    IsColimit (d.multicofork.toLinearOrder.map Set.functorToTypes) :=
  Multicofork.isColimitToLinearOrder
    (d.multicofork.map Set.functorToTypes) (isColimitMulticoforkMapSetToTypes _)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        dsimp
        rw [d.eq_inf, d.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

namespace MulticoequalizerDiagram

variable {Y : Type w}

lemma funext {f g : X → Y} (h : ∀ (i : ι) (u : U i), f ⟨u.1, d.le i u.2⟩ = g ⟨u.1, d.le i u.2⟩) :
    f = g :=
  MultispanIndex.MulticoforkTypes.IsColimit.funext
    (isColimit_multicoforkTypesMapSetToTypes d) (fun i ↦ by ext; apply h)


variable (f : ∀ (i : ι), U i → Y) (hf : ∀ (i j : ι) (x : V i j),
  f i ⟨x, d.le₁ i j x.2⟩ = f j ⟨x, d.le₂ i j x.2⟩)

include hf in
lemma exists_desc : ∃ (φ : X → Y), ∀ (i : ι) (x : U i), φ ⟨x.1, d.le i x.2⟩ = f i x := by
  obtain ⟨φ, hφ⟩ := MultispanIndex.MulticoforkTypes.IsColimit.exists_desc
    (isColimit_multicoforkTypesMapSetToTypes d) f (fun ⟨i, j⟩ ↦ by
      ext v
      exact hf i j v)
  exact ⟨φ, fun i ↦ congr_fun (hφ i)⟩

noncomputable def desc : X → Y := (exists_desc d f hf).choose

lemma fac {i : ι} (x : U i) : desc d f hf ⟨x.1, d.le i x.2⟩ = f i x :=
  (exists_desc d f hf).choose_spec i x

end MulticoequalizerDiagram

end

section

variable {X₁ X₂ X₃ X₄ X₅ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄}
  {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄}

/-lemma eq_or_eq_of_isPushout (h : IsPushout t l r b)
    (x₄ : X₄) : (∃ x₂, x₄ = r x₂) ∨ ∃ x₃, x₄ = b x₃ := by
  obtain ⟨j, x, rfl⟩ := jointly_surjective_of_isColimit h.isColimit x₄
  obtain (_ | _ | _) := j
  · exact Or.inl ⟨t x, by cat_disch⟩
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma eq_or_eq_of_isPushout' (h : IsPushout t l r b)
    (x₄ : X₄) : (∃ x₂, x₄ = r x₂) ∨ ∃ x₃, x₄ = b x₃ ∧ x₃ ∉ Set.range l := by
  obtain h₁ | ⟨x₃, hx₃⟩ := eq_or_eq_of_isPushout h x₄
  · refine Or.inl h₁
  · by_cases h₂ : x₃ ∈ Set.range l
    · obtain ⟨x₁, rfl⟩ := h₂
      exact Or.inl ⟨t x₁, by simpa [hx₃] using ConcreteCategory.congr_hom h.w.symm x₁⟩
    · exact Or.inr ⟨x₃, hx₃, h₂⟩-/

lemma exists_of_inl_eq_inr_of_isPushout (h : IsPushout t l r b) (ht : Function.Injective t)
    (x₂ : X₂) (x₃ : X₃) (hx : r x₂ = b x₃) :
    ∃ x₁, t x₁ = x₂ ∧ l x₁ = x₃ :=
  (pushoutCocone_inl_eq_inr_iff_of_isColimit h.isColimit ht x₂ x₃).1 hx

--lemma pushoutCocone_inl_eq_inr_iff_of_isColimit {c : PushoutCocone f g} (hc : IsColimit c)
--    (h₁ : Function.Injective f) (x₁ : X₁) (x₂ : X₂) :
--    c.inl x₁ = c.inr x₂ ↔ ∃ (s : S), f s = x₁ ∧ g s = x₂ := by
--  rw [pushoutCocone_inl_eq_inr_iff_of_iso
--    (Cocones.ext (IsColimit.coconePointUniqueUpToIso hc (Pushout.isColimitCocone f g))
--    (by simp))]
--  have := (mono_iff_injective f).2 h₁
--  apply Pushout.inl_eq_inr_iff


/-lemma ext_of_isPullback (h : IsPullback t l r b) {x₁ y₁ : X₁}
    (h₁ : t x₁ = t y₁) (h₂ : l x₁ = l y₁) : x₁ = y₁ := by
  apply (h.isLimit.conePointUniqueUpToIso
    (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
  dsimp; ext <;> assumption

lemma exists_of_isPullback (h : IsPullback t l r b)
    (x₂ : X₂) (x₃ : X₃) (hx : r x₂ = b x₃) :
    ∃ x₁, x₂ = t x₁ ∧ x₃ = l x₁ := by
  let e := PullbackCone.IsLimit.equivPullbackObj h.isLimit
  obtain ⟨x₁, hx₁⟩ := e.surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁.symm,
    congr_arg _root_.Prod.snd hx₁.symm⟩-/


open MorphismProperty

/-lemma mono_of_isPushout_of_isPullback (h₁ : IsPushout t l r b)
    {r' : X₂ ⟶ X₅} {b' : X₃ ⟶ X₅} (h₂ : IsPullback t l r' b')
    (facr : r ≫ k = r') (facb : b ≫ k = b') [hr' : Mono r']
    (H : ∀ (x₃ y₃ : X₃) (_ : x₃ ∉ Set.range l)
      (_ : y₃ ∉ Set.range l), b' x₃ = b' y₃ → x₃ = y₃) :
    Mono k := by
  subst facr facb
  have hl : Mono l := (monomorphisms _).of_isPullback h₂ (.infer_property _)
  rw [mono_iff_injective] at hr' hl ⊢
  have w := congr_fun h₁.w
  dsimp at w
  intro x₃ y₃ eq
  obtain (⟨x₂, rfl⟩ | ⟨x₃, rfl, hx₃⟩) := eq_or_eq_of_isPushout' h₁ x₃ <;>
  obtain (⟨y₂, rfl⟩ | ⟨y₃, rfl, hy₃⟩) := eq_or_eq_of_isPushout' h₁ y₃
  · obtain rfl : x₂ = y₂ := hr' eq
    rfl
  · obtain ⟨x₁, rfl, rfl⟩ := exists_of_isPullback h₂ x₂ y₃ eq
    rw [w]
  · obtain ⟨x₁, rfl, rfl⟩ := exists_of_isPullback h₂ y₂ x₃ eq.symm
    rw [w]
  · obtain rfl := H x₃ y₃ hx₃ hy₃ eq
    rfl

lemma isPushout_of_isPullback_of_mono {k : X₄ ⟶ X₅}
    {r' : X₂ ⟶ X₅} {b' : X₃ ⟶ X₅} (h₁ : IsPullback t l r' b')
    (facr : r ≫ k = r') (facb : b ≫ k = b') [Mono r'] [Mono k]
    (h₂ : Set.range r ⊔ Set.range b = Set.univ)
    (H : ∀ (x₃ y₃ : X₃) (_ : x₃ ∉ Set.range l)
      (_ : y₃ ∉ Set.range l), b' x₃ = b' y₃ → x₃ = y₃) :
    IsPushout t l r b := by
  let φ : pushout t l ⟶ X₄ := pushout.desc r b
    (by simp only [← cancel_mono k, Category.assoc, facr, facb, h₁.w])
  have hφ₁ : pushout.inl t l ≫ φ = r := by simp [φ]
  have hφ₂ : pushout.inr t l ≫ φ = b := by simp [φ]
  have := mono_of_isPushout_of_isPullback (IsPushout.of_hasPushout t l) h₁
    (k := φ ≫ k) (by simp [φ, facr]) (by simp [φ, facb]) H
  have := mono_of_mono φ k
  have : Epi φ := by
    rw [epi_iff_surjective]
    intro x₄
    have hx₄ := Set.mem_univ x₄
    simp only [← h₂, Set.sup_eq_union, Set.mem_union, Set.mem_range] at hx₄
    obtain (⟨x₂, rfl⟩ | ⟨x₃, rfl⟩) := hx₄
    · exact ⟨_, congr_fun hφ₁ x₂⟩
    · exact ⟨_, congr_fun hφ₂ x₃⟩
  have := isIso_of_mono_of_epi φ
  exact IsPushout.of_iso (IsPushout.of_hasPushout t l)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso φ) (by simp) (by simp)
    (by simp [φ]) (by simp [φ])

lemma isPushout_of_isPullback_of_mono'
    (h₁ : IsPullback t l r b)
    [Mono r]
    (h₂ : Set.range r ⊔ Set.range b = Set.univ)
    (H : ∀ (x₃ y₃ : X₃) (_ : x₃ ∉ Set.range l)
      (_ : y₃ ∉ Set.range l), b x₃ = b y₃ → x₃ = y₃) :
    IsPushout t l r b :=
  isPushout_of_isPullback_of_mono (k := 𝟙 _) h₁ (by simp) (by simp) h₂ H-/

end

/-lemma isPullback_iff {X₁ X₂ X₃ X₄ : Type u} (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (r : X₂ ⟶ X₄)
    (b : X₃ ⟶ X₄) :
  IsPullback t l r b ↔ t ≫ r = l ≫ b ∧
    (∀ x₁ y₁, t x₁ = t y₁ ∧ l x₁ = l y₁ → x₁ = y₁) ∧
    ∀ x₂ x₃, r x₂ = b x₃ → ∃ x₁, x₂ = t x₁ ∧ x₃ = l x₁ := by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ ↦ ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := fun x₁ ↦ ⟨⟨t x₁, l x₁⟩, congr_fun w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      constructor
      · intro x₁ y₁ h
        rw [Subtype.ext_iff, _root_.Prod.ext_iff] at h
        exact h₁ _ _ h
      · rintro ⟨⟨x₂, x₃⟩, h⟩
        obtain ⟨x₁, rfl, rfl⟩ := h₂ x₂ x₃ h
        exact ⟨x₁, rfl⟩
    exact ⟨⟨w⟩, ⟨IsLimit.ofIsoLimit ((Types.pullbackLimitCone r b).isLimit)
      (PullbackCone.ext (asIso φ)).symm⟩⟩-/

lemma isPullback_of_eq_setPreimage {X Y : Type u} (f : X ⟶ Y) (B : Set Y) {A : Set X}
    (hA : A = B.preimage f) :
    IsPullback (↾fun (⟨a, ha⟩ : A) ↦ (⟨f a, by simpa [hA] using ha⟩ : B))
      (↾Subtype.val) (↾Subtype.val) f := by
  rw [isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x₁, _⟩ ⟨_, _⟩ ⟨_, rfl⟩
    rfl
  · rintro ⟨_, hx₃⟩ x₃ rfl
    exact ⟨⟨x₃, by rwa [hA]⟩, rfl, rfl⟩

section

variable {ι : Type v} {X : ι → Type u} {c : Cofan X} (hc : IsColimit c)

include hc
lemma jointly_surjective_of_isColimit_cofan (x : c.pt) :
    ∃ (i : ι) (y : X i), c.inj i y = x := by
  obtain ⟨⟨i⟩, y, hy⟩ := jointly_surjective_of_isColimit hc x
  exact ⟨i, y, hy⟩

lemma cofanInj_apply_eq_iff_of_isColimit {i j : ι} (x : X i) (y : X j) :
    c.inj i x = c.inj j y ↔ ∃ (hij : i = j), y = cast (by rw [hij]) x := by
  constructor; swap
  · rintro ⟨rfl, rfl⟩
    rfl
  · let ρ := Relation.EqvGen (Discrete.functor X).ColimitTypeRel
    have hρ (x y) (h : ρ x y) : x = y := by
      induction h with
      | rel a b r =>
          obtain ⟨⟨a⟩, a'⟩ := a
          obtain ⟨⟨b⟩, b'⟩ := b
          obtain ⟨r, s⟩ := r
          obtain rfl : a = b := Discrete.eq_of_hom r
          aesop
      | refl => rfl
      | symm _ _ _ h => exact h.symm
      | trans _ _ _ _ _ h h' => exact h.trans h'
    intro h
    suffices ρ ⟨_, x⟩ ⟨_, y⟩ by
      have := hρ _ _ this
      aesop
    exact Quot.eq.1
      (((isColimit_iff_coconeTypesIsColimit _).1 ⟨hc⟩).bijective.1 h)

lemma cofanInj_injective_of_isColimit (i : ι) :
    Function.Injective (c.inj i) := by
  intro x y h
  rw [cofanInj_apply_eq_iff_of_isColimit hc] at h
  obtain ⟨_, rfl⟩ := h
  rfl

lemma eq_cofanInj_apply_eq_of_isColimit {i j : ι} (x : X i) (y : X j)
    (h : c.inj i x = c.inj j y) : i = j := by
  rw [cofanInj_apply_eq_iff_of_isColimit hc] at h
  exact h.choose

lemma preimage_image_eq_of_coproducts
    {X' : ι → Type u} {c' : Cofan X'} (hc' : IsColimit c') (f : ∀ i, X i ⟶ X' i)
    (φ : c.pt ⟶ c'.pt) (hφ : ∀ i, c.inj i ≫ φ = f i ≫ c'.inj i)
    (i : ι) (F : Set (X' i)) :
    φ ⁻¹' (c'.inj i '' F) = c.inj i '' ((f i) ⁻¹' F) := by
  replace hφ {i : ι} (x : X i) : φ (c.inj i x) = c'.inj i (f i x) :=
    ConcreteCategory.congr_hom (hφ i) x
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, eq⟩
    obtain ⟨j, z, rfl⟩ := jointly_surjective_of_isColimit_cofan hc y
    rw [hφ] at eq
    obtain rfl := eq_cofanInj_apply_eq_of_isColimit hc' _ _ eq
    obtain rfl := cofanInj_injective_of_isColimit hc' i eq
    refine ⟨z, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hx, (hφ x).symm⟩

end

section

variable {S X₁ X₂ : Type u} (f : S ⟶ X₁) (g : S ⟶ X₂)

lemma Pushout.inl_eq_inl_iff [Mono f] (x₁ y₁ : X₁) :
    (inl f g x₁ = inl f g y₁) ↔
      x₁ = y₁ ∨ ∃ x₀ y₀, x₁ = f x₀ ∧ y₁ = f y₀ ∧ g x₀ = g y₀ :=
  (Pushout.quot_mk_eq_iff f g (Sum.inl x₁) (Sum.inl y₁)).trans (by aesop)

variable {f g}

lemma pushoutCocone_inl_eq_inl_imp_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ y₁ : X₁) (h : c.inl x₁ = c.inl y₁) :
    c'.inl x₁ = c'.inl y₁ := by
  convert congr_arg e.hom.hom h
  all_goals apply ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm

lemma pushoutCocone_inl_eq_inl_iff_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ y₁ : X₁) :
    c.inl x₁ = c.inl y₁ ↔ c'.inl x₁ = c'.inl y₁ := by
  constructor
  · apply pushoutCocone_inl_eq_inl_imp_of_iso e
  · apply pushoutCocone_inl_eq_inl_imp_of_iso e.symm

lemma pushoutCocone_inl_eq_inl_iff_of_isColimit {c : PushoutCocone f g} (hc : IsColimit c)
    (h₁ : Function.Injective f) (x₁ y₁ : X₁) :
    c.inl x₁ = c.inl y₁ ↔
      x₁ = y₁ ∨ ∃ x₀ y₀, x₁ = f x₀ ∧ y₁ = f y₀ ∧ g x₀ = g y₀ := by
  rw [pushoutCocone_inl_eq_inl_iff_of_iso
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso hc (Pushout.isColimitCocone f g))
    (by cat_disch))]
  have := (mono_iff_injective f).2 h₁
  apply Pushout.inl_eq_inl_iff f g

end


section

variable {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma preimage_image_eq_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t)
    (F : Set X₃) :
    r ⁻¹' (b '' F) = t '' (l ⁻¹' F) := by
  ext x₂
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x₃, hx₃, hx₃'⟩
    obtain ⟨x₁, rfl, rfl⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      sq.isColimit ht x₂ x₃).1 hx₃'.symm
    exact ⟨x₁, hx₃, rfl⟩
  · rintro ⟨x₁, hx₁, rfl⟩
    exact ⟨l x₁, hx₁, ConcreteCategory.congr_hom sq.w.symm x₁⟩

lemma preimage_range_eq_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t) :
    r ⁻¹' (Set.range b) = Set.range t := by
  simpa using preimage_image_eq_of_isPushout sq ht .univ

section

variable (sq : IsPushout t l r b) (ht : Function.Injective t)

include sq ht

lemma injective_of_isPushout  :
    Function.Injective b :=
  Types.pushoutCocone_inr_injective_of_isColimit sq.isColimit ht

noncomputable def equivOfIsPushoutOfInjective :
    ((Set.range t)ᶜ : Set _) ≃ ((Set.range b)ᶜ : Set _) :=
  Equiv.ofBijective (fun ⟨x₂, hx₂⟩ ↦ ⟨r x₂, by
      simpa [← preimage_range_eq_of_isPushout sq ht] using hx₂⟩) (by
    constructor
    · rintro ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩ h
      rw [Subtype.ext_iff] at h
      dsimp at h
      obtain rfl | ⟨x₁, _, rfl, _⟩ :=
        (pushoutCocone_inl_eq_inl_iff_of_isColimit sq.isColimit ht x₂ y₂).1 h
      · rfl
      · simp at hx₂
    · rintro ⟨x₄, hx₄⟩
      obtain ⟨x₃, rfl⟩ | ⟨x₂, rfl, hx₂⟩ :=  eq_or_eq_of_isPushout' sq.flip x₄
      · simp at hx₄
      · refine ⟨⟨x₂, ?_⟩, rfl⟩
        rintro ⟨x₁, rfl⟩
        simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hx₄
        exact hx₄ (l x₁) (ConcreteCategory.congr_hom sq.w.symm x₁))

@[simp]
lemma equivOfIsPushoutOfInjective_apply (x : ((Set.range t)ᶜ : Set _)) :
    (equivOfIsPushoutOfInjective sq ht x).1 = r x.1 := rfl

end

end

end Types

end Limits

namespace Functor

variable {C : Type*} (F : Discrete C ⥤ Type*)

abbrev CofanTypes := F.CoconeTypes

variable {F}

namespace CofanTypes

abbrev inj (c : F.CofanTypes) (i : C) : F.obj ⟨i⟩ → c.pt := c.ι ⟨i⟩

variable (F) in
@[simps]
def sigma : F.CofanTypes where
  pt := Σ (i : C), F.obj ⟨i⟩
  ι := fun ⟨i⟩ x ↦ ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    aesop

@[simp]
lemma sigma_inj (i : C) (x : F.obj ⟨i⟩) :
    (sigma F).inj i x = ⟨i, x⟩ := rfl

lemma isColimit_mk (c : F.CofanTypes)
    (h₁ : ∀ (x : c.pt), ∃ (i : C) (y : F.obj ⟨i⟩), c.inj i y = x)
    (h₂ : ∀ (i : C), Function.Injective (c.inj i))
    (h₃ : ∀ (i j : C) (x : F.obj ⟨i⟩) (y : F.obj ⟨j⟩), c.inj i x = c.inj j y → i = j) :
    CoconeTypes.IsColimit c where
  bijective := by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := F.ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := F.ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨F.ιColimitType ⟨i⟩ y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (F) in
lemma isColimit_sigma : CoconeTypes.IsColimit (sigma F) :=
  isColimit_mk _ (by aesop)
    (fun _ _ _ h ↦ by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h ↦ congr_arg Sigma.fst h)

variable (F) in
@[simp]
def fromSigma (c : F.CofanTypes) (x : Σ (i : C), F.obj ⟨i⟩) : c.pt :=
  c.inj x.1 x.2

section

variable {c : F.CofanTypes} (hc : CoconeTypes.IsColimit c)

include hc

lemma bijective_fromSigma_of_isColimit :
    Function.Bijective c.fromSigma := by
  erw [← Function.Bijective.of_comp_iff _ (isColimit_sigma F).bijective]
  convert hc.bijective
  ext ⟨⟨i⟩, x⟩
  rfl

noncomputable def equivOfIsColimit :
    (Σ (i : C), F.obj ⟨i⟩) ≃ c.pt :=
  Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]
lemma equivOfIsColimit_apply (i : C) (x : F.obj ⟨i⟩) :
    equivOfIsColimit hc ⟨i, x⟩ = c.inj i x := rfl

@[simp]
lemma equivOfIsColimit_symm_apply (i : C) (x : F.obj ⟨i⟩) :
    (equivOfIsColimit hc).symm (c.inj i x) = ⟨i, x⟩ :=
  (equivOfIsColimit hc).injective (by simp)

lemma inj_jointly_surjective_of_isColimit (x : c.pt) :
    ∃ (i : C) (y : F.obj ⟨i⟩), c.inj i y = x := by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩

end

end CofanTypes

end Functor

end CategoryTheory
