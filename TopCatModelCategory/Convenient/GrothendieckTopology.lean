import TopCatModelCategory.Convenient.Limits
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.TopCat.Limits
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.CommSq
import TopCatModelCategory.MorphismPropertyLocally
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.Topology.Sets.Opens

universe w v t u

namespace CategoryTheory.Sieve

variable {C : Type*} [Category C] {S : C} {ι : Type*}
  {X : ι → C} (f : ∀ i, X i ⟶ S) (T : Sieve S)

lemma ofArrows_le_iff :
    Sieve.ofArrows _ f ≤ T ↔ ∀ (i : ι), T (f i) := by
  constructor
  · intro h i
    exact h _ (ofArrows_mk X f i)
  · intro h
    rintro _ _ ⟨_, _, _, ⟨i⟩, rfl⟩
    exact T.downward_closed (h i) _

end CategoryTheory.Sieve

open CategoryTheory Topology Limits

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

namespace TopCat

def openImmersions : MorphismProperty TopCat.{v} :=
  fun _ _ f ↦ IsOpenEmbedding f

lemma openImmersions_iff {Y Z : TopCat.{v}} (f : Y ⟶ Z) :
    openImmersions f ↔ IsOpenEmbedding f := Iff.rfl

lemma openImmersions.mono {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : openImmersions f) :
    Mono f where
  right_cancellation g₁ g₂ h := by
    ext x
    exact hf.injective (ConcreteCategory.congr_hom h x)

instance : openImmersions.{v}.IsMultiplicative where
  id_mem _ := IsOpenEmbedding.id
  comp_mem _ _ h₁ h₂ := h₂.comp h₁

lemma openImmersions.of_isIso {Y Z : TopCat.{v}} (f : Y ⟶ Z) [IsIso f] :
    openImmersions f :=
  (homeoOfIso (asIso f)).isOpenEmbedding

instance : (openImmersions.{v}).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ openImmersions.of_isIso f)

lemma openImmersions.exists_iso {X Y : TopCat.{v}} {f : X ⟶ Y}
    (hf : openImmersions f) :
    ∃ (U : TopologicalSpace.Opens Y) (e : X ≅ TopCat.of U),
      e.hom ≫ ofHom ⟨_, continuous_subtype_val⟩ = f := by
  refine ⟨⟨Set.range f, hf.isOpen_range⟩, isoOfHomeo hf.homeoRange, rfl⟩

instance : openImmersions.{v}.IsStableUnderBaseChange where
  of_isPullback {X₃ X₂ X₁ X₄ b r t l} sq hr := by
    obtain ⟨U, e₂, fac⟩ := hr.exists_iso
    obtain ⟨e₁, h₁, h₂⟩ := sq.exists_iso_of_isos (TopCat.isPullbackRestrictPreimage b U).flip e₂
      (Iso.refl _) (Iso.refl _) (by simpa using fac.symm) (by simp)
    dsimp at h₂
    rw [Category.comp_id] at h₂
    have h : openImmersions (ofHom ⟨_, continuous_subtype_val⟩ : of (b ⁻¹' U) ⟶ X₃) :=
      (U.isOpen.preimage b.hom.continuous).isOpenEmbedding_subtypeVal
    exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk e₁ (Iso.refl _))).2 h

section

variable {X Y : TopCat.{v}} {f : X ⟶ Y} (hf : openImmersions f) {Z : TopCat.{v}}
  (g : Z ⟶ Y) (hg : Set.range g ⊆ Set.range f)

noncomputable def openImmersions.lift : Z ⟶ X :=
  TopCat.ofHom
    (ContinuousMap.comp ⟨_, hf.homeoRange.continuous_symm⟩
      ⟨fun z ↦ ⟨g z, hg (by simp)⟩, by continuity⟩)

@[reassoc (attr := simp)]
lemma openImmersions.lift_comp : hf.lift g hg ≫ f = g := by
  ext x
  obtain ⟨y, hy⟩ := hf.homeoRange.surjective ⟨g x, hg (by simp)⟩
  dsimp [lift]
  rw [← hy, Homeomorph.symm_apply_apply]
  simpa [IsOpenEmbedding.homeoRange] using hy

@[reassoc]
lemma openImmersions.comp_lift {T : TopCat.{v}} (φ : T ⟶ Z) :
    φ ≫ hf.lift g hg = hf.lift (φ ≫ g)
      (subset_trans (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) hg) := by
  have := hf.mono
  rw [← cancel_mono f, Category.assoc, lift_comp, lift_comp]

end

end TopCat

namespace GeneratedByTopCat

def openImmersions : MorphismProperty (GeneratedByTopCat.{v} X) :=
    TopCat.openImmersions.{v}.inverseImage toTopCat

lemma openImmersions.of_isIso {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z) [IsIso f] :
    openImmersions f :=
  TopCat.openImmersions.of_isIso _

lemma openImmersions.mono {Y₁ Y₂ : GeneratedByTopCat.{v} X} {f : Y₁ ⟶ Y₂} (hf : openImmersions f) :
    Mono f where
  right_cancellation g₁ g₂ h := by
    ext x
    exact hf.injective (ConcreteCategory.congr_hom h x)

instance :
    (openImmersions.{v} (X := X)).IsMultiplicative := by
  dsimp only [openImmersions]
  infer_instance

instance : (openImmersions.{v} (X := X)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ openImmersions.of_isIso f)

section

variable {Y₁ Y₂ Z : GeneratedByTopCat.{v} X} {f : Y₁ ⟶ Y₂} (hf : openImmersions f)
  (g : Z ⟶ Y₂) (hg : Set.range g ⊆ Set.range f)

noncomputable def openImmersions.lift : Z ⟶ Y₁ := TopCat.openImmersions.lift hf g hg

@[reassoc (attr := simp)]
lemma openImmersions.lift_comp : hf.lift g hg ≫ f = g :=
  TopCat.openImmersions.lift_comp hf g hg

include hf hg in
lemma openImmersions.exists_lift : ∃ (l : Z ⟶ Y₁), l ≫ f = g :=
  ⟨hf.lift g hg, by simp⟩

@[reassoc]
lemma openImmersions.comp_lift {T : GeneratedByTopCat.{v} X} (φ : T ⟶ Z) :
    φ ≫ hf.lift g hg = hf.lift (φ ≫ g)
      (subset_trans (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) hg) :=
  TopCat.openImmersions.comp_lift _ _ _ _

@[reassoc (attr := simp)]
lemma openImmersions.lift_comp_self (g : Z ⟶ Y₁) :
    hf.lift (g ≫ f) (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) = g := by
  have := hf.mono
  rw [← cancel_mono f, lift_comp]

end

section

variable [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]

lemma openImmersions.preservesLimit_cospan {Y Z : GeneratedByTopCat.{v} X} {f : Y ⟶ Z}
    (hf : openImmersions f) ⦃T : GeneratedByTopCat.{v} X⦄ (p : T ⟶ Z) :
    PreservesLimit (cospan f p) toTopCat := by
  let c₁ : PullbackCone (toTopCat.map f) (toTopCat.map p) :=
    PullbackCone.mk _ _ pullback.condition
  let hc₁ : IsLimit c₁ := pullbackIsPullback _ _
  let e : cospan f p ⋙ (TopCat.generatedBy X).ι ≅ cospan (toTopCat.map f) (toTopCat.map p) :=
    cospanCompIso _ _ _
  let c₂ : Cone (cospan f p ⋙ (TopCat.generatedBy X).ι) := (Cones.postcompose e.inv).obj c₁
  let hc₂ : IsLimit c₂ := (IsLimit.postcomposeInvEquiv (cospanCompIso _ _ _) _).2 hc₁
  refine ObjectProperty.preservesLimit_of_limit_cone_comp_ι _ c₂ hc₂ ?_
  have hsnd : TopCat.openImmersions c₁.snd :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hf
  exact hsnd.isGeneratedBy (X := X)

instance : (openImmersions.{v} (X := X)).IsStableUnderBaseChange where
  of_isPullback {X₃ X₂ X₁ X₄ b r t l} sq hr := by
    have := hr.preservesLimit_cospan
    exact MorphismProperty.of_isPullback (P := TopCat.openImmersions)
      (sq.map toTopCat) hr

end

structure OpenCover (S : GeneratedByTopCat.{v} X) where
  ι : Type w
  U (i : ι) : GeneratedByTopCat.{v} X
  p (i : ι) : U i ⟶ S
  hp (i : ι) : openImmersions (p i)
  union_range_eq_univ :
    ⋃ (i : ι), Set.range (toTopCat.map (p i)) = .univ := by cat_disch

namespace OpenCover

variable {S : GeneratedByTopCat.{v} X}

section

variable (c : OpenCover.{w} S)

abbrev sieve : Sieve S := .ofArrows _ (fun i ↦ c.p i)

lemma exists_eq (s : toTopCat.obj S) :
    ∃ (i : c.ι) (u : toTopCat.obj (c.U i)),
      toTopCat.map (c.p i) u = s := by
  simpa [← c.union_range_eq_univ] using Set.mem_univ s

end

def id : OpenCover.{w} S where
  ι := PUnit
  U _ := S
  p _ := 𝟙 _
  hp _ := MorphismProperty.id_mem _ _

end OpenCover

variable [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]

def grothendieckTopology :
    GrothendieckTopology (GeneratedByTopCat.{v} X) where
  sieves Y S := ∃ (c : OpenCover.{v} Y), c.sieve ≤ S
  top_mem' Y := ⟨.id, by simp⟩
  pullback_stable' := by
    rintro Y Z S f ⟨c, hc⟩
    refine ⟨{
      ι := c.ι
      U := _
      p i := pullback.snd (c.p i) f
      hp i := MorphismProperty.of_isPullback (IsPullback.of_hasPullback (c.p i) f) (c.hp i)
      union_range_eq_univ := by
        ext z
        simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, Set.mem_iUnion, Set.mem_range,
          Set.mem_univ, iff_true]
        obtain ⟨i, u, hu⟩ := c.exists_eq (f z)
        obtain ⟨p, rfl, rfl⟩ := ((Types.isPullback_iff _ _ _ _).1
          ((IsPullback.of_hasPullback (c.p i) f).map (forget _))).2.2 _ _ hu
        exact ⟨i, p, rfl⟩ }, ?_⟩
    rw [Sieve.ofArrows_le_iff]
    dsimp
    intro i
    rw [← pullback.condition]
    exact hc _ (c.sieve.downward_closed (Sieve.ofArrows_mk _ _ _) _)
  transitive' := by
    rintro Y S ⟨c, hc⟩ T hT
    replace hT (i : c.ι) := hT (hc _ (Sieve.ofArrows_mk _ _ i))
    choose c' hc' using hT
    refine ⟨{
      ι := Σ (i : c.ι), (c' i).ι
      U := fun ⟨i, i'⟩ ↦ (c' i).U i'
      p := fun ⟨i, i'⟩ ↦ (c' i).p i' ≫ c.p i
      hp := fun ⟨i, i'⟩ ↦ MorphismProperty.comp_mem _ _ _ ((c' i).hp _) (c.hp _)
      union_range_eq_univ := by
        ext y
        simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, Set.mem_iUnion, Set.mem_range,
          Sigma.exists, Set.mem_univ, iff_true]
        obtain ⟨i, u, rfl⟩ := c.exists_eq y
        obtain ⟨i', v, rfl⟩ := (c' i).exists_eq u
        exact ⟨i, i', v, rfl⟩ }, ?_⟩
    rw [Sieve.ofArrows_le_iff]
    dsimp
    rintro ⟨i, i'⟩
    exact hc' i _ (Sieve.ofArrows_mk _ _ _)

lemma locallyTarget_grothendieckTopology_iff (W : MorphismProperty (GeneratedByTopCat.{v} X))
    [W.IsStableUnderBaseChange]
    {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z) :
    W.locallyTarget grothendieckTopology f ↔
      ∀ (z : Z), ∃ (U : GeneratedByTopCat.{v} X) (i : U ⟶ Z)
        (_ : openImmersions i) (_ : z ∈ Set.range i), Nonempty (W.Over f i) := by
  constructor
  · rintro ⟨U, hU⟩ z
    have := Set.mem_univ z
    rw [← U.union_range_eq_univ] at this
    simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, Set.mem_iUnion, Set.mem_range] at this
    obtain ⟨i, y, rfl⟩ := this
    exact ⟨U.U i, U.p i, U.hp i, Set.mem_range_self y, hU _ (Sieve.ofArrows_mk _ _ _)⟩
  · rintro h
    choose U p h₁ h₂ h₃ using h
    exact ⟨{
        ι := Z.obj
        U := U
        p := p
        hp := h₁ }, by rwa [Sieve.ofArrows_le_iff]⟩

lemma objectProprertyOverLocally_iff {B : (GeneratedByTopCat.{v} X)}
    (P : ObjectProperty (Over B)) [P.IsStableByPrecomp] (X : Over (B)) :
    P.overLocally grothendieckTopology X ↔ ∀ (x : X.left),
      ∃ (U : Over B) (i : U ⟶ X) (_ : openImmersions i.left)
        (_ : x ∈ Set.range i.left), P U := by
  constructor
  · rintro ⟨U, hU⟩ x
    have := Set.mem_univ x
    rw [← U.union_range_eq_univ] at this
    simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, Set.mem_iUnion, Set.mem_range] at this
    obtain ⟨i, u, rfl⟩ := this
    exact ⟨Over.mk (U.p i ≫ X.hom), Over.homMk (U.p i), U.hp i, by aesop,
      hU _ (Sieve.ofArrows_mk _ _ _)⟩
  · rintro h
    choose U p h₁ h₂ h₃ using h
    exact ⟨{
        ι := X.left
        U x := (U x).left
        p x := (p x).left
        hp := h₁ }, by simpa [Sieve.ofArrows_le_iff] using h₃⟩

end GeneratedByTopCat
