import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.SmallObject
import TopCatModelCategory.TopCat.ToTopSdIso
import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.SmallObject
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Topology.Sets.OpenCover

open CategoryTheory Simplicial HomotopicalAlgebra Limits

universe u

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma HasLiftingPropertyFixedBot.ofArrowIso {A B A' B' : C} {f : A ⟶ B} {f' : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk f') {X Y : C} {p : X ⟶ Y} {b : B ⟶ Y}
    (h : HasLiftingPropertyFixedBot f' p (e.inv.right ≫ b)):
    HasLiftingPropertyFixedBot f p b := by
  intro t sq
  have h₂ := e.hom.w
  dsimp at h₂
  have sq' : CommSq (e.inv.left ≫ t) f' p (e.inv.right ≫ b) := ⟨by simp [sq.w]⟩
  have := h (e.inv.left ≫ t) sq'
  exact ⟨⟨{
    l := e.hom.right ≫ sq'.lift
    fac_left := by
      rw [← reassoc_of% h₂, sq'.fac_left, Arrow.hom_inv_id_left_assoc]
  }⟩⟩

lemma HasLiftingPropertyFixedBot.of_coproduct {ι : Type*} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i)
    {cofan₁ : Cofan A} {cofan₂ : Cofan B} (h₁ : IsColimit cofan₁)
    (h₂ : IsColimit cofan₂) (φ : cofan₁.pt ⟶ cofan₂.pt)
    (hφ : ∀ i, cofan₁.inj i ≫ φ = f i ≫ cofan₂.inj i)
    {X Y : C} (p : X ⟶ Y) (b : cofan₂.pt ⟶ Y)
    (h : ∀ i, HasLiftingPropertyFixedBot (f i) p (cofan₂.inj i ≫ b)) :
    HasLiftingPropertyFixedBot φ p b := by
  intro t sq
  have sq' (i : ι) : CommSq (cofan₁.inj i ≫ t) (f i) p (cofan₂.inj i ≫ b) := ⟨by
    rw [Category.assoc, sq.w, reassoc_of% hφ]⟩
  have (i : ι) := h _ _ (sq' i)
  exact ⟨⟨{
    l := Cofan.IsColimit.desc h₂ (fun i ↦ (sq' i).lift)
    fac_left := Cofan.IsColimit.hom_ext h₁ _ _ (fun i ↦ by simp [reassoc_of% hφ])
    fac_right := Cofan.IsColimit.hom_ext h₂ _ _ (fun i ↦ by simp)
  }⟩⟩

lemma IsPushout.hasLiftingPropertyFixedBot
    {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) {Y Z : C} {p : Y ⟶ Z} {β : X₄ ⟶ Z}
    (h : HasLiftingPropertyFixedBot l p (b ≫ β) ) :
    HasLiftingPropertyFixedBot r p β := by
  intro θ s
  have s' : CommSq (t ≫ θ) l p (b ≫ β) := ⟨by rw [Category.assoc, s.w, sq.w_assoc]⟩
  have := h (t ≫ θ) s'
  exact ⟨⟨{
    l := sq.desc θ s'.lift (by simp)
    fac_right := sq.hom_ext (by simp [s.w]) (by simp) }⟩⟩

end CategoryTheory

namespace SSet

open modelCategoryQuillen SmallObject

namespace anodyneExtensions

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

variable {X Y E B : SSet.{u}} {i : X ⟶ Y}

open HasLiftingProperty.transfiniteComposition in
lemma hasLiftingPropertyFixedBot_of_simplices_aux
    {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
    (hi : RelativeCellComplex.{u} (fun (_ : α) ↦ J.homFamily) i)
    (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ ⦃n : ℕ⦄ (σ : Δ[n + 1] ⟶ Y) (i : Fin (n + 2)),
      HasLiftingPropertyFixedBot (horn (n + 1) i).ι p (σ ≫ b)) :
    HasLiftingPropertyFixedBot i p b := by
  have : HasLiftingPropertyFixedBot (hi.incl.app ⊥) p b :=
    hasLiftingPropertyFixedBot_ι_app_bot hi.isColimit (fun j hj ↦ by
      let H := hi.attachCells j hj
      apply H.isPushout.hasLiftingPropertyFixedBot
      refine HasLiftingPropertyFixedBot.of_coproduct H.isColimit₁
        H.isColimit₂ (f := fun j ↦ (H.π j).1.hom) H.m H.hm _ _ (fun a ↦ ?_)
      · dsimp
        obtain ⟨n, i, ⟨e⟩⟩ : ∃ (n : ℕ) (i : Fin (n + 2)),
            Nonempty (Arrow.mk (H.π a).1.hom ≅ Arrow.mk (horn _ i).ι) := by
          have : Arrow.mk _ ∈ _ := (H.π a).2
          dsimp [J] at this
          rw [MorphismProperty.arrow_mk_mem_toSet_iff] at this
          simp only [MorphismProperty.iSup_iff] at this
          obtain ⟨n, hn⟩ := this
          rw [MorphismProperty.ofHoms_iff] at hn
          obtain ⟨j, hj⟩ := hn
          exact ⟨n, j, ⟨eqToIso hj⟩⟩
        apply HasLiftingPropertyFixedBot.ofArrowIso e
        simp only [← Category.assoc]
        apply h)
  intro t sq
  have sq' : CommSq (hi.isoBot.hom ≫ t) (hi.incl.app ⊥) p b := ⟨by
    rw [Category.assoc, sq.w]
    simp only [← hi.fac]
    rw [Category.assoc, Iso.hom_inv_id_assoc]⟩
  have := this _ sq'
  exact ⟨⟨{
    l := sq'.lift
    fac_left := by
      simp only [← hi.fac]
      rw [← cancel_epi (hi.isoBot.hom), Category.assoc, Iso.hom_inv_id_assoc,
        sq'.fac_left]
  }⟩⟩

lemma hasLiftingPropertyFixedBot_of_simplices
    (hi : anodyneExtensions i) (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ ⦃n : ℕ⦄ (σ : Δ[n + 1] ⟶ Y) (i : Fin (n + 2)),
      HasLiftingPropertyFixedBot (horn (n + 1) i).ι p (σ ≫ b)) :
    HasLiftingPropertyFixedBot i p b := by
  replace hi : J.rlp.llp i := fun _ _ p hp ↦ hi _ (by rwa [fibrations_eq])
  obtain ⟨Y', r, i', fac, ⟨hi'⟩⟩ :=
    exists_retract_relativeCellComplex_of_llp_rlp hi Cardinal.aleph0.{u}
  replace hi' := hasLiftingPropertyFixedBot_of_simplices_aux hi' p (r.r ≫ b) (by
    intro n u i
    rw [← Category.assoc]
    apply h)
  intro t sq
  have sq' : CommSq t i' p (r.r ≫ b) := ⟨by
    rw [sq.w, ← reassoc_of% fac, reassoc_of% r.retract]⟩
  have := hi' t sq'
  exact ⟨⟨
    { l := r.i ≫ sq'.lift
      fac_left := by rw [reassoc_of% fac, sq'.fac_left] } ⟩⟩

end anodyneExtensions

end SSet

namespace TopCat

open Topology TopologicalSpace modelCategory SSet

variable {E B : TopCat.{u}} (p : E ⟶ B)

lemma isPullbackRestrictPreimage (U : Set B) :
    IsPullback (ofHom ⟨_, continuous_subtype_val⟩) (ofHom (p.hom.restrictPreimage U)) p
      (ofHom ⟨_, continuous_subtype_val⟩) where
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ ofHom ⟨fun x ↦ ⟨s.fst x, by
      simp only [Set.mem_preimage]
      have := ConcreteCategory.congr_hom s.condition x
      convert (s.snd x).2⟩, by continuity⟩)
    (fun s ↦ rfl)
    (fun s ↦ by
      ext x
      exact ConcreteCategory.congr_hom s.condition x)
    (fun s m hm₁ hm₂ ↦ by
      ext x
      exact ConcreteCategory.congr_hom hm₁ x)⟩

def IsSerreFibrationOver (U : Set B) : Prop :=
  ∀ ⦃n : ℕ⦄ (i : Fin (n + 2)) (f : |Δ[n + 1]| ⟶ B),
    Set.range f ⊆ U → HasLiftingPropertyFixedBot (toTop.map (horn _ i).ι) p f

lemma IsSerreFibrationOver.iff_fibration (U : Set B) :
    IsSerreFibrationOver p U ↔ Fibration (ofHom (p.hom.restrictPreimage U)) := by
  let p' := ofHom (p.hom.restrictPreimage U)
  let ι : of U ⟶ B := ofHom ⟨_, continuous_subtype_val⟩
  let ι' : of (p ⁻¹' U) ⟶ E := ofHom ⟨_, continuous_subtype_val⟩
  change _ ↔ Fibration p'
  constructor
  · intro hp
    rw [fibration_iff_rlp]
    intro n i
    constructor
    intro t b sq
    have sq' : CommSq (t ≫ ι') (toTop.map Λ[n + 1, i].ι) p (b ≫ ι) := ⟨by
      ext x
      exact Subtype.ext_iff.1 (ConcreteCategory.congr_hom sq.w x)⟩
    have := hp i _ (by dsimp [ι]; grind) _ sq'
    exact ⟨⟨{
      l := ofHom ⟨fun x ↦ ⟨sq'.lift x, by
        simp only [Set.mem_preimage]
        convert (b x).2
        exact ConcreteCategory.congr_hom sq'.fac_right x⟩, by continuity⟩
      fac_left := by
        ext x
        exact ConcreteCategory.congr_hom sq'.fac_left x
      fac_right := by
        ext x
        exact ConcreteCategory.congr_hom sq'.fac_right x
    }⟩⟩
  · intro _ n i f hf t sq
    let f' : toTop.obj Δ[n + 1] ⟶ of U :=
      ofHom ⟨fun x ↦ ⟨f x, hf (by simp)⟩, by continuity⟩
    let t' : toTop.obj Λ[n + 1, i].toSSet ⟶ of (p ⁻¹' U) :=
      ofHom ⟨fun y ↦ ⟨t y, by
        simp
        erw [ConcreteCategory.congr_hom sq.w y]
        apply hf
        simp
        tauto⟩, by continuity⟩
    have sq' : CommSq t' (toTop.map Λ[n + 1, i].ι) p' f' := ⟨by
      ext
      apply ConcreteCategory.congr_hom sq.w⟩
    have := sq'.lift
    exact ⟨⟨{
      l := sq'.lift ≫ ι'
      fac_left := by rw [sq'.fac_left_assoc]; rfl
      fac_right := by
        ext y
        exact Subtype.ext_iff.1 (ConcreteCategory.congr_hom sq'.fac_right y)
    }⟩⟩

variable {p} in
lemma fibration_of_isSerreFibrationOver_univ
    (hp : IsSerreFibrationOver p .univ) : Fibration p := by
  rw [fibration_iff_rlp]
  intro n i
  constructor
  intro t b sq
  exact hp _ _ (by simp) _ _

namespace fibration_of_isOpenCover

variable {p} {ι : Type*} {U : ι → Opens B} (hU : IsOpenCover U)
  (hp : ∀ i, IsSerreFibrationOver p (U i))
  {n : ℕ} (b : |Δ[n + 1]| ⟶ B) (i : Fin (n + 2))

include hU hp

lemma exists_iter :
    ∃ (r : ℕ), HasLiftingPropertyFixedBot
        (toTop.map ((sd.iter r).map (horn _ i).ι)) p
          ((toTopSdIterIso Δ[n + 1] r).hom ≫ b) := by
  let b' : C(⦋n + 1⦌.toTopObj, B) :=
    ⟨b ∘ ⦋n + 1⦌.toTopHomeo.symm, by continuity⟩
  have hV := hU.comap b'
  have := hp
  sorry

lemma hasLiftingPropertyFixedBot  :
    HasLiftingPropertyFixedBot (toTop.map (horn _ i).ι) p b := by
  obtain ⟨r, hr⟩ := exists_iter hU hp b i
  exact .ofArrowIso (toTopSdIterArrowIso.{u} (horn _ i).ι r).symm hr

end fibration_of_isOpenCover

variable {p}

lemma fibration_of_isOpenCover
    {ι : Type*} {U : ι → Opens B} (hU : IsOpenCover U)
    (hp : ∀ i, IsSerreFibrationOver p (U i)) : Fibration p := by
  rw [fibration_iff_rlp]
  intro n i
  constructor
  intro t b sq
  exact fibration_of_isOpenCover.hasLiftingPropertyFixedBot hU hp b i _ sq

end TopCat
