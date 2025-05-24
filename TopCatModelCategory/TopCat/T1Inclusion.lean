import TopCatModelCategory.TopCat.ClosedEmbeddings
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Basic

universe u

open CategoryTheory Topology Limits MorphismProperty Opposite

lemma Set.Nonempty.exists_min_of_wellFoundedLT
    {J : Type*} [LinearOrder J] [WellFoundedLT J] {S : Set J} (hS : S.Nonempty) :
    ∃ (m : J), m ∈ S ∧ ∀ i, i ∈ S → m ≤ i :=
  ⟨WellFounded.min (r := (· < ·)) wellFounded_lt _ hS, WellFounded.min_mem _ _ _,
    fun _ hi ↦ WellFounded.min_le wellFounded_lt hi _⟩

namespace Topology

-- This was also formalized by Reid Barton
-- Reference is [Hovey, *Model categories*, 2.4]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[mk_iff]
structure IsT₁Inclusion (f : X → Y) : Prop extends IsClosedEmbedding f where
  isClosed_singleton  (y : Y) (_ : y ∉ Set.range f) : IsClosed {y}

lemma IsT₁Inclusion.of_homeo (e : Homeomorph X Y) :
    IsT₁Inclusion e where
  toIsClosedEmbedding := Homeomorph.isClosedEmbedding e
  isClosed_singleton _ hy := by simp at hy

variable (X) in
lemma IsT₁Inclusion.id : IsT₁Inclusion (id : X → X) :=
  IsT₁Inclusion.of_homeo (Homeomorph.refl X)

lemma IsT₁Inclusion.comp {g : Y → Z} {f : X → Y}
    (hg : IsT₁Inclusion g) (hf : IsT₁Inclusion f) :
    IsT₁Inclusion (g.comp f) where
  toIsClosedEmbedding := hg.toIsClosedEmbedding.comp hf.toIsClosedEmbedding
  isClosed_singleton z hz := by
    by_cases hz' : z ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hz'
      convert
        (IsClosedEmbedding.isClosed_iff_image_isClosed hg.toIsClosedEmbedding).1
          (hf.isClosed_singleton y (by rintro ⟨x, rfl⟩; exact hz ⟨x, rfl⟩))
      aesop
    · exact hg.isClosed_singleton _ hz'

end Topology

namespace TopCat

def t₁Inclusions : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsT₁Inclusion f

lemma t₁Inclusions_le_closedEmbeddings :
    t₁Inclusions.{u} ≤ closedEmbeddings := fun _ _ _ h ↦ h.toIsClosedEmbedding

lemma t₁Inclusions_le_monomorphisms :
    t₁Inclusions.{u} ≤ monomorphisms _ := by
  intro _ _ f hf
  apply Functor.mono_of_mono_map (forget TopCat)
  rw [CategoryTheory.mono_iff_injective]
  exact hf.injective

namespace t₁Inclusions

instance : t₁Inclusions.{u}.IsMultiplicative where
  id_mem _ := IsT₁Inclusion.id _
  comp_mem _ _ hf hg := hg.comp hf

instance : t₁Inclusions.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) ↦
    IsT₁Inclusion.of_homeo (TopCat.homeoOfIso (asIso f)))

lemma isT₁Inclusion_of_isPushout
    {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b)
    (ht : IsT₁Inclusion t) :
    IsT₁Inclusion b where
  toIsClosedEmbedding := isClosedEmbedding_of_isPushout sq ht.toIsClosedEmbedding
  isClosed_singleton y hy := by
    rw [isClosed_iff_of_isPushout sq]
    constructor
    · obtain ⟨x₃, rfl⟩ | ⟨x₂, rfl, hx₂⟩ := Types.eq_or_eq_of_isPushout' (sq.flip.map (forget _)) y
      · exact (hy ⟨_, rfl⟩).elim
      · convert ht.isClosed_singleton x₂ hx₂
        ext y₂
        simp only [ConcreteCategory.forget_map_eq_coe, Set.mem_preimage, Set.mem_singleton_iff]
        refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
        obtain rfl | ⟨x₀, y₀, rfl, rfl, hxy⟩ := (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
          (sq.map (forget _)).isColimit ht.injective y₂ x₂).1 h
        · rfl
        · exact (hx₂ ⟨_, rfl⟩).elim
    · simpa only [show b ⁻¹' {y} = ∅ by aesop] using isClosed_empty

lemma isT₁Inclusion_of_isColimit_cofan
    {J : Type u'} {X₁ : J → TopCat.{u}} {X₂ : J → TopCat.{u}}
    (f : ∀ j, X₁ j ⟶ X₂ j) {c₁ : Cofan X₁} (h₁ : IsColimit c₁) {c₂ : Cofan X₂}
    (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.inj j ≫ φ = f j ≫ c₂.inj j)
    (hf : ∀ j, IsT₁Inclusion (f j)) :
    IsT₁Inclusion φ where
  toIsClosedEmbedding := isClosedEmbedding_of_isColimit f h₁ h₂ φ hφ
    (fun j ↦ (hf j).toIsClosedEmbedding)
  isClosed_singleton y hy := by
    obtain ⟨⟨i⟩, (y : X₂ i), rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) h₂) y
    rw [isClosed_iff_of_isColimit _ h₂]
    rintro ⟨j⟩
    by_cases hj : i = j
    · subst hj
      convert (hf i).isClosed_singleton y (by
        rintro ⟨x, rfl⟩
        exact hy ⟨c₁.inj i x, congr_fun ((forget _).congr_map (hφ i)) x⟩)
      convert (cofanInj_injective_of_isColimit h₂ i).preimage_image {y}
      dsimp
      simp only [Set.image_singleton, Set.singleton_eq_singleton_iff]
      rfl
    · convert isClosed_empty
      ext (x : X₂ j)
      dsimp
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hj (eq_cofanInj_apply_eq_of_isColimit h₂ _ _ h.symm)

lemma isT₁Inclusion_of_transfiniteCompositionOfShape {J : Type u'} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : t₁Inclusions.TransfiniteCompositionOfShape J f) :
    IsT₁Inclusion f where
  toIsClosedEmbedding :=
    isClosedEmbedding_of_transfiniteCompositionOfShape (hf.ofLE t₁Inclusions_le_closedEmbeddings)
  isClosed_singleton y hy := by
    let S := setOf (fun j ↦ y ∈ Set.range (hf.incl.app j))
    have hS : S.Nonempty := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) hf.isColimit) y
    obtain ⟨i, ⟨x, rfl⟩, hi⟩ := hS.exists_min_of_wellFoundedLT
    simp only [Functor.const_obj_obj, Set.mem_range,
      Set.mem_setOf_eq, forall_exists_index, S] at hi
    obtain ⟨j, hj, rfl⟩ : ∃ j, ¬IsMax j ∧ i = Order.succ j := by
      induction i using SuccOrder.limitRecOn with
      | hm j hj =>
        obtain rfl := hj.eq_bot
        refine (hy ?_).elim
        simp only [← hf.fac]
        obtain ⟨z, rfl⟩ := ((forget _).mapIso hf.isoBot.symm).toEquiv.surjective x
        exact ⟨z, rfl⟩
      | hs j hj hj' => exact ⟨j, hj, rfl⟩
      | hl j hj hj' =>
        obtain ⟨⟨k, hk⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget _) (hf.F.isColimitOfIsWellOrderContinuous j hj)) x
        exact (lt_irrefl _ (lt_of_lt_of_le hk (hi k y
          (congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE hk.le)).symm) y)))).elim
    simpa using (isClosedEmbedding_of_transfiniteCompositionOfShape
      ((hf.ici (Order.succ j)).ofLE t₁Inclusions_le_closedEmbeddings)).isClosedMap _
        ((hf.map_mem j hj).isClosed_singleton x (fun ⟨y, hy⟩ ↦
          not_le.2 (Order.lt_succ_of_not_isMax hj) (hi j y (by
            rw [← hy]
            exact congr_fun ((forget _).congr_map
              (hf.incl.naturality (homOfLE (Order.le_succ j))).symm) y))))

instance : t₁Inclusions.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isT₁Inclusion_of_isPushout sq.flip hl

instance : IsStableUnderCoproducts.{u'} t₁Inclusions.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    exact isT₁Inclusion_of_isColimit_cofan f (colimit.isColimit _)
      (colimit.isColimit _) _ (fun j ↦ colimit.ι_desc _ _) hf

instance : IsStableUnderTransfiniteComposition.{u'} t₁Inclusions.{u} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ ↦ isT₁Inclusion_of_transfiniteCompositionOfShape hf⟩

section

variable {J : Type*} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
  (hf : t₁Inclusions.TransfiniteCompositionOfShape J f) {T : TopCat.{u}}

lemma range_le_of_transfiniteCompositionOfShape (g : T ⟶ Y) :
    ∃ (j : J), Set.range g ≤ Set.range (hf.incl.app j) := by
  sorry

variable (T)

lemma preservesColimit_coyoneda_obj_of_compactSpace [CompactSpace T] :
    PreservesColimit hf.F (coyoneda.obj (op T)) :=
  preservesColimit_of_preserves_colimit_cocone hf.isColimit (by
    apply Types.FilteredColimit.isColimitOf'
    · intro g
      dsimp at g ⊢
      obtain ⟨j, hj⟩ := range_le_of_transfiniteCompositionOfShape hf g
      sorry
    · intro j g₁ g₂ hg
      have : Mono (hf.incl.app j) :=
        t₁Inclusions_le_monomorphisms _
          (isT₁Inclusion_of_transfiniteCompositionOfShape (hf.ici j))
      refine ⟨j, 𝟙 _, ?_⟩
      simpa only [Functor.comp_obj, coyoneda_obj_obj, FunctorToTypes.map_id_apply,
        ← cancel_mono (hf.incl.app j)])

end

end t₁Inclusions


end TopCat
