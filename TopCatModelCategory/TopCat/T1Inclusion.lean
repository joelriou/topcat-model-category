import TopCatModelCategory.TopCat.ClosedEmbeddings
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms
--import Mathlib.CategoryTheory.Limits.Shapes.Types
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
structure IsClosedT₁Embedding (f : X → Y) : Prop extends IsClosedEmbedding f where
  isClosed_singleton (y : Y) (_ : y ∉ Set.range f) : IsClosed {y}

lemma IsClosedT₁Embedding.of_homeomorph (e : Homeomorph X Y) :
    IsClosedT₁Embedding e where
  toIsClosedEmbedding := Homeomorph.isClosedEmbedding e
  isClosed_singleton _ hy := by simp at hy

variable (X) in
lemma IsClosedT₁Embedding.id : IsClosedT₁Embedding (id : X → X) :=
  IsClosedT₁Embedding.of_homeomorph (Homeomorph.refl X)

lemma IsClosedT₁Embedding.comp {g : Y → Z} {f : X → Y}
    (hg : IsClosedT₁Embedding g) (hf : IsClosedT₁Embedding f) :
    IsClosedT₁Embedding (g.comp f) where
  toIsClosedEmbedding := hg.toIsClosedEmbedding.comp hf.toIsClosedEmbedding
  isClosed_singleton z hz := by
    by_cases hz' : z ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hz'
      convert
        (IsClosedEmbedding.isClosed_iff_image_isClosed hg.toIsClosedEmbedding).1
          (hf.isClosed_singleton y (by rintro ⟨x, rfl⟩; exact hz ⟨x, rfl⟩))
      aesop
    · exact hg.isClosed_singleton _ hz'

lemma IsClosedT₁Embedding.isClosed_of_finite {f : X → Y} (hf : IsClosedT₁Embedding f)
    (S : Set Y) (h : S.Finite) (h' : S ∩ Set.range f = ⊥) :
    IsClosed S := by
  have : Finite S := h
  convert isClosed_iUnion_of_finite (s := fun (i : S) ↦ {i.1}) (by
    rintro ⟨y, hy⟩
    refine hf.isClosed_singleton _ (fun hy' ↦ ?_)
    have : y ∈ (S ∩ Set.range f) := ⟨hy, hy'⟩
    simp [h'] at this)
  aesop

end Topology

namespace TopCat

abbrev closedT₁Embeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedT₁Embedding f

lemma closedT₁Embeddings_le_closedEmbeddings :
    closedT₁Embeddings.{u} ≤ closedEmbeddings := fun _ _ _ h ↦ h.toIsClosedEmbedding

lemma closedT₁Embeddings_le_monomorphisms :
    closedT₁Embeddings.{u} ≤ monomorphisms _ := by
  intro _ _ f hf
  apply Functor.mono_of_mono_map (forget TopCat)
  rw [CategoryTheory.mono_iff_injective]
  exact hf.injective

namespace closedT₁Embeddings

instance : closedT₁Embeddings.{u}.IsMultiplicative where
  id_mem _ := IsClosedT₁Embedding.id _
  comp_mem _ _ hf hg := hg.comp hf

instance : closedT₁Embeddings.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) ↦
    IsClosedT₁Embedding.of_homeomorph (TopCat.homeoOfIso (asIso f)))

lemma isClosedT₁Embedding_of_isPushout
    {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b)
    (ht : IsClosedT₁Embedding t) :
    IsClosedT₁Embedding b where
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

lemma isClosedT₁Embedding_of_isColimit_cofan
    {J : Type u'} {X₁ : J → TopCat.{u}} {X₂ : J → TopCat.{u}}
    (f : ∀ j, X₁ j ⟶ X₂ j) {c₁ : Cofan X₁} (h₁ : IsColimit c₁) {c₂ : Cofan X₂}
    (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.inj j ≫ φ = f j ≫ c₂.inj j)
    (hf : ∀ j, IsClosedT₁Embedding (f j)) :
    IsClosedT₁Embedding φ where
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

lemma isClosedT₁Embedding_of_transfiniteCompositionOfShape {J : Type u'} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedT₁Embeddings.TransfiniteCompositionOfShape J f) :
    IsClosedT₁Embedding f where
  toIsClosedEmbedding :=
    isClosedEmbedding_of_transfiniteCompositionOfShape (hf.ofLE closedT₁Embeddings_le_closedEmbeddings)
  isClosed_singleton y hy := by
    let S := setOf (fun j ↦ y ∈ Set.range (hf.incl.app j))
    have hS : S.Nonempty := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) hf.isColimit) y
    obtain ⟨i, ⟨x, rfl⟩, hi⟩ := hS.exists_min_of_wellFoundedLT
    simp only [Functor.const_obj_obj, Set.mem_range,
      Set.mem_setOf_eq, forall_exists_index, S] at hi
    obtain ⟨j, hj, rfl⟩ : ∃ j, ¬IsMax j ∧ i = Order.succ j := by
      induction i using SuccOrder.limitRecOn with
      | isMin j hj =>
        obtain rfl := hj.eq_bot
        refine (hy ?_).elim
        simp only [← hf.fac]
        obtain ⟨z, rfl⟩ := ((forget _).mapIso hf.isoBot.symm).toEquiv.surjective x
        exact ⟨z, rfl⟩
      | succ j hj hj' => exact ⟨j, hj, rfl⟩
      | isSuccLimit j hj hj' =>
        obtain ⟨⟨k, hk⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget _) (hf.F.isColimitOfIsWellOrderContinuous j hj)) x
        exact (lt_irrefl _ (lt_of_lt_of_le hk (hi k y
          (congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE hk.le)).symm) y)))).elim
    simpa using (isClosedEmbedding_of_transfiniteCompositionOfShape
      ((hf.ici (Order.succ j)).ofLE closedT₁Embeddings_le_closedEmbeddings)).isClosedMap _
        ((hf.map_mem j hj).isClosed_singleton x (fun ⟨y, hy⟩ ↦
          not_le.2 (Order.lt_succ_of_not_isMax hj) (hi j y (by
            rw [← hy]
            exact congr_fun ((forget _).congr_map
              (hf.incl.naturality (homOfLE (Order.le_succ j))).symm) y))))

instance : closedT₁Embeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isClosedT₁Embedding_of_isPushout sq.flip hl

instance : IsStableUnderCoproducts.{u'} closedT₁Embeddings.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    exact isClosedT₁Embedding_of_isColimit_cofan f (colimit.isColimit _)
      (colimit.isColimit _) _ (fun j ↦ colimit.ι_desc _ _) hf

instance : IsStableUnderTransfiniteComposition.{u'} closedT₁Embeddings.{u} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ ↦ isClosedT₁Embedding_of_transfiniteCompositionOfShape hf⟩

lemma isClosed_of_subsingleton_compl {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedT₁Embeddings f) {Z : Set Y} (hZ : IsClosed (f ⁻¹' Z))
    (hZ' : Subsingleton ((Set.range f)ᶜ ∩ Z : Set _)) : IsClosed Z := by
  rw [show Z = f '' (f ⁻¹' Z) ∪ ((Set.range f)ᶜ ∩ Z) by grind]
  refine IsClosed.union (hf.1.isClosedMap _ hZ) ?_
  by_cases h : ((Set.range ⇑(ConcreteCategory.hom f))ᶜ ∩ Z).Nonempty
  · obtain ⟨x, hx, hx'⟩ := h
    convert hf.isClosed_singleton _ hx
    aesop
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact isClosed_empty

section

variable {J : Type*} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
  (hf : closedT₁Embeddings.TransfiniteCompositionOfShape J f) {T : TopCat.{u}}
  [CompactSpace T]

lemma range_le_of_transfiniteCompositionOfShape (g : T ⟶ Y) :
    ∃ (j : J), Set.range g ⊆ Set.range (hf.incl.app j) := by
  by_contra!
  simp only [Set.subset_def, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, not_forall, not_exists] at this
  let R (j : J) : Set Y := Set.range (hf.incl.app j)
  have hR : Monotone R := by
    rintro j j' hjj' _ ⟨x, rfl⟩
    exact ⟨hf.F.map (homOfLE hjj') x,
      congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE hjj'))) x⟩
  have (j : J) : ∃ (j' : J) (y : Y) (hy : y ∈ Set.range g)
      (hj' : y ∈ R j'), y ∉ R j := by
    obtain ⟨t, ht⟩ := this j
    obtain ⟨j', z, hz⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) hf.isColimit) (g t)
    exact ⟨j', g t, by simp, ⟨z, hz⟩, by simpa [R] using ht⟩
  obtain ⟨j, hj₀, y, hy₁, hy₂, hy₃⟩ :
      ∃ (j : ℕ → J) (hj₀ : j 0 = ⊥) (y : ℕ → Y), (Set.range y ⊆ Set.range g) ∧
        (∀ (n : ℕ), y n ∈ R (j (n + 1))) ∧ (∀ (n : ℕ), y n ∉ R (j n)) := by
    let s (j : J) : J := (this j).choose
    let y (j : J) : Y := (this j).choose_spec.choose
    have hy₁ (j : J) : y j ∈ Set.range g := (this j).choose_spec.choose_spec.choose
    have hy₂ (j : J) : y j ∈ R (s j) := (this j).choose_spec.choose_spec.choose_spec.choose
    have hy₃ (j : J) : y j ∉ R j := (this j).choose_spec.choose_spec.choose_spec.choose_spec
    let j (n : ℕ) : J := Nat.iterate s n ⊥
    have hj (n : ℕ) : j (n + 1) = s (j n) := by
      rw [add_comm]
      exact congr_fun (Function.iterate_add s 1 n) ⊥
    exact ⟨j, rfl, fun n ↦ y (j n), by rintro _ ⟨n, rfl⟩; apply hy₁,
      fun n ↦ by simpa only [hj] using hy₂ (j n), fun n ↦ hy₃ (j n)⟩
  have hj : StrictMono j := strictMono_nat_of_lt_succ (fun n ↦ by
    by_contra!
    exact hy₃ n (hR this (hy₂ n)))
  have hy₄ : Function.Injective y := by
    intro a b h
    wlog hab : a ≤ b generalizing a b
    · exact (this h.symm (not_le.1 hab).le).symm
    obtain ⟨k, hk⟩ := Nat.le.dest hab
    obtain _ | k := k
    · simpa using hk
    · refine (hy₃ b ?_).elim
      rw [← h]
      exact hR (hj.monotone (by omega)) (hy₂ a)
  let c := closedEmbeddings.coconeOfTransfiniteCompositionOfShape
    (hf.ofLE closedT₁Embeddings_le_closedEmbeddings) hj
  have hc : IsColimit c := closedEmbeddings.isColimitCoconeOfTransfiniteCompositionOfShape
      (hf.ofLE closedT₁Embeddings_le_closedEmbeddings) hj
  let Z : Set Y := ⋃ (n : ℕ), R (j n)
  let ι : Z → Y := Subtype.val
  have hι : IsClosedEmbedding ι :=
    closedEmbeddings.coconeOfTransfiniteCompositionOfShape.closedEmbeddings_ιPoint
      (hf.ofLE closedT₁Embeddings_le_closedEmbeddings) hj
  have hy₅ : Set.range y ⊆ Z := by
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_iUnion, Z]
    exact ⟨_, hy₂ n⟩
  have hZ' (A : Set Y) (hA : A ⊆ Z) :
      IsClosed A ↔ ∀ (n : ℕ), IsClosed (A ∩ R (j n)) := by
    rw [hι.isClosed_iff_preimage_isClosed (hA.trans (by simp [ι])),
      isClosed_iff_of_isColimit _ hc]
    refine forall_congr' (fun n ↦ ?_)
    have hn : IsClosedEmbedding (hf.incl.app (j n)) :=
      (isClosedT₁Embedding_of_transfiniteCompositionOfShape (hf.ici (j n))).toIsClosedEmbedding
    have : (c.ι.app n) ⁻¹' (ι ⁻¹' A) = (hf.incl.app (j n)) ⁻¹' (A ∩ R (j n)) := by
      ext x
      constructor
      · rintro hx
        exact ⟨hx, by simp [R]⟩
      · rintro ⟨hx, _⟩
        exact hx
    rw [hn.isClosed_iff_preimage_isClosed Set.inter_subset_right, this]
  have hy₆ (S : Set Y) (hS : S ⊆ Set.range y) : IsClosed S := by
    rw [hZ' _ (hS.trans hy₅)]
    intro n
    apply (isClosedT₁Embedding_of_transfiniteCompositionOfShape hf).isClosed_of_finite
    · let S₀ := Set.range (fun (i : Fin n) ↦ y i.1)
      have : S₀.Finite := Set.finite_range _
      have h : S ∩ R (j n) ⊆ S₀ := by
        rintro t ⟨h₁, h₂⟩
        obtain ⟨i, rfl⟩ := hS h₁
        by_cases hi : i < n
        · exact ⟨⟨i, hi⟩, rfl⟩
        · simp only [not_lt] at hi
          exact (hy₃ _ (hR (hj.monotone hi) h₂)).elim
      let φ : (S ∩ R (j n) : Set _) → S₀ := fun x ↦ ⟨x, h x.2⟩
      exact Finite.of_injective φ (fun _ _ h ↦ by rwa [Subtype.ext_iff] at h ⊢)
    · ext z
      simp only [Set.mem_inter_iff, Set.bot_eq_empty, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨h₁, h₂⟩, h₃⟩
      obtain ⟨m, rfl⟩ := hS h₁
      have : Set.range f ≤ R (j 0) := by
        simp only [Functor.const_obj_obj, hj₀, Set.le_eq_subset, R]
        rintro _ ⟨x, rfl⟩
        exact ⟨hf.isoBot.inv x, congr_fun ((forget _).congr_map hf.fac) x⟩
      exact hy₃ m (hR (hj.monotone (Nat.zero_le m)) (this h₃))
  have hy₇ : DiscreteTopology (Set.range y) := by
    rw [discreteTopology_iff_forall_isClosed]
    intro A
    rw [isClosed_induced_iff]
    exact ⟨Subtype.val '' A, hy₆ _ (by simp), by simp⟩
  have : CompactSpace (Set.range y) := by
    rw [← isCompact_iff_compactSpace]
    convert (IsCompact.image isCompact_univ g.hom.continuous).inter_right
      (hy₆ _ (subset_refl _))
    exact (Set.inter_eq_self_of_subset_right (by simpa using hy₁)).symm
  have : Finite (Set.range y) := finite_of_compact_of_discrete
  have : Infinite (Set.range y) :=
    Infinite.of_injective (fun (n : ℕ) ↦ ⟨y n, by simp⟩)
      (Function.Injective.of_comp (f := Subtype.val) hy₄)
  exact not_finite (Set.range y)

variable (T)

lemma preservesColimit_coyoneda_obj_of_compactSpace :
    PreservesColimit hf.F (coyoneda.obj (op T)) :=
  preservesColimit_of_preserves_colimit_cocone hf.isColimit (by
    apply Types.FilteredColimit.isColimitOf'
    · intro g
      dsimp at g ⊢
      obtain ⟨j, hj⟩ := range_le_of_transfiniteCompositionOfShape hf g
      let g' : T ⟶ .of (Set.range (hf.incl.app j)) :=
        ofHom ⟨fun t ↦ ⟨g t, hj (by aesop)⟩, by continuity⟩
      exact ⟨j, g' ≫ (TopCat.isoOfHomeo
        (isClosedT₁Embedding_of_transfiniteCompositionOfShape (hf.ici j)).homeomorphRange).inv,
          by aesop⟩
    · intro j g₁ g₂ hg
      have : Mono (hf.incl.app j) :=
        closedT₁Embeddings_le_monomorphisms _
          (isClosedT₁Embedding_of_transfiniteCompositionOfShape (hf.ici j))
      refine ⟨j, 𝟙 _, ?_⟩
      simpa only [Functor.comp_obj, coyoneda_obj_obj, FunctorToTypes.map_id_apply,
        ← cancel_mono (hf.incl.app j)])

end

end closedT₁Embeddings

end TopCat
