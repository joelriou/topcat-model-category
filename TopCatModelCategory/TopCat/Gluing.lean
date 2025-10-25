import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.TopCat.CoconeTop

universe w' w'' w v u

open CategoryTheory Topology Limits

lemma Topology.IsEmbedding.isHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) (hf' : Function.Surjective f) :
    IsHomeomorph f where
  continuous := hf.continuous
  bijective := ⟨hf.injective, hf'⟩
  isOpenMap U hU := by
    rw [hf.eq_induced] at hU
    obtain ⟨W, hW, rfl⟩ := hU
    rwa [Set.image_preimage_eq _ hf']

namespace Set

variable {X : Type u} [TopologicalSpace X]

@[simps]
def functorToTopCat : Set X ⥤ TopCat.{u} where
  obj S := TopCat.of S
  map {S T} φ := TopCat.ofHom ⟨fun ⟨x, hx⟩ ↦ ⟨x, leOfHom φ hx⟩, by continuity⟩

end Set

namespace TopCat

variable {X : TopCat.{u}} {ι : Type w} (A : Set X) (U : ι → Set X) (V : ι → ι → Set X)

structure MulticoequalizerDiagram extends CompleteLattice.MulticoequalizerDiagram A U V where
  eq_iSup_coinduced : (TopCat.of A).str = ⨆ (i : ι),
    (TopCat.of (U i)).str.coinduced (fun ⟨x, hx⟩ ↦ ⟨x, toMulticoequalizerDiagram.le i hx⟩)

namespace MulticoequalizerDiagram

variable {A U V}

section

variable (h : MulticoequalizerDiagram A U V)

nonrec abbrev multispanIndex : MultispanIndex (.prod ι) TopCat.{u} :=
  h.multispanIndex.map Set.functorToTopCat

nonrec abbrev multicofork : Multicofork h.multispanIndex :=
  h.multicofork.map Set.functorToTopCat

lemma continuous_iff {B : Type*} [TopologicalSpace B] (f : A → B) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun (⟨x, hx⟩ : U i) ↦ f ⟨x, h.le i hx⟩) := by
  change Continuous[(TopCat.of A).str, _] f ↔ _
  rw [h.eq_iSup_coinduced, continuous_iSup_dom]
  simp only [continuous_coinduced_dom]
  rfl

noncomputable def multicoforkIsColimit : IsColimit h.multicofork :=
  Multicofork.IsColimit.mk _
    (fun s ↦ ofHom ⟨(Types.isColimitMulticoforkMapSetToTypes
        h.toMulticoequalizerDiagram).desc (Multicofork.map s (forget _)), by
        rw [h.continuous_iff]
        intro i
        convert (s.ι.app (.right i)).hom.continuous using 1
        dsimp
        exact (Types.isColimitMulticoforkMapSetToTypes
          h.toMulticoequalizerDiagram).fac (Multicofork.map s (forget _)) (.right i)⟩)
    (fun s j ↦ (forget _).map_injective
      (((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram).fac
        (Multicofork.map s (forget _)) (.right j))))
    (fun s m hm ↦ (forget _).map_injective
      (Multicofork.IsColimit.hom_ext
        ((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram)) (fun j ↦
          Eq.trans (by dsimp; rw [← hm]; rfl)
            ((Types.isColimitMulticoforkMapSetToTypes h.toMulticoequalizerDiagram).fac
              (Multicofork.map s (forget _)) (.right j)).symm)))

end

lemma mk_of_isOpen (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hU : ∀ i, IsOpen (U i)) :
    TopCat.MulticoequalizerDiagram A U V where
  toMulticoequalizerDiagram := h
  eq_iSup_coinduced := by
    ext W
    simp only [isOpen_iSup_iff, isOpen_coinduced]
    let f (i : ι) : U i → A := fun ⟨x, hx⟩ ↦ ⟨x, h.le i hx⟩
    have hf (i : ι) : Continuous (f i) := by continuity
    refine ⟨fun hF i ↦ IsOpen.preimage (hf i) hF, fun hF ↦ ?_⟩
    have hf' (i : ι) : IsOpenEmbedding (f i) :=
      { toIsEmbedding := IsEmbedding.inclusion (h.le i)
        isOpen_range := by
          rw [isOpen_induced_iff]
          aesop }
    have : W = ⋃ (i : ι), (f i) '' ((f i) ⁻¹' W) := by
      ext ⟨x, hx⟩
      rw [← h.iSup_eq] at hx
      aesop
    rw [this]
    exact isOpen_iUnion (fun i ↦ (hf' i).isOpenMap _ (hF i))

lemma mk_of_isClosed [Finite ι] (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hU : ∀ i, IsClosed (U i)) :
    TopCat.MulticoequalizerDiagram A U V where
  toMulticoequalizerDiagram := h
  eq_iSup_coinduced := by
    rw [TopologicalSpace.ext_iff_isClosed]
    intro F
    simp only [isClosed_iSup_iff, isClosed_coinduced]
    let f (i : ι) : U i → A := fun ⟨x, hx⟩ ↦ ⟨x, h.le i hx⟩
    have hf (i : ι) : Continuous (f i) := by continuity
    refine ⟨fun hF i ↦ IsClosed.preimage (hf i) hF, fun hF ↦ ?_⟩
    have hf' (i : ι) : IsClosedEmbedding (f i) :=
      { toIsEmbedding := IsEmbedding.inclusion (h.le i)
        isClosed_range := by
          rw [isClosed_induced_iff]
          aesop }
    have : F = ⋃ (i : ι), (f i) '' ((f i) ⁻¹' F) := by
      ext ⟨x, hx⟩
      rw [← h.iSup_eq] at hx
      aesop
    rw [this]
    exact isClosed_iUnion_of_finite (fun i ↦ (hf' i).isClosedMap _ (hF i))

variable (h : MulticoequalizerDiagram A U V)

section

variable {Y : Type v}

lemma funext {f g : A → Y} (hfg : ∀ (i : ι) (u : U i), f ⟨u.1, h.le i u.2⟩ = g ⟨u.1, h.le i u.2⟩) :
    f = g :=
  Types.MulticoequalizerDiagram.funext h.toMulticoequalizerDiagram hfg

variable [TopologicalSpace Y]
  (f : ∀ (i : ι), U i → Y) (hf : ∀ i, Continuous (f i)) (hf' : ∀ (i j : ι) (x : V i j),
    f i ⟨x, h.le₁ i j x.2⟩ = f j ⟨x, h.le₂ i j x.2⟩)

include hf hf' in
lemma exists_desc : ∃ (φ : C(A, Y)), ∀ (i : ι) (x : U i), φ ⟨x.1, h.le i x.2⟩ = f i x := by
  obtain ⟨φ, hφ⟩ := Types.MulticoequalizerDiagram.exists_desc h.toMulticoequalizerDiagram f hf'
  refine ⟨⟨φ, ?_⟩, hφ⟩
  rw [continuous_iff h]
  simpa [hφ] using hf

noncomputable def desc : C(A, Y) := (exists_desc h f hf hf').choose

@[simp]
noncomputable def fac {i : ι} (x : U i) : desc h f hf hf' ⟨x.1, h.le i x.2⟩ = f i x :=
  (exists_desc h f hf hf').choose_spec i x

end

variable {X' : TopCat.{v}} {A' : Set X'} {U' : ι → Set X'} {V' : ι → ι → Set X'}
  (h' : MulticoequalizerDiagram A' U' V') (φ : X → X')
  (hφ₁ : ∀ (i : ι), Set.image φ (U i) = U' i)
  (hφ₂ : ∀ (i : ι), IsEmbedding (φ.comp (Subtype.val : U i → _)))
  (hφ₃ : ∀ (i j : ι), V' i j ⊆ Set.image φ (V i j))

namespace homeomorph

def hom : C(A, A') :=
  ⟨fun a ↦ ⟨φ a, by
      obtain ⟨a, ha⟩ := a
      simp only [← h.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] at ha
      obtain ⟨i, hi⟩ := ha
      apply h'.le i
      rw [← hφ₁]
      exact ⟨a, hi, rfl⟩⟩, by
    rw [continuous_iff h]
    intro i
    exact ((hφ₂ i).continuous).subtype_mk _⟩

@[simps! apply_coe]
noncomputable def homeo (i : ι) : U i ≃ₜ U' i := by
  apply IsHomeomorph.homeomorph (f := (fun ⟨u, hu⟩ ↦ ⟨φ u,
      by simpa only [← hφ₁] using ⟨u, hu, rfl⟩⟩))
  exact Topology.IsEmbedding.isHomeomorph (by
    rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact hφ₂ _) (by
    rintro ⟨u', hu'⟩
    rw [← hφ₁, Set.mem_image] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    exact ⟨⟨u, hu⟩, rfl⟩)

lemma homeo_symm_apply (x : X) (i : ι) (hx : x ∈ U i) :
    (homeo φ hφ₁ hφ₂ i).symm ⟨φ x, by simpa only [← hφ₁] using ⟨x, hx, rfl⟩⟩ = ⟨x, hx⟩ :=
  (homeo φ hφ₁ hφ₂ i).symm_apply_apply ⟨x, hx⟩

include h hφ₃ in
lemma exists_inv : ∃ (ψ : C(A', A)), ∀ (i : ι) (u' : U' i),
    (ψ ⟨u'.1, by
        simpa only [← h'.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] using ⟨i, u'.2⟩⟩).1 =
      (homeo φ hφ₁ hφ₂ i).symm u' := by
  obtain ⟨ψ, hψ⟩ :=
    exists_desc h' (Y := A)
      (fun i u' ↦ ⟨(homeo φ hφ₁ hφ₂ i).symm u', h.le i (by simp)⟩) (fun i ↦
        (Set.functorToTopCat.map (homOfLE (h.le i))).hom.continuous.comp
          (homeo φ hφ₁ hφ₂ i).symm.continuous) (fun i j ↦ by
      rintro ⟨v', hv'⟩
      obtain ⟨v, hv, rfl⟩ := hφ₃ _ _ hv'
      rw [h.min_eq] at hv
      ext
      dsimp
      rw [homeo_symm_apply _ _ _ _ _ hv.1, homeo_symm_apply _ _ _ _ _ hv.2])
  exact ⟨ψ, fun i u' ↦ by simp [hψ]⟩

noncomputable def inv : C(A', A) := (exists_inv h h' φ hφ₁ hφ₂ hφ₃).choose

lemma inv_apply (a' : A') (i : ι) (ha' : a'.1 ∈ U' i) :
    (inv h h' φ hφ₁ hφ₂ hφ₃ a').1 =
    (homeo φ hφ₁ hφ₂ i).symm ⟨a'.1, ha'⟩ :=
  (exists_inv h h' φ hφ₁ hφ₂ hφ₃).choose_spec i ⟨a'.1, ha'⟩

lemma hom_apply (a : A) : hom h h' φ hφ₁ hφ₂ a = ⟨φ a, by
  obtain ⟨a, ha⟩ := a
  rw [← h.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] at ha
  obtain ⟨i, hi⟩ := ha
  simp only [← h'.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion, ← hφ₁]
  exact ⟨i, a, hi, rfl⟩⟩ := rfl

@[simp]
lemma hom_apply_coe (a : A) : (hom h h' φ hφ₁ hφ₂ a).1 = φ a := rfl

@[simp]
lemma inv_hom_apply (a : A) :
    (inv h h' φ hφ₁ hφ₂ hφ₃) (hom h h' φ hφ₁ hφ₂ a) = a := by
  obtain ⟨a, ha⟩ := a
  simp only [← h.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] at ha
  obtain ⟨i, hi⟩ := ha
  ext
  rw [inv_apply _ _ _ _ _ _ _ i (by simpa only [hom_apply_coe, ← hφ₁] using ⟨a, hi, rfl⟩)]
  dsimp only [hom_apply_coe]
  rw [homeo_symm_apply _ _ _ _ _ hi]

@[simp]
lemma hom_inv_apply (a' : A') :
    (hom h h' φ hφ₁ hφ₂) (inv h h' φ hφ₁ hφ₂ hφ₃ a') = a' := by
  obtain ⟨a', ha'⟩ := a'
  simp only [← h'.iSup_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] at ha'
  obtain ⟨i, hi⟩ := ha'
  ext
  simp only [hom_apply_coe]
  rw [← hφ₁, Set.mem_image] at hi
  obtain ⟨x, hx, rfl⟩ := hi
  have := congr_arg (φ ∘ Subtype.val) (inv_hom_apply h h' φ hφ₁ hφ₂ hφ₃ ⟨x, h.le i hx⟩)
  rwa [hom_apply] at this

end homeomorph

@[simps! apply_coe]
noncomputable def homeomorph : A ≃ₜ A' where
  toFun := homeomorph.hom h h' φ hφ₁ hφ₂
  invFun := homeomorph.inv h h' φ hφ₁ hφ₂ hφ₃
  left_inv _ := by simp
  right_inv _ := by simp

end MulticoequalizerDiagram

end TopCat

namespace CategoryTheory.Functor.CoconeTop

lemma isColimit_of_isClosedEmbedding
    {ι : Type w} [Category ι] [Finite ι]
    {F : ι ⥤ TopCat.{u}}
    (c : CoconeTop.{v} F)
    (h₁ : ⋃ i, Set.range (c.ι i) = .univ)
    (h₂ : ∀ (i : ι), IsClosedEmbedding (c.ι i))
    (h₃ : ∀ ⦃i₁ i₂ : ι⦄ (x₁ : F.obj i₁) (x₂ : F.obj i₂),
      c.ι i₁ x₁ = c.ι i₂ x₂ →
        ∃ (j : ι) (f₁ : j ⟶ i₁) (f₂ : j ⟶ i₂) (y : F.obj j),
          F.map f₁ y = x₁ ∧ F.map f₂ y = x₂) : IsColimit c := by
  rw [isColimit_iff_toCoconeTypes_isColimit_and_coinduced]
  refine ⟨⟨fun x₁ x₂ hx ↦ ?_, fun x ↦ ?_⟩, ?_⟩
  · obtain ⟨i₁, x₁, rfl⟩ := ιColimitType_jointly_surjective _ x₁
    obtain ⟨i₂, x₂, rfl⟩ := ιColimitType_jointly_surjective _ x₂
    dsimp at hx
    obtain ⟨j, f₁, f₂, y, rfl, rfl⟩ := h₃ _ _ hx
    exact ((F ⋙ forget _).ιColimitType_map f₁ y).trans
      ((F ⋙ forget _).ιColimitType_map f₂ y).symm
  · have hx := Set.mem_univ x
    simp only [← h₁, comp_obj, Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    exact ⟨ιColimitType _ i y, rfl⟩
  · rw [TopologicalSpace.ext_iff_isClosed]
    intro Z
    rw [isClosed_iSup_iff]
    trans ∀ (i : ι), IsClosed ((c.ι i) ⁻¹' Z)
    · refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
      · exact IsClosed.preimage (c.continuous_ι i) h
      · have : Z = ⋃ (i : ι), c.ι i '' (c.ι i ⁻¹' Z) := by
          ext z
          simp only [comp_obj, Set.mem_iUnion, Set.mem_image,
            Set.mem_preimage]
          refine ⟨fun hz ↦ ?_, ?_⟩
          · have hz' := Set.mem_univ z
            rw [← h₁] at hz'
            simp only [comp_obj, Set.mem_iUnion, Set.mem_range] at hz'
            obtain ⟨i, y, rfl⟩ := hz'
            exact ⟨i, y, hz, rfl⟩
          · rintro ⟨i, x, hx, rfl⟩
            exact hx
        rw [this]
        exact isClosed_iUnion_of_finite
          (fun i ↦ (IsClosedEmbedding.isClosed_iff_image_isClosed (h₂ i)).1 (h i))
    · exact forall_congr' (fun i ↦ by simp [isClosed_coinduced])

section

variable {ι : Type u} [Category.{v} ι] {F : ι ⥤ TopCat.{w}}
  {c : CoconeTop.{w'} F} {c' : CoconeTop.{w''} F}
  (hc : c.IsColimit) (hc' : c'.IsColimit)

include hc hc' in
noncomputable def IsColimit.ptUnique : c.pt ≃ₜ c'.pt :=
  hc.homeomorph.symm.trans hc'.homeomorph

@[simp]
lemma IsColimit.ptUnique_ι
    {i : ι} (x : F.obj i) :
    (hc.ptUnique hc') (c.ι i x) = c'.ι i x := by
  simp [ptUnique]

@[simp]
lemma IsColimit.ptUnique_comp_ι (i : ι)  :
    hc.ptUnique hc' ∘ c.ι i = c'.ι i := by
  aesop

end

end CategoryTheory.Functor.CoconeTop
