import TopCatModelCategory.SSet.Homotopy

universe u

open CategoryTheory MonoidalCategory Simplicial ChosenFiniteProducts
  HomotopicalAlgebra SSet.modelCategoryQuillen Limits Opposite
  MonoidalClosed

namespace SSet

variable {E E' B : SSet.{u}} (p : E ⟶ B) (p' : E' ⟶ B)

@[ext]
structure FiberwiseHomotopy  (f g : E ⟶ E') extends Homotopy f g where
  fac : toHomotopy.h ≫ p' = fst _ _ ≫ p

namespace FiberwiseHomotopy

attribute [reassoc (attr := simp)] fac

section

variable {p p'} {f g : E ⟶ E'} (h : FiberwiseHomotopy p p' f g)

include h

@[reassoc]
lemma fac₀ : f ≫ p' = p := by
  simpa only [Category.assoc, h.fac,
    ι₀_fst_assoc, Subcomplex.RelativeMorphism.botEquiv_symm_apply_map] using h.h₀.symm =≫ p'

@[reassoc]
lemma fac₁ : g ≫ p' = p := by
  simpa only [Category.assoc, h.fac,
    ι₀_fst_assoc, Subcomplex.RelativeMorphism.botEquiv_symm_apply_map] using h.h₁.symm =≫ p'

end

variable {f f'} in
@[simps!]
noncomputable def refl (hf : f ≫ p' = p) : FiberwiseHomotopy p p' f f where
  toHomotopy := .refl _
  fac := by simp [hf]

end FiberwiseHomotopy

lemma fiberwiseHom_commSq : CommSq (initial.to _) (initial.to _) p' p := ⟨by simp⟩

noncomputable def fiberwiseHom : ((ihom E).obj E').Subcomplex :=
  ihomToPullbackFiber (fiberwiseHom_commSq p p')

lemma range_le_fiberwiseHom_iff {T : SSet.{u}} (φ : T ⟶ (ihom E).obj E') :
    Subcomplex.range φ ≤ fiberwiseHom p p' ↔
      φ ≫ (ihom E).map p' = SSet.const (ihom₀Equiv.symm p) :=
  (range_le_ihomToPullbackFiber_iff _ _).trans (by
    simp only [and_iff_right_iff_imp]
    intro
    apply uncurry_injective
    rw [← cancel_epi (β_ _ _).hom]
    apply curry_injective
    apply initialIsInitial.hom_ext)

lemma le_fiberwiseHom_iff (Z : ((ihom E).obj E').Subcomplex) :
    Z ≤ fiberwiseHom p p' ↔
      Z.ι ≫ (ihom E).map p' = SSet.const (ihom₀Equiv.symm p) :=
  (le_ihomToPullbackFiber_iff _ _).trans (by
    simp only [and_iff_right_iff_imp]
    intro
    have : (pre (initial.to E)).app E' = const (ihom₀Equiv.symm (initial.to E')) := by
      apply uncurry_injective
      rw [← cancel_epi (β_ _ _).hom]
      apply curry_injective
      apply initialIsInitial.hom_ext
    simp [this])

@[reassoc (attr := simp)]
lemma fiberwiseHom_ι_ihom_map :
    (fiberwiseHom p p').ι ≫ (ihom E).map p' = SSet.const (ihom₀Equiv.symm p) := by
  rw [← le_fiberwiseHom_iff]

instance [Fibration p'] : IsFibrant (fiberwiseHom p p' : SSet) := by
  dsimp [fiberwiseHom]
  infer_instance

lemma ihom₀Equiv_symm_mem_fiberwiseHom_obj_zero_iff (f : E ⟶ E') :
    ihom₀Equiv.symm f ∈ (fiberwiseHom p p').obj (op ⦋0⦌) ↔ f ≫ p' = p :=
  (ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff _ _).trans (by simp)

variable {p p'} in
@[simps]
noncomputable def fiberwiseHomMk (f : E ⟶ E') (hf : f ≫ p' = p) :
    (fiberwiseHom p p' : SSet) _⦋0⦌ :=
  ⟨ihom₀Equiv.symm f, by rwa [ihom₀Equiv_symm_mem_fiberwiseHom_obj_zero_iff]⟩

namespace FiberwiseHomotopy

open KanComplex.FundamentalGroupoid

section

variable {p p'} {f : E ⟶ E'} (hf : f ≫ p' = p) {g : E ⟶ E'} (hg : g ≫ p' = p)

namespace equiv

@[simps! map]
noncomputable def toFun (h : FiberwiseHomotopy p p' f g) :
    Edge (.mk (fiberwiseHomMk f hf)) (.mk (fiberwiseHomMk g hg)) :=
  Edge.mk (Subcomplex.lift (curry h.h) (by
    simp only [Subcomplex.preimage_eq_top_iff,
      range_le_fiberwiseHom_iff]
    rw [← curry_natural_right, h.fac]
    rfl)) (by
    ext : 1
    rw [Category.assoc, Subcomplex.lift_ι, const_comp, Subpresheaf.ι_app,
      fiberwiseHomMk_coe]
    apply uncurry_injective
    rw [← cancel_epi (stdSimplex.rightUnitor _).inv,
      uncurry_natural_left, uncurry_curry,
      stdSimplex.rightUnitor_inv_map_δ_one_assoc, h.h₀,
      Subcomplex.RelativeMorphism.botEquiv_symm_apply_map]
    rfl) (by
    ext : 1
    rw [Category.assoc, Subcomplex.lift_ι, const_comp, Subpresheaf.ι_app,
      fiberwiseHomMk_coe]
    apply uncurry_injective
    rw [← cancel_epi (stdSimplex.rightUnitor _).inv,
      uncurry_natural_left, uncurry_curry,
      stdSimplex.rightUnitor_inv_map_δ_zero_assoc, h.h₁,
      Subcomplex.RelativeMorphism.botEquiv_symm_apply_map]
    rfl)

variable {hf hg}
@[simps]
noncomputable def invFun
    (h : Edge (.mk (fiberwiseHomMk f hf)) (.mk (fiberwiseHomMk g hg))) :
    FiberwiseHomotopy p p' f g where
  h := uncurry (h.map ≫ Subcomplex.ι _)
  h₀ := by
    rw [Subcomplex.RelativeMorphism.botEquiv_symm_apply_map,
      ← cancel_epi (stdSimplex.rightUnitor _).hom,
      stdSimplex.rightUnitor_hom_ι₀_assoc,
      ← uncurry_natural_left, h.comm₀_assoc,
      const_comp, Subpresheaf.ι_app, fiberwiseHomMk_coe]
    rfl
  h₁ := by
    rw [Subcomplex.RelativeMorphism.botEquiv_symm_apply_map,
      ← cancel_epi (stdSimplex.rightUnitor _).hom,
      stdSimplex.rightUnitor_hom_ι₁_assoc,
      ← uncurry_natural_left, h.comm₁_assoc,
      const_comp, Subpresheaf.ι_app, fiberwiseHomMk_coe]
    rfl
  rel := by
    ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx
  fac := by
    dsimp
    rw [← uncurry_natural_right]
    aesop

end equiv

noncomputable def equiv : FiberwiseHomotopy p p' f g ≃
    Edge (.mk (fiberwiseHomMk f hf)) (.mk (fiberwiseHomMk g hg)) where
  toFun := equiv.toFun hf hg
  invFun := equiv.invFun
  left_inv _ := by aesop
  right_inv _ := by aesop

end

variable {p p'} {f₀ f₁ f₂ : E ⟶ E'}

noncomputable def symm [Fibration p'] (h : FiberwiseHomotopy p p' f₀ f₁) :
    FiberwiseHomotopy p p' f₁ f₀ :=
  (equiv h.fac₁ h.fac₀).symm (equiv h.fac₀ h.fac₁ h).inv

noncomputable def trans [Fibration p'] (h₀₁ : FiberwiseHomotopy p p' f₀ f₁)
    (h₁₂ : FiberwiseHomotopy p p' f₁ f₂) :
    FiberwiseHomotopy p p' f₀ f₂ :=
  (equiv h₀₁.fac₀ h₁₂.fac₁).symm
    ((equiv h₀₁.fac₀ h₀₁.fac₁ h₀₁).comp (equiv h₁₂.fac₀ h₁₂.fac₁ h₁₂))

end FiberwiseHomotopy

end SSet
