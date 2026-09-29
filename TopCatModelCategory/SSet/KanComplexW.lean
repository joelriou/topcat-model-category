module

public import TopCatModelCategory.SSet.FundamentalGroupoidAction

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen Simplicial

namespace SSet

namespace KanComplex

def W : MorphismProperty SSet.{u} := fun X Y f ↦
  ∃ (_ : IsFibrant X) (_ : IsFibrant Y),
    (mapFundamentalGroupoid f).IsEquivalence ∧
      ∀ (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
        Function.Bijective (mapπ f n x y h)

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma W.mk [IsFibrant X] [IsFibrant Y] (h₀₁ : (mapFundamentalGroupoid f).IsEquivalence)
    (h : ∀ (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
      Function.Bijective (mapπ f n x y h)) : W f :=
  ⟨inferInstance, inferInstance, h₀₁, h⟩

variable {f}

lemma W.isFibrant_src (hf : W f) : IsFibrant X := hf.choose

lemma W.isFibrant_tgt (hf : W f) : IsFibrant Y := hf.choose_spec.choose

lemma W.isEquivalence [IsFibrant X] [IsFibrant Y] (hf : W f) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  hf.choose_spec.choose_spec.1

lemma W.bijective (hf : W f) (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) :
    Function.Bijective (mapπ f n x y h) :=
  hf.choose_spec.choose_spec.2 n x y h

lemma W.bijective_of_iso {n : ℕ} [IsFibrant X] [IsFibrant Y]
    {x y : FundamentalGroupoid X} (e : x ≅ y)
    (hx : Function.Bijective (mapπ f n x.pt _ rfl)) :
    Function.Bijective (mapπ f n y.pt _ rfl) := by
  rw [← isIso_iff_bijective] at hx ⊢
  exact (NatTrans.isIso_app_iff_of_iso
    (FundamentalGroupoid.actionMap f n) e).1 hx

variable (f) in
lemma W.of_iso [IsIso f] [IsFibrant X] [IsFibrant Y] : W f := by
  apply W.mk
  · infer_instance
  · intro n x y h
    exact (mapπEquivOfIso (asIso f) n x y h).bijective

variable (X) in
lemma W.id [IsFibrant X] : W (𝟙 X) := W.of_iso _

variable (f) {Z : SSet.{u}} (g : Y ⟶ Z)

lemma W.comp (hf : W f) (hg : W g) : W (f ≫ g) := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  have := hg.isFibrant_tgt
  apply W.mk
  · have := hf.isEquivalence
    have := hg.isEquivalence
    exact Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g).symm
  · rintro n x _ rfl
    dsimp
    rw [← mapπ_comp_mapπ f n x _ rfl g _ rfl]
    exact (hg.bijective n _ _ rfl).comp (hf.bijective n x _ rfl)

lemma W.of_postcomp (hg : W g) (hfg : W (f ≫ g)) : W f := by
  have := hg.isFibrant_src
  have := hg.isFibrant_tgt
  have := hfg.isFibrant_src
  apply W.mk
  · have := hg.isEquivalence
    have := hfg.isEquivalence
    have := Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g)
    exact Functor.isEquivalence_of_comp_right _
      (mapFundamentalGroupoid g)
  · rintro n x _ rfl
    rw [← Function.Bijective.of_comp_iff' (hg.bijective n (f.app _ x) _ rfl),
      mapπ_comp_mapπ f n x _ rfl g _ rfl]
    exact hfg.bijective n x _ rfl

lemma W.of_precomp (hf : W f) (hfg : W (f ≫ g)) : W g := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  have := hfg.isFibrant_tgt
  apply W.mk
  · have := hf.isEquivalence
    have := hfg.isEquivalence
    have := Functor.isEquivalence_of_iso
      (compMapFundamentalGroupoidIso f g)
    exact Functor.isEquivalence_of_comp_left
      (mapFundamentalGroupoid f) _
  · rintro n y _ rfl
    have hg (x : X _⦋0⦌) : Function.Bijective (mapπ g n (f.app _ x) _ rfl) := by
      rw [← Function.Bijective.of_comp_iff _ (hf.bijective n x _ rfl),
        mapπ_comp_mapπ f n x _ rfl g _ rfl]
      exact hfg.bijective n x _ rfl
    have := hf.isEquivalence
    exact W.bijective_of_iso
      (e := (mapFundamentalGroupoid f).objObjPreimageIso _) (hg _)

lemma W.postcomp_iff (hg : W g) : W (f ≫ g) ↔ W f :=
  ⟨fun hfg ↦ W.of_postcomp _ _ hg hfg, fun hf ↦ W.comp _ _ hf hg⟩

lemma W.precomp_iff (hf : W f) : W (f ≫ g) ↔ W g :=
  ⟨fun hfg ↦ W.of_precomp _ _ hf hfg, fun hg ↦ W.comp _ _ hf hg⟩

instance : W.{u}.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := W.comp f g hf hg
  of_postcomp f g hg hfg := W.of_postcomp f g hg hfg
  of_precomp f g hf hfg := W.of_precomp f g hf hfg

lemma isFibrant_of_retract {X Y : SSet.{u}} (r : Retract X Y) [hY : IsFibrant Y] : IsFibrant X := by
  rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff] at hY ⊢
  refine MorphismProperty.of_retract ?_ hY
  exact
    { i := Arrow.homMk r.i (𝟙 _)
      r := Arrow.homMk r.r (𝟙 _) }

attribute [local simp] mapπ_mapπ

@[simps]
def retractArrowMapπ {X X' Y Y' : SSet.{u}} {f : X ⟶ X'} {g : Y ⟶ Y'} (r : RetractArrow f g)
    (n : ℕ) (x : X _⦋0⦌) (x' : X' _⦋0⦌) (hxx' : f.app _ x = x')
    (y : Y _⦋0⦌) (y' : Y' _⦋0⦌) (hyy' : g.app _ y = y') (hy : r.left.i.app _ x = y) :
    RetractArrow (C := Type _) (mapπ f n x x' hxx') (mapπ g n y y' hyy') where
  i := Arrow.homMk (mapπ r.left.i n x y hy) ((mapπ r.right.i n x' y' (by
        subst hxx' hyy' hy
        exact congr_fun (congr_app r.i_w.symm _) x)))
  r := Arrow.homMk
      (mapπ r.left.r n y x (by
        subst hy
        exact congr_fun (congr_app r.left.retract _) x))
      (mapπ r.right.r n y' x' (by
        subst hxx' hyy' hy
        have : r.left.i ≫ g ≫ r.right.r = f := by simp
        exact congr_fun (congr_app this _) x))

end KanComplex

end SSet
