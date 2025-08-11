import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.PiZero

universe u

open CategoryTheory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen MonoidalCategory CartesianMonoidalCategory

namespace SSet

variable {X Y : SSet.{u}}

namespace KanComplex

def π₀EquivπZero (x : X _⦋0⦌) : π₀ X ≃ π 0 X x where
  toFun := Quot.lift (fun a ↦ π.mk ((PtSimplex.equiv₀ x).symm a)) (by
    rintro a b ⟨s, h₀, h₁⟩
    apply Quot.sound
    dsimp
    refine ⟨{
      h := snd _ _ ≫ yonedaEquiv.symm s
      h₀ := by
        apply yonedaEquiv.injective
        simp [PtSimplex.equiv₀, ← h₀, yonedaEquiv, uliftYonedaEquiv,
          SimplicialObject.δ]
        apply congr_fun
        congr 2
        ext i
        fin_cases i
        rfl
      h₁ := by
        apply yonedaEquiv.injective
        simp [PtSimplex.equiv₀, ← h₁, yonedaEquiv, uliftYonedaEquiv,
          SimplicialObject.δ]
        apply congr_fun
        congr 2
        ext i
        fin_cases i
        rfl
      rel := by ext
    }⟩)
  invFun := Quot.lift (fun f ↦ π₀.mk (yonedaEquiv f.map)) (by
    rintro f g ⟨h⟩
    apply π₀.sound (yonedaEquiv ((stdSimplex.leftUnitor _).inv ≫ h.h))
    · rw [← h.h₀]
      apply yonedaEquiv.symm.injective
      rw [Equiv.symm_apply_apply, yonedaEquiv_symm_δ, Equiv.symm_apply_apply,
        ← ι₀_stdSimplex_zero_assoc]
    · rw [← h.h₁]
      apply yonedaEquiv.symm.injective
      rw [Equiv.symm_apply_apply, yonedaEquiv_symm_δ, Equiv.symm_apply_apply,
        ← ι₁_stdSimplex_zero_assoc])
  left_inv a := by
    obtain ⟨a, rfl⟩ := a.mk_surjective
    apply congr_arg π₀.mk
    simp [PtSimplex.equiv₀]
  right_inv f := by
    obtain ⟨f, rfl⟩ := f.mk_surjective
    apply congr_arg π.mk
    exact (PtSimplex.equiv₀ x).injective (by simp [PtSimplex.equiv₀])

@[simp]
lemma π₀EquivπZero_mk (x a : X _⦋0⦌) :
    π₀EquivπZero x (π₀.mk a) = π.mk ((PtSimplex.equiv₀ x).symm a) := rfl

lemma mapπ_comp_π₀EquivπZero
    (f : X ⟶ Y) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) :
    mapπ f 0 x y h ∘ π₀EquivπZero x =
      π₀EquivπZero y ∘ mapπ₀ f := by
  ext a
  obtain ⟨a, rfl⟩ := a.mk_surjective
  simp
  congr
  apply (PtSimplex.equiv₀ y).injective
  simp [PtSimplex.equiv₀]

lemma bijective_mapπ₀_iff_bijective_mapπ_zero (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) :
    Function.Bijective (mapπ f 0 x y h) ↔
      Function.Bijective (mapπ₀ f) := by
  rw [← Function.Bijective.of_comp_iff _ (π₀EquivπZero x).bijective]
  rw [← Function.Bijective.of_comp_iff' (π₀EquivπZero y).bijective]
  rw [mapπ_comp_π₀EquivπZero]

namespace FundamentalGroupoid

def toπ₀ (x : FundamentalGroupoid X) : π₀ X := π₀.mk x.pt

lemma toπ₀_surjective : Function.Surjective (toπ₀ (X := X)) := by
  intro p
  obtain ⟨_, rfl⟩ := p.mk_surjective
  exact ⟨_, rfl⟩

@[simp]
lemma toπ₀_mk (x : X _⦋0⦌) : toπ₀ (.mk x) = .mk x := rfl

variable [IsFibrant X]

lemma congr_toπ₀_of_hom {x y : FundamentalGroupoid X} (f : x ⟶ y) :
    toπ₀ x = toπ₀ y := by
  obtain ⟨f, rfl⟩ := homMk_surjective f
  apply π₀.sound (yonedaEquiv f.map)
  · -- this is suboptimal...
    simp only [← f.comm₀']
    dsimp only [SimplicialObject.δ]
    rw [← yonedaEquiv_map_comp]
    dsimp [yonedaEquiv, uliftYoneda, uliftYonedaEquiv, stdSimplex, uliftFunctor]
    apply congr_arg
    ext i
    fin_cases i
    rfl
  · simp only [← f.comm₁']
    dsimp only [SimplicialObject.δ]
    rw [← yonedaEquiv_map_comp]
    dsimp [yonedaEquiv, uliftYoneda, uliftYonedaEquiv, stdSimplex, uliftFunctor]
    apply congr_arg
    ext i
    fin_cases i
    rfl

lemma toπ₀_eq_toπ₀_iff (x y : FundamentalGroupoid X) :
    toπ₀ x = toπ₀ y ↔ Nonempty (x ≅ y) := by
  refine ⟨fun h ↦ ?_, fun ⟨f⟩ ↦ congr_toπ₀_of_hom f.hom⟩
  obtain ⟨x, rfl⟩ := objEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := objEquiv.symm.surjective y
  simp only [objEquiv, Equiv.coe_fn_symm_mk, toπ₀_mk] at h
  replace h := Quot.eqvGen_exact h
  induction h with
  | rel x y r =>
    obtain ⟨e, hx, hy⟩ := r
    let f : mk x ⟶ mk y := homMk (.mk (yonedaEquiv.symm e)
      (yonedaEquiv.injective (by simp [← hx, ← yonedaEquiv_symm_δ]))
      (yonedaEquiv.injective (by simp [← hy, ← yonedaEquiv_symm_δ])))
    exact ⟨asIso f⟩
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ e => exact ⟨e.some.symm⟩
  | trans _ _ _ _ _ e₁ e₂ => exact ⟨e₁.some.trans e₂.some⟩

lemma π₀_mk_eq_π₀_mk_iff (x y : X _⦋0⦌) :
    π₀.mk x = π₀.mk y ↔ Nonempty (mk x ≅ mk y) := by
  apply toπ₀_eq_toπ₀_iff

section

variable (f : X ⟶ Y) [IsFibrant Y]

lemma mapπ₀_surjective_iff :
    Function.Surjective (mapπ₀ f) ↔
      (mapFundamentalGroupoid f).EssSurj := by
  constructor
  · refine fun hf ↦ ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hf (π₀.mk y.pt)
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact ⟨.mk x, by rwa [← toπ₀_eq_toπ₀_iff]⟩
  · intro _ y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, ⟨e⟩⟩ :
        ∃ (x : X _⦋0⦌), Nonempty ((mapFundamentalGroupoid f).obj (.mk x) ≅ .mk y) :=
      ⟨_, ⟨(mapFundamentalGroupoid f).objObjPreimageIso (.mk y)⟩⟩
    exact ⟨π₀.mk x, congr_toπ₀_of_hom e.hom⟩

lemma mapπ₀_injective_iff :
    Function.Injective (mapπ₀ f) ↔
      (∀ (x x' : FundamentalGroupoid X)
        (_ : (mapFundamentalGroupoid f).obj x ≅ (mapFundamentalGroupoid f).obj x'),
        Nonempty (x ≅ x')) := by
  constructor
  · intro hf x x' e
    rw [← toπ₀_eq_toπ₀_iff]
    obtain ⟨x, rfl⟩ := objEquiv.symm.surjective x
    obtain ⟨x', rfl⟩ := objEquiv.symm.surjective x'
    apply hf
    simp only [objEquiv, Equiv.coe_fn_symm_mk, toπ₀_mk, mapπ₀_mk, π₀_mk_eq_π₀_mk_iff]
    exact ⟨e⟩
  · intro hf x x' h
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨x', rfl⟩ := x'.mk_surjective
    simp only [mapπ₀_mk] at h
    rw [π₀_mk_eq_π₀_mk_iff] at h ⊢
    exact hf _ _ h.some

lemma mapπ₀_injective_of_full [(mapFundamentalGroupoid f).Full] :
    Function.Injective (mapπ₀ f) := by
  rw [mapπ₀_injective_iff]
  intro x x' e
  exact ⟨asIso ((mapFundamentalGroupoid f).map_surjective e.hom).choose⟩

end

@[simps apply_map symm_apply_map]
def edgeEquiv {x : X _⦋0⦌} :
    Edge (.mk x) (.mk x) ≃ X.PtSimplex 1 x where
  toFun e := { map := e.map }
  invFun s := { map := s.map }
  left_inv _ := rfl
  right_inv _ := rfl

def homEquiv {x : X _⦋0⦌} : (mk x ⟶ mk x) ≃ π 1 X x where
  toFun := Quot.lift (fun e ↦ π.mk (edgeEquiv e)) (fun e₁ e₂ ⟨h⟩ ↦ by
    rw [π.mk_eq_mk_iff]
    refine ⟨PtSimplex.Homotopy.relStruct₀ ?_⟩
    exact
      { h := h.h
        h₀ := h.h₀
        h₁ := h.h₁
        rel := by apply boundary₁.hom_ext_rightTensor <;> simp })
  invFun := Quot.lift (fun s ↦ homMk (edgeEquiv.symm s)) (fun s₁ s₂ ⟨h⟩ ↦ by
    apply homMk_eq_of_homotopy
    exact
      { h := h.h
        h₀ := h.h₀
        h₁ := h.h₁
        rel := by apply boundary₁.hom_ext_rightTensor <;> simp })
  left_inv e := by
    obtain ⟨e, rfl⟩ := homMk_surjective e
    rfl
  right_inv s := by
    obtain ⟨s, rfl⟩ := s.mk_surjective
    rfl

@[simp]
lemma homEquiv_homMk {x : X _⦋0⦌} (e : Edge (.mk x) (.mk x)) :
    homEquiv (homMk e) = π.mk (edgeEquiv e) :=
  rfl

@[simp]
lemma homEquiv_symm_mk {x : X _⦋0⦌} (s : X.PtSimplex 1 x) :
    homEquiv.symm (π.mk s) = homMk (edgeEquiv.symm s) := rfl

@[simps]
def Edge.CompStruct.mulStruct {x : X _⦋0⦌} {f g fg : Edge (.mk x) (.mk x)}
    (h : Edge.CompStruct f g fg) :
    PtSimplex.MulStruct (edgeEquiv f) (edgeEquiv g) (edgeEquiv fg) 0 where
  map := h.map
  δ_map_of_gt j hj := by
    have : 2 < j.1 := by simpa [Fin.lt_iff_val_lt_val] using hj
    omega

lemma homEquiv_comp {x : X _⦋0⦌} (f g : mk x ⟶ mk x) :
    homEquiv (f ≫ g) = homEquiv f * homEquiv g := by
  obtain ⟨f, rfl⟩ := homMk_surjective f
  obtain ⟨g, rfl⟩ := homMk_surjective g
  exact (π.mul_eq_of_mulStruct (Edge.compStruct f g).mulStruct).symm

lemma homEquiv_symm_mul {x : X _⦋0⦌} (g₁ g₂ : π 1 X x) :
    homEquiv.symm (g₁ * g₂) = homEquiv.symm g₁ ≫ homEquiv.symm g₂ := by
  apply homEquiv.injective
  simp only [homEquiv_comp, Equiv.apply_symm_apply]

variable [IsFibrant Y]

lemma homEquiv_map {x : X _⦋0⦌} (φ : mk x ⟶ mk x) (f : X ⟶ Y) :
    homEquiv ((mapFundamentalGroupoid f).map φ) = mapπ f _ _ _ rfl (homEquiv φ) := by
  obtain ⟨φ, rfl⟩ := homMk_surjective φ
  aesop

lemma mapπ_comp_homEquiv (f : X ⟶ Y) (x : X _⦋0⦌) :
    mapπ f 1 x _ rfl ∘ homEquiv =
    homEquiv ∘ (mapFundamentalGroupoid f).map (X := .mk x) (Y := .mk x) := by
  ext φ
  exact (homEquiv_map φ f).symm

lemma bijective_mapπ_one_iff (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    Function.Bijective (mapπ f 1 x y h) ↔
      Function.Bijective ((mapFundamentalGroupoid f).map (X := .mk x) (Y := .mk x)) := by
  subst h
  rw [← Function.Bijective.of_comp_iff _ (homEquiv (x := x)).bijective,
    ← Function.Bijective.of_comp_iff' (homEquiv (x := f.app _ x)).bijective,
    mapπ_comp_homEquiv]
  rfl

end FundamentalGroupoid

section

variable [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)

lemma isEquivalence_mapFundamentalGroupoid_iff :
    (mapFundamentalGroupoid f).IsEquivalence ↔
      Function.Bijective (mapπ₀ f) ∧
        ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
          Function.Bijective (mapπ f 1 x y h) := by
  constructor
  · intro
    constructor
    · constructor
      · rw [FundamentalGroupoid.mapπ₀_injective_iff]
        intro _ _ e
        exact ⟨(mapFundamentalGroupoid f).preimageIso e⟩
      · rw [FundamentalGroupoid.mapπ₀_surjective_iff]
        infer_instance
    · intro x y h
      rw [FundamentalGroupoid.bijective_mapπ_one_iff]
      apply Functor.FullyFaithful.map_bijective
      apply Functor.FullyFaithful.ofFullyFaithful
  · rintro ⟨h₀, h₁⟩
    simp only [FundamentalGroupoid.bijective_mapπ_one_iff] at h₁
    have : (mapFundamentalGroupoid f).EssSurj := by
      rw [← FundamentalGroupoid.mapπ₀_surjective_iff]
      exact h₀.2
    have : (mapFundamentalGroupoid f).Faithful := ⟨by
      intro x₀ x₁ g g' h
      have e : x₁ ≅ x₀ := (asIso g).symm
      rw [← cancel_mono e.hom]
      exact (h₁ x₀.pt _ rfl).1 (by aesop)⟩
    have : (mapFundamentalGroupoid f).Full := ⟨fun {x₀ x₁} φ ↦ by
      have e : x₁ ≅ x₀ :=
        ((FundamentalGroupoid.mapπ₀_injective_iff f).1 h₀.1 _ _ (asIso φ).symm).some
      obtain ⟨g, hg⟩ := (h₁ x₀.pt _ rfl).2 (φ ≫ (mapFundamentalGroupoid f).map e.hom)
      exact ⟨g ≫ e.inv, by aesop⟩⟩
    exact { }

lemma W_iff :
    W f ↔ Function.Bijective (mapπ₀ f) ∧
      ∀ (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y),
        Function.Bijective (mapπ f (n + 1) x y h) := by
  constructor
  · intro hf
    exact ⟨((isEquivalence_mapFundamentalGroupoid_iff f).1 hf.isEquivalence).1,
      fun _ ↦ hf.bijective _⟩
  · rintro ⟨hf₀, hf⟩
    apply W.mk
    · rw [isEquivalence_mapFundamentalGroupoid_iff]
      exact ⟨hf₀, fun x y h ↦ hf 0 x y h⟩
    · rintro (_ | n)
      · intro x y h
        simpa only [bijective_mapπ₀_iff_bijective_mapπ_zero]
      · exact hf _

end

lemma W.bijective_mapπ₀ {f : X ⟶ Y} (hf : W f) : Function.Bijective (mapπ₀ f) := by
  have := hf.isFibrant_src
  have := hf.isFibrant_tgt
  rw [W_iff] at hf
  exact hf.1

lemma π₀_mk_eq_π₀_mk_iff [IsFibrant X] (x y : X _⦋0⦌) :
    π₀.mk x = π₀.mk y ↔
      Nonempty (FundamentalGroupoid.Edge (.mk x) (.mk y)) := by
  rw [FundamentalGroupoid.π₀_mk_eq_π₀_mk_iff]
  constructor
  · rintro h
    obtain ⟨e, _⟩ := FundamentalGroupoid.homMk_surjective h.some.hom
    exact ⟨e⟩
  · rintro ⟨h⟩
    exact ⟨asIso (FundamentalGroupoid.homMk h)⟩

end KanComplex

end SSet
