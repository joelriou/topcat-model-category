import TopCatModelCategory.SSet.KanComplexW
import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.DeformationRetract

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen
  ChosenFiniteProducts MonoidalCategory

namespace SSet

namespace stdSimplex

@[reassoc (attr := simp)]
lemma δ_one_ι₀ :
    stdSimplex.δ (1 : Fin 2) ≫ ι₀ =
      SSet.const (prodStdSimplex.obj₀Equiv.symm ⟨0, 0⟩) :=
  yonedaEquiv.injective (Prod.ext (by ext i; fin_cases i; rfl) (by rfl))

@[reassoc (attr := simp)]
lemma δ_zero_ι₀ :
    stdSimplex.δ (0 : Fin 2) ≫ ι₀ =
      SSet.const (prodStdSimplex.obj₀Equiv.symm ⟨1, 0⟩) :=
  yonedaEquiv.injective (Prod.ext (by ext i; fin_cases i; rfl) (by rfl))

@[reassoc (attr := simp)]
lemma δ_one_ι₁ :
    stdSimplex.δ (1 : Fin 2) ≫ ι₁ =
      SSet.const (prodStdSimplex.obj₀Equiv.symm ⟨0, 1⟩) :=
  yonedaEquiv.injective (Prod.ext (by ext i; fin_cases i; rfl) (by rfl))

@[reassoc (attr := simp)]
lemma δ_zero_ι₁ :
    stdSimplex.δ (0 : Fin 2) ≫ ι₁ =
      SSet.const (prodStdSimplex.obj₀Equiv.symm ⟨1, 1⟩) :=
  yonedaEquiv.injective (Prod.ext (by ext i; fin_cases i; rfl) (by rfl))

end stdSimplex

namespace KanComplex

namespace FundamentalGroupoid

lemma commSq {X : SSet.{u}} [IsFibrant X] (f : Δ[1] ⊗ Δ[1] ⟶ X)
    (x₀₀ x₀₁ x₁₀ x₁₁ : FundamentalGroupoid X)
    (h₀₀ : f.app _ (prodStdSimplex.obj₀Equiv.symm ⟨0, 0⟩) = x₀₀.pt)
    (h₀₁ : f.app _ (prodStdSimplex.obj₀Equiv.symm ⟨0, 1⟩) = x₀₁.pt)
    (h₁₀ : f.app _ (prodStdSimplex.obj₀Equiv.symm ⟨1, 0⟩) = x₁₀.pt)
    (h₁₁ : f.app _ (prodStdSimplex.obj₀Equiv.symm ⟨1, 1⟩) = x₁₁.pt) :
    CommSq (homMk (Edge.mk (x₀ := x₀₀) (x₁ := x₁₀) (ι₀ ≫ f)
      (by simp [← h₀₀]) (by simp [← h₁₀])))
        (homMk (Edge.mk (ι₀ ≫ (β_ _ _).hom ≫ f)
          (by simp [← h₀₀]; rfl) (by simp [← h₀₁]; rfl)))
        (homMk (Edge.mk (ι₁ ≫ (β_ _ _).hom ≫ f)
          (by simp [← h₁₀]; rfl) (by simp [← h₁₁]; rfl)))
        (homMk (Edge.mk (x₀ := x₀₁) (x₁ := x₁₁) (ι₁ ≫ f)
          (by simp [← h₀₁]) (by simp [← h₁₁]))) where
  w := by
    trans homMk (Edge.mk (square.diagonal ≫ f)
        (by simp [← h₀₀]) (by simp [← h₁₁]))
    · exact Edge.CompStruct.fac { map := square.ιTriangle₀ ≫ f }
    · exact (Edge.CompStruct.fac { map := square.ιTriangle₁ ≫ f }).symm

end FundamentalGroupoid

end KanComplex

variable {X Y : SSet.{u}}

variable (X Y) in
structure HomotopyEquiv where
  hom : X ⟶ Y
  inv : Y ⟶ X
  homInvId : Homotopy (hom ≫ inv) (𝟙 X)
  invHomId : Homotopy (inv ≫ hom) (𝟙 Y)

variable (X) in
@[simps hom inv]
noncomputable def HomotopyEquiv.refl : HomotopyEquiv X X where
  hom := 𝟙 _
  inv := 𝟙 _
  homInvId := .ofEq (by simp)
  invHomId := .ofEq (by simp)

@[simps]
def HomotopyEquiv.symm (e : HomotopyEquiv X Y) : HomotopyEquiv Y X where
  hom := e.inv
  inv := e.hom
  homInvId := e.invHomId
  invHomId := e.homInvId

@[simps]
noncomputable def HomotopyEquiv.ofDeformationRetract (h : DeformationRetract X Y) :
    HomotopyEquiv X Y where
  hom := h.i
  inv := h.r
  homInvId := .ofEq (by simp)
  invHomId :=
    { h := h.h
      rel := by ext _ ⟨⟨_, hx⟩, _⟩; simp at hx }

namespace KanComplex

variable [IsFibrant Y]

section

variable {f₀ f₁ : X ⟶ Y} (h : Homotopy f₀ f₁)

@[simps! map]
noncomputable def edgeOfHomotopy
  (x : X _⦋0⦌) {y₀ y₁ : Y _⦋0⦌} (hy₀ : f₀.app _ x = y₀) (hy₁ : f₁.app _ x = y₁) :
      FundamentalGroupoid.Edge { pt := y₀ } { pt := y₁ } :=
  FundamentalGroupoid.Edge.mk (lift (const x) (𝟙 _) ≫ h.h) (by
    convert yonedaEquiv.symm x ≫= h.h₀ using 1
    · rw [← ι₀_comp_assoc, ι₀_stdSimplex_zero]
      rfl
    · simp [← hy₀]) (by
    convert yonedaEquiv.symm x ≫= h.h₁ using 1
    · rw [← ι₁_comp_assoc, ι₁_stdSimplex_zero]
      rfl
    · simp [← hy₁])

noncomputable def mapFundamentalGroupoidIsoOfHomotopy [IsFibrant X] :
    mapFundamentalGroupoid f₀ ≅ mapFundamentalGroupoid f₁ :=
  NatIso.ofComponents
    (fun x ↦ asIso (FundamentalGroupoid.homMk (edgeOfHomotopy h x.pt rfl rfl)))
    (fun {x₀ x₁} p ↦ by
      obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
      dsimp
      have := (FundamentalGroupoid.commSq (p.map ▷ _ ≫ h.h)
        ((mapFundamentalGroupoid f₀).obj x₀)
        ((mapFundamentalGroupoid f₁).obj x₀)
        ((mapFundamentalGroupoid f₀).obj x₁)
        ((mapFundamentalGroupoid f₁).obj x₁)
        (by
          simp only [← h.h₀]
          dsimp
          exact congr_arg _ (Prod.ext p.comm₀' rfl))
        (by
          simp only [← h.h₁]
          dsimp
          exact congr_arg _ (Prod.ext p.comm₀' rfl))
        (by
          simp only [← h.h₀]
          dsimp
          exact congr_arg _ (Prod.ext p.comm₁' rfl))
        (by
          simp only [← h.h₁]
          dsimp
          exact congr_arg _ (Prod.ext p.comm₁' rfl))).w
      convert this
      · ext : 1
        dsimp
        simp only [← h.h₀]
        rfl
      · ext : 1
        dsimp
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext : 1
        · simp [← p.comm₁']
        · rfl
      · ext : 1
        dsimp
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext : 1
        · simp [← p.comm₀']
        · rfl
      · ext : 1
        dsimp
        simp only [← h.h₁]
        rfl)

variable (n : ℕ) (x : X _⦋0⦌) {y₀ y₁ : Y _⦋0⦌}
  (hy₀ : f₀.app _ x = y₀) (hy₁ : f₁.app _ x = y₁)

lemma congr_mapπ_of_homotopy :
    (FundamentalGroupoid.action.map (FundamentalGroupoid.homMk
      (edgeOfHomotopy h x hy₀ hy₁))).comp (mapπ f₀ n x y₀ hy₀) = mapπ f₁ n x y₁ hy₁ := by
  ext s
  obtain ⟨s, rfl⟩ := s.mk_surjective
  simp only [mapπ_mk, Function.comp_apply]
  exact FundamentalGroupoid.action.map_eq
    { map := s.map ▷ _ ≫ h.h
      whiskerRight_ι_comp_map := by
        simp only [edgeOfHomotopy_map, ← comp_whiskerRight_assoc, s.comm,
          Subcomplex.ofSimplex_ι, comp_const]
        rfl }

include h in
lemma bijective_mapπ_iff_of_homotopy [IsFibrant X] :
    Function.Bijective (mapπ f₀ n x y₀ hy₀) ↔
      Function.Bijective (mapπ f₁ n x y₁ hy₁) := by
  rw [← congr_mapπ_of_homotopy h n x hy₀ hy₁]
  symm
  apply Function.Bijective.of_comp_iff'
  apply FundamentalGroupoid.action.bijective_map

end

variable [IsFibrant X]

lemma isEquivalence_mapFundamentalGroupoid_homotopyEquivHom (e : HomotopyEquiv X Y) :
    (mapFundamentalGroupoid e.hom).IsEquivalence := by
  let e : FundamentalGroupoid X ≌ FundamentalGroupoid Y :=
    CategoryTheory.Equivalence.mk
      (mapFundamentalGroupoid e.hom) (mapFundamentalGroupoid e.inv)
        ((idMapFundamentalGroupoidIso X).symm ≪≫
          (mapFundamentalGroupoidIsoOfHomotopy e.homInvId).symm ≪≫
          compMapFundamentalGroupoidIso e.hom e.inv)
        ((compMapFundamentalGroupoidIso e.inv e.hom).symm ≪≫
          (mapFundamentalGroupoidIsoOfHomotopy e.invHomId) ≪≫
          idMapFundamentalGroupoidIso Y)
  exact e.isEquivalence_functor

lemma isEquivalence_mapFundamentalGroupoid_homotopyEquivInv (e : HomotopyEquiv X Y) :
    (mapFundamentalGroupoid e.inv).IsEquivalence :=
  isEquivalence_mapFundamentalGroupoid_homotopyEquivHom e.symm

lemma W.homotopyEquivHom (e : HomotopyEquiv X Y) :
    W e.hom := by
  have := isEquivalence_mapFundamentalGroupoid_homotopyEquivHom e
  refine W.mk _ inferInstance (fun n x y h ↦ ?_)
  subst h
  wlog hx : ∃ y, e.inv.app _ y = x generalizing x
  · exact W.bijective_of_iso (asIso (FundamentalGroupoid.homMk
      (edgeOfHomotopy e.homInvId x rfl rfl))) (this _ ⟨e.hom.app _ x, rfl⟩)
  constructor
  · have := (bijective_mapπ_iff_of_homotopy e.homInvId n x (y₁ := x) rfl rfl).2
      (by convert Function.bijective_id; aesop)
    rw [← mapπ_comp_mapπ _ _ _ _ rfl _ _ (by aesop)] at this
    exact this.1.of_comp
  · obtain ⟨y, hy⟩ := hx
    have := (bijective_mapπ_iff_of_homotopy e.invHomId n y (y₁ := y) rfl rfl).2
      (by convert Function.bijective_id; aesop)
    subst hy
    rw [← mapπ_comp_mapπ _ _ _ _ rfl _ _ (by aesop)] at this
    exact this.2.of_comp

lemma W.homotopyEquivInv (e : HomotopyEquiv X Y) :
    W e.inv := W.homotopyEquivHom e.symm

variable {f₀ f₁ : X ⟶ Y}

lemma W.of_homotopy (h₀ : W f₀) (h : Homotopy f₀ f₁) : W f₁ :=
  W.mk _ (by
    have := h₀.isEquivalence
    exact Functor.isEquivalence_of_iso (mapFundamentalGroupoidIsoOfHomotopy h)) (by
      intro n x y hxy
      rw [← congr_mapπ_of_homotopy h n x rfl hxy]
      exact (FundamentalGroupoid.action.bijective_map _ _).comp (h₀.bijective _ _ _ _))

lemma W.iff_homotopy (h : Homotopy f₀ f₁) :
    W f₀ ↔ W f₁ :=
  ⟨fun hf₀ ↦ hf₀.of_homotopy h,
    fun hf₁ ↦ hf₁.of_homotopy h.symm⟩

end KanComplex

end SSet
