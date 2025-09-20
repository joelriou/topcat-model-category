import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.SSet.FiniteInduction
import TopCatModelCategory.TrivialBundleOver
import TopCatModelCategory.TopCat.SerreFibrationBundle
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.ToTopExact
import TopCatModelCategory.ModelCategoryTopCat

universe u

open Simplicial CategoryTheory MorphismProperty HomotopicalAlgebra
  TopCat.modelCategory Limits

namespace CategoryTheory

lemma Limits.PushoutCocone.isPushout_iff_nonempty_isColimit
    {C : Type*} [Category C]
    {S T₁ T₂ : C} {f₁ : S ⟶ T₁} {f₂ : S ⟶ T₂}
    (c : PushoutCocone f₁ f₂) :
    IsPushout f₁ f₂ c.inl c.inr ↔ Nonempty (IsColimit c) :=
  ⟨fun sq ↦ ⟨IsColimit.ofIsoColimit sq.isColimit (PushoutCocone.ext (Iso.refl _))⟩, fun h ↦
    { w := c.condition
      isColimit' := ⟨IsColimit.ofIsoColimit h.some (PushoutCocone.ext (Iso.refl _))⟩ }⟩

namespace Over

variable {C : Type*} [Category C] {B : C} {X₁ X₂ X₃ X₄ : Over B}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma isPushout_iff_forget [HasPushouts C] :
    IsPushout t l r b ↔ IsPushout t.left l.left r.left b.left :=
  ⟨fun sq ↦ sq.map (Over.forget _), fun sq ↦
    { w := by ext; exact sq.w
      isColimit' := ⟨by
        refine PushoutCocone.IsColimit.mk _
          (fun s ↦ Over.homMk (sq.desc s.inl.left s.inr.left
            ((Over.forget _).congr_map s.condition)) (by apply sq.hom_ext <;> simp))
          (by aesop) (by aesop) (fun s m h₁ h₂ ↦ ?_)
        ext
        apply sq.hom_ext
        · simp [← h₁]
        · simp [← h₂]⟩ }⟩

instance {D : Type*} [Category D] [HasPushouts C] [HasPushouts D]
    (F : C ⥤ D) [PreservesColimitsOfShape WalkingSpan F] (X : C) :
    PreservesColimitsOfShape WalkingSpan (Over.post (X := X) F) := by
  suffices ∀ {S T₁ T₂ : Over X} (f₁ : S ⟶ T₁) (f₂ : S ⟶ T₂),
      PreservesColimit (span f₁ f₂) (Over.post (X := X) F) from
    ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro S T₁ T₂ f₁ f₂
  constructor
  intro c hc
  refine ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).2
    (((PushoutCocone.isPushout_iff_nonempty_isColimit _).1 ?_).some)⟩
  rw [isPushout_iff_forget]
  exact (PushoutCocone.isPushout_iff_nonempty_isColimit _).2
    ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).1
      (isColimitOfPreserves (Over.forget _ ⋙ F) hc)⟩

end Over

end CategoryTheory

def DeltaGenerated'.isLimitBinaryFanOfIsEmpty
    {X Y : DeltaGenerated'.{u}} {c : BinaryFan X Y}
    (hX : IsEmpty ((forget _).obj X)) (_ : IsEmpty ((forget _).obj c.pt)) :
    IsLimit c :=
  have h {T : DeltaGenerated'.{u}} (f : T ⟶ X) (t : (forget _).obj T) : False := by
    have := Function.isEmpty ((forget _).map f)
    exact isEmptyElim (α := ((forget _).obj T)) t
  BinaryFan.IsLimit.mk _ (fun {T} f₁ _ ↦ TopCat.ofHom ⟨fun t ↦ (h f₁ t).elim, by
      rw [continuous_iff_continuousAt]
      intro t
      exact (h f₁ t).elim⟩)
    (fun f₁ _ ↦ by ext t; exact (h f₁ t).elim)
    (fun f₁ _ ↦ by ext t; exact (h f₁ t).elim)
    (fun f₁ _ _ _ _ ↦ by ext t; exact (h f₁ t).elim)

def DeltaGenerated'.isInitialOfIsEmpty (X : DeltaGenerated'.{u})
    [IsEmpty ((forget _).obj X)] :
    IsInitial X :=
  have h {T : DeltaGenerated'.{u}} (f : T ⟶ X) (t : (forget _).obj T) : False := by
    have := Function.isEmpty ((forget _).map f)
    exact isEmptyElim (α := ((forget _).obj T)) t
  IsInitial.ofUniqueHom
    (fun _ ↦ TopCat.ofHom ⟨fun (x : (forget _).obj X) ↦ isEmptyElim x, by
      rw [continuous_iff_continuousAt]
      intro (x : (forget _).obj X)
      exact isEmptyElim x⟩)
    (fun _ f ↦ by
      ext (x : (forget _).obj X)
      dsimp
      exact isEmptyElim x)

lemma DeltaGenerated'.isEmpty_of_isInitial {X : DeltaGenerated'.{u}}
    (hX : IsInitial X) : IsEmpty ((forget _).obj X) := by
  let f : X ⟶ GeneratedByTopCat.of PEmpty := hX.to _
  exact Function.isEmpty f

namespace SSet

variable {E B : SSet.{u}} {p : E ⟶ B} {F : SSet.{u}}
  (τ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ)

namespace MinimalFibrationLocTrivial

section

noncomputable abbrev pull (_ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ) :=
    Over.pullback ((toDeltaGenerated.map p))

variable (A : Over (toDeltaGenerated.obj B))

noncomputable def pullObj : DeltaGenerated'.{u} := ((pull τ).obj A).left

noncomputable def ι : pullObj τ A ⟶ toDeltaGenerated.obj E := ((pull τ).obj A).hom

noncomputable def π : pullObj τ A ⟶ A.left := pullback.fst _ _

lemma isPullback : IsPullback (ι τ A) (π τ A) (toDeltaGenerated.map p) A.hom :=
  (IsPullback.of_hasPullback _ _).flip

variable (p F) in
def IsTrivial : Prop :=
  Nonempty (TrivialBundleWithFiberOver (toDeltaGenerated.obj F) (toDeltaGenerated.map p) A.hom)

instance (X : Type u) [IsEmpty X] [TopologicalSpace X] [DeltaGeneratedSpace' X] :
    IsEmpty ((forget DeltaGenerated').obj (.of X)) := by assumption

lemma isTrivial_of_isEmpty (h : IsEmpty ((forget _).obj A.left)) :
    IsTrivial p F A := by
  let φ := ((forget _).map (pullback.fst (X := A.left) A.hom (toDeltaGenerated.map p)))
  have := Function.isEmpty φ
  exact
    ⟨{sq := (IsPullback.of_hasPullback _ _).flip
      h :=
      { r := (DeltaGenerated'.isInitialOfIsEmpty _).to _
        isLimit :=DeltaGenerated'.isLimitBinaryFanOfIsEmpty h (by assumption) } }⟩

def IsLocTrivial : Prop :=
  (trivialBundlesWithFiber (toDeltaGenerated.obj F)).locally
    GeneratedByTopCat.grothendieckTopology (π τ A)

variable {τ A} in
lemma IsTrivial.isLocTrivial (hA : IsTrivial p F A) : IsLocTrivial τ A :=
  MorphismProperty.le_locally _ _ _
    ⟨hA.some.trivialBundleWithFiber (IsPullback.of_hasPullback _ _).flip⟩

section

variable {Z : DeltaGenerated'.{u}} {t : Z ⟶ toDeltaGenerated.obj E}
    {l : Z ⟶ A.left} (sq : IsPullback t l (toDeltaGenerated.map p) A.hom)

include sq

noncomputable def objIso : pullObj τ A ≅ Z :=
  (IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose

@[reassoc (attr := simp)]
lemma objIso_hom_comp_eq_π : (objIso τ A sq).hom ≫ l = π τ A := by
  simpa using ((IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose_spec.2).symm

end

end

section

variable {A} {K₀ A₀ K : Over (toDeltaGenerated.obj B)}
  {t : K₀ ⟶ A₀} {l : K₀ ⟶ K} {r : A₀ ⟶ A} {b : K ⟶ A}
  (sq : IsPushout t l r b)

include sq

lemma isLocTrivial_of_isPushout
    (hl : TopCat.closedEmbeddings (DeltaGenerated'.toTopCat.map l.left))
    (hK : IsTrivial p F K) (hA₀ : IsLocTrivial τ A₀)
    (hsq : PreservesColimit (span t l) (CategoryTheory.Over.pullback (toDeltaGenerated.map p)))
    {U : DeltaGenerated'.{u}} (i : U ⟶ K.left) (hi : GeneratedByTopCat.openImmersions i)
    (l' : K₀.left ⟶ U) (fac : l' ≫ i = l.left) (ρ : U ⟶ K₀.left) (fac' : l' ≫ ρ = 𝟙 _) :
    IsLocTrivial τ A := by
  have := sq
  sorry

end

lemma isLocTrivial {Z : SSet.{u}} [IsFinite Z] (a : Z ⟶ B) :
    IsLocTrivial τ (Over.mk (toDeltaGenerated.map a)) := by
  induction Z using SSet.finite_induction with
  | hP₀ X =>
    refine (isTrivial_of_isEmpty _
      (DeltaGenerated'.isEmpty_of_isInitial ?_)).isLocTrivial
    dsimp
    exact IsInitial.isInitialObj _ _ (SSet.isInitialOfNotNonempty
      (by rwa [SSet.notNonempty_iff_hasDimensionLT_zero]))
  | @hP Z₀ Z i n j j₀ sq _ h₀ =>
    let t : Over.mk (j ≫ i ≫ a) ⟶ Over.mk (i ≫ a) := Over.homMk j
    let b : Over.mk (j₀ ≫ a) ⟶ Over.mk a := Over.homMk j₀
    have sq' : IsPushout (Over.homMk j : Over.mk (j ≫ i ≫ a) ⟶ Over.mk (i ≫ a))
        (Over.homMk (Subcomplex.ι _) (by simp [sq.w_assoc]))
        (Over.homMk (by exact i)) (Over.homMk j₀ : Over.mk (j₀ ≫ a) ⟶ Over.mk a) := by
      rwa [Over.isPushout_iff_forget ]
    refine isLocTrivial_of_isPushout τ (sq'.map (Over.post (SSet.toDeltaGenerated)))
      ?_ ⟨(τ (j₀ ≫ a)).map toDeltaGenerated⟩ (h₀ _) ?_ (U := ?_) ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp
      apply closedEmbeddings_toObj_map_of_mono
    · dsimp
      sorry
    -- the next goals are about taking the complement of the isobarycenter in the simplex
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

end MinimalFibrationLocTrivial

variable (p) in
open MinimalFibrationLocTrivial MorphismProperty in
include τ in
lemma fibration_toTop_map_of_trivialBundle_over_simplices [IsFinite B] :
    Fibration (toTop.map p) := by
  let e : Arrow.mk (π τ (Over.mk (toDeltaGenerated.map (𝟙 B)))) ≅ Arrow.mk (toDeltaGenerated.map p) := by
    have : IsPullback (𝟙 (toDeltaGenerated.obj E)) (toDeltaGenerated.map p)
        (toDeltaGenerated.map p) (toDeltaGenerated.map (𝟙 B)) := by
      simpa using IsPullback.id_horiz (toDeltaGenerated.map p)
    exact Arrow.isoMk (objIso τ _ this) (Iso.refl _)
  exact DeltaGenerated'.fibration_toTopCat_map_of_locally_trivialBundle
    ((arrow_mk_iso_iff _ e).1
      (locally_monotone (trivialBundlesWithFiber_le_trivialBundles _) _ _ (isLocTrivial τ (𝟙 B))))

end SSet
