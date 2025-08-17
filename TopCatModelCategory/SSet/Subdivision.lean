import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.SSet.NonemptyFiniteChains
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.ULift

universe v u

open CategoryTheory Limits Simplicial Opposite

instance : HasColimitsOfSize.{u, u} SSet.{u} := by
  dsimp [SSet, SimplicialObject]
  infer_instance

instance : HasColimitsOfSize.{0, u} SSet.{u} := by
  dsimp [SSet, SimplicialObject]
  infer_instance

def PartOrd.uliftFUnctor : PartOrd.{u} ⥤ PartOrd.{max u v} where
  obj X := .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x ↦ ULift.up (f (ULift.down x)),
    fun x y hxy ↦ f.hom.monotone hxy⟩

namespace SimplexCategory

def toPartOrd : SimplexCategory ⥤ PartOrd.{u} :=
  skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFUnctor

@[simp]
lemma toPartOrd_obj (n : SimplexCategory) :
    toPartOrd.{u}.obj n = .of (ULift.{u} (Fin (n.len + 1))) := by
  rfl

@[simp]
lemma toPartOrd_map_apply {n m : SimplexCategory} (f : n ⟶ m)
    (i : (Fin (n.len + 1))) :
    toPartOrd.{u}.map f (ULift.up i) = ULift.up (f i) := by
  rfl

noncomputable def sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

end SimplexCategory

namespace SSet

noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.sd

noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

noncomputable def sdExAdjunction : sd.{u} ⊣ ex.{u} :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

namespace stdSimplex

noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

def partOrdIso : stdSimplex.{u} ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n ↦ by
    induction' n using SimplexCategory.rec with n
    exact isoNerve _ (orderIsoULift _).symm)

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd.{u}))

@[simps!]
noncomputable def B : SSet.{u} ⥤ SSet.{u} := SSet.N.functor ⋙ PartOrd.nerveFunctor

open Functor in
noncomputable def stdSimplexCompBIso : stdSimplex.{u} ⋙ B ≅ SimplexCategory.sd :=
  isoWhiskerRight stdSimplex.partOrdIso _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight PartOrd.nerveFunctorCompNIso PartOrd.nerveFunctor)

noncomputable def sdToB : sd.{u} ⟶ B :=
  sd.{u}.descOfIsLeftKanExtension stdSimplex.sdIso.inv _ stdSimplexCompBIso.{u}.inv

lemma sdToB_app_stdSimplex_obj (n : SimplexCategory) :
    sdToB.{u}.app (stdSimplex.obj n) =
      stdSimplex.sdIso.hom.app n ≫ stdSimplexCompBIso.inv.app n := by
  have := sd.{u}.descOfIsLeftKanExtension_fac_app
    stdSimplex.sdIso.inv _ stdSimplexCompBIso.{u}.inv n
  simp only [← this, Iso.hom_inv_id_app_assoc, sdToB]

instance (n : SimplexCategory) : IsIso (sdToB.{u}.app (stdSimplex.obj n)) := by
  rw [sdToB_app_stdSimplex_obj]
  infer_instance

instance : IsIso (Functor.whiskerLeft stdSimplex sdToB) := by
  rw [NatTrans.isIso_iff_isIso_app]
  dsimp
  infer_instance

section

variable (X : SSet.{u})

variable {X} in
lemma N.lift_monotone_aux {s₀ s₁ : X.N} (hs : s₀ ≤ s₁)
    {d : ℕ} (f : Δ[d] ⟶ X) (φ₁ : Δ[d].N)
    (hφ₁ : s₁.toS = S.map f φ₁.toS) :
    ∃ (φ₀ : Δ[d].N), φ₀ ≤ φ₁ ∧ s₀.toS = S.map f φ₀.toS := by
  obtain ⟨dx, ⟨x, hx⟩, rfl⟩ := φ₁.mk_surjective
  obtain ⟨a, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [stdSimplex.mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply] at hx
  obtain rfl : s₁.dim = dx := S.dim_eq_of_eq hφ₁
  rw [le_iff_exists] at hs
  obtain ⟨g, _, hg⟩ := hs
  rw [S.ext_iff'] at hφ₁
  simp only [S.map_dim, mk_dim, S.cast_dim, S.cast_simplex_rfl, S.map_simplex, mk_simplex,
    exists_const] at hφ₁
  refine ⟨N.mk (SSet.stdSimplex.objEquiv.symm (g ≫ a)) ?_, ?_, ?_⟩
  · rw [stdSimplex.mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply]
    infer_instance
  · dsimp
    rw [N.le_iff, Subpresheaf.ofSection_le_iff,
      Subcomplex.mem_ofSimplex_obj_iff]
    exact ⟨g, rfl⟩
  · dsimp
    rw [S.ext_iff']
    simp only [S.map_dim, mk_dim, S.cast_dim, S.cast_simplex_rfl, S.map_simplex, mk_simplex,
      exists_const]
    rw [← hg, hφ₁, stdSimplex.objEquiv_symm_comp, ← FunctorToTypes.naturality]
    rfl

variable {X} in
lemma N.lift_monotone {n : ℕ} (s : Fin (n + 1) →o X.N) :
    ∃ (d : ℕ) (f : Δ[d] ⟶ X) (φ : Fin (n + 1) → Δ[d].N) (_ : Monotone φ),
      ∀ (i : Fin (n + 1)), (s i).toS = S.map f (φ i).toS := by
  induction n with
  | zero =>
    refine ⟨_, yonedaEquiv.symm (s 0).simplex,
      fun _ ↦ N.mk _ (stdSimplex.id_nonDegenerate (s 0).dim), ?_, ?_⟩
    · rw [Fin.monotone_iff_le_succ]
      intro i
      fin_cases i
    · intro i
      fin_cases i
      simp [SSet.S.ext_iff']
  | succ n hn =>
    let t : Fin (n + 1) →o X.N := ⟨_, (s.monotone.comp Fin.strictMono_succ.monotone)⟩
    obtain ⟨d, f, φ, hφ, hφ'⟩ := hn t
    obtain ⟨φ₀, hφ₀, hφ₀'⟩ :=
      N.lift_monotone_aux (s.monotone (Fin.zero_le 1)) f (φ 0) (hφ' 0)
    refine ⟨d, f, Fin.cases φ₀ φ, ?_, ?_⟩
    · rw [Fin.monotone_iff_le_succ]
      intro i
      induction i using Fin.cases with
      | zero => exact hφ₀
      | succ i => exact hφ (by simp)
    · intro i
      induction i using Fin.cases with
      | zero =>  exact hφ₀'
      | succ i => exact hφ' i

open PartialOrder in
instance : Epi (sdToB.app X) := by
  rw [epi_iff_nonDegenerate]
  intro n b hb
  obtain ⟨d, f, φ, hφ, hφ'⟩ := N.lift_monotone b.toOrderHom
  let ψ (i : Fin (n + 1)) : NonemptyFiniteChains (ULift.{u} (Fin (d + 1))) :=
    NonemptyFiniteChains.ofN (mapN (stdSimplex.partOrdIso.hom.app _) (φ i))
  have hψ : Monotone ψ := fun i j hij ↦ by
    dsimp [ψ]
    rw [NonemptyFiniteChains.le_iff, NonemptyFiniteChains.ofN_le_ofN_iff]
    exact (mapN _).monotone (hφ hij)
  let s : SimplexCategory.sd ^⦋d⦌ _⦋n⦌ := Monotone.functor hψ
  refine ⟨(sd.map f).app _
    ((stdSimplex.sdIso.{u}.inv.app ⦋d⦌).app _ s), ?_⟩
  dsimp
  rw [← FunctorToTypes.comp, NatTrans.naturality, FunctorToTypes.comp,
    sdToB_app_stdSimplex_obj, comp_app, types_comp_apply]
  nth_rw 3 [← FunctorToTypes.comp]
  rw [Iso.inv_hom_id_app, NatTrans.id_app, types_id_apply]
  apply Preorder.nerveExt
  ext i
  dsimp [B, mapN]
  rw [toN_of_nonDegenerate]
  · rw [N.ext_iff]
    change S.map f (((stdSimplexCompBIso.inv.app ⦋d⦌).app (op ⦋n⦌) s).obj i).toS = _
    refine Eq.trans ?_ (hφ' i).symm
    congr
    dsimp [s, ψ]
    ext
    sorry
  · sorry

noncomputable def isColimitBMapCoconeCoconeN :
    IsColimit (B.mapCocone X.coconeN) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    sorry)

instance : PreservesColimit X.functorN B :=
  preservesColimit_of_preserves_colimit_cocone X.isColimitCoconeN
    X.isColimitBMapCoconeCoconeN

end

end SSet
