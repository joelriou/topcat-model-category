import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.SSet.NonemptyFiniteChains
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.Skeleton
import TopCatModelCategory.SSet.Monomorphisms
import TopCatModelCategory.MorphismProperty
import TopCatModelCategory.ULift

-- Jardine, *Simplicial approximation*

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

@[simp]
lemma partOrdIso_inv_app (n : ℕ) :
    partOrdIso.{u}.inv.app ⦋n⦌ = (isoNerve _ (orderIsoULift _).symm).inv := rfl

@[simp]
lemma partOrdIso_hom_app (n : ℕ) :
    partOrdIso.{u}.hom.app ⦋n⦌ = (isoNerve _ (orderIsoULift _).symm).hom := rfl

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
  have hs (i : Fin (n + 1)) :
      ((stdSimplexCompBIso.inv.app ⦋d⦌).app (op ⦋n⦌) s).obj i = φ i := by
    rw [N.ext_iff]
    dsimp [s, stdSimplexCompBIso]
    rw [toS_mapN_of_isIso]
    dsimp [PartOrd.nerveFunctorCompNIso]
    have : NonemptyFiniteChains.nerveNEquiv.symm (ψ i) =
      N.mk' (S.map (stdSimplex.isoNerve.{u} (ULift.{u} (Fin (d + 1)))
        (orderIsoULift _).symm).hom (φ i).toS) (by
          rw [S.simplex_map_nonDegenerate_iff_of_mono]
          exact (φ i).nonDegenerate) := by
      apply NonemptyFiniteChains.nerveNEquiv.injective
      simp [ψ]
      congr
      rw [N.ext_iff, toS_mapN_of_isIso]
      rfl
    erw [this]
    rw [N.mk'_toS, S.map_map, Iso.hom_inv_id, S.map_id]
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
  rw [S.toN_of_nonDegenerate]
  · dsimp
    rw [N.ext_iff]
    change S.map f (((stdSimplexCompBIso.inv.app ⦋d⦌).app (op ⦋n⦌) s).obj i).toS = _
    rw [hs, ← hφ']
    dsimp
  · rw [hs, ← hφ']
    exact (b.toOrderHom i).2

noncomputable def N.equivSubcomplex (s : X.N) :
    s.subcomplex.toSSet.N ≃o Set.Iic s where
  toFun x := ⟨mapN s.subcomplex.ι x, by simp [le_iff_toS_le_toS, toS_mapN_of_mono, S.le_iff]⟩
  invFun y := N.toSubcomplex y.1 (by
    rw [← Subpresheaf.ofSection_le_iff]
    exact y.2)
  left_inv x := by simp
  right_inv y := by aesop
  map_rel_iff' {x y} := by
    rw [← Subtype.coe_le_coe]
    dsimp
    rw [N.le_iff, N.le_iff, subcomplex_mapN, subcomplex_mapN,
      Subcomplex.image_le_image_iff_of_mono]

variable {X} in
lemma isColimitBMapCoconeCoconeN_aux
    {n : ℕ} {i : X.N} (x : ComposableArrows i.subcomplex.toSSet.N n)
    {k : X.N} (hk : mapN i.subcomplex.ι (x.obj (Fin.last _)) = k) :
    ∃ (z : ComposableArrows k.subcomplex.toSSet.N n), ∀ (d : Fin (n + 1)),
      mapN k.subcomplex.ι (z.obj d) =
        mapN i.subcomplex.ι (x.obj d) := by
  let φ (d : Fin (n + 1)) : k.subcomplex.toSSet.N :=
    (mapN i.subcomplex.ι (x.obj d)).toSubcomplex (by
      simp only [← Subpresheaf.ofSection_le_iff, subcomplex_mapN]
      have h₁ := x.monotone d.le_last
      rw [N.le_iff] at h₁
      exact (Subcomplex.image_monotone i.subcomplex.ι h₁).trans (by simp [← hk]))
  have hφ : Monotone φ := by
    intro d d' h
    dsimp [φ]
    rw [N.toSubcomplex_le_toSubcomplex_iff]
    exact (mapN _).monotone (x.monotone h)
  refine ⟨hφ.functor, fun d ↦ by simp [φ]⟩

open Functor in
noncomputable def isColimitBMapCoconeCoconeN :
    IsColimit (B.mapCocone X.coconeN) :=
  evaluationJointlyReflectsColimits _ (fun ⟨n⟩ ↦ by
    induction' n using SimplexCategory.rec with n
    apply Nonempty.some
    rw [Types.isColimit_iff_coconeTypesIsColimit]
    refine ⟨⟨?_, fun b ↦ ?_⟩⟩
    · intro x y h
      obtain ⟨i, x, rfl⟩ := ιColimitType_jointly_surjective _ x
      obtain ⟨j, y, rfl⟩ := ιColimitType_jointly_surjective _ y
      dsimp at x y h
      generalize hx : mapN i.subcomplex.ι (x.obj (Fin.last _)) = k
      have hy : mapN j.subcomplex.ι (y.obj (Fin.last _)) = k := by
        rw [← hx]
        exact Functor.congr_obj h.symm (Fin.last _)
      have hki : k ≤ i := by
        rw [← hx, N.le_iff_toS_le_toS, toS_mapN_of_mono, S.le_iff]
        simp
      have hkj : k ≤ j := by
        rw [← hy, N.le_iff_toS_le_toS, toS_mapN_of_mono, S.le_iff]
        simp
      obtain ⟨z, hz⟩ := isColimitBMapCoconeCoconeN_aux x hx
      obtain ⟨z', hz'⟩ := isColimitBMapCoconeCoconeN_aux y hy
      obtain rfl : z = z' := by
        apply Preorder.nerveExt
        ext d : 1
        apply N.mapN_injective_of_mono k.subcomplex.ι
        rw [hz, hz']
        exact Functor.congr_obj h d
      trans Functor.ιColimitType _ k z
      · rw [← ιColimitType_map _ (homOfLE hki)]
        congr
        apply Preorder.nerveExt
        ext d : 1
        apply N.mapN_injective_of_mono i.subcomplex.ι
        dsimp
        rw [mapN_mapN]
        exact (hz d).symm
      · rw [← ιColimitType_map _ (homOfLE hkj)]
        congr
        apply Preorder.nerveExt
        ext d : 1
        apply N.mapN_injective_of_mono j.subcomplex.ι
        dsimp
        rw [mapN_mapN]
        exact hz' d
    · refine ⟨Functor.ιColimitType _ (b.obj (Fin.last _))
        (Monotone.functor (f := fun i ↦ (b.obj i).toSubcomplex ?_) (fun i j hij ↦ ?_)),
        Preorder.nerveExt ?_⟩
      · dsimp
        rw [← Subpresheaf.ofSection_le_iff, ← N.le_iff]
        exact b.monotone i.le_last
      · dsimp
        rw [N.toSubcomplex_le_toSubcomplex_iff]
        exact b.monotone hij
      · ext i
        rw [N.ext_iff]
        dsimp
        apply toS_mapN_of_mono)

instance : PreservesColimit X.functorN B :=
  preservesColimit_of_preserves_colimit_cocone X.isColimitCoconeN
    X.isColimitBMapCoconeCoconeN

end

variable (X : SSet.{u})

class IsWeaklyPolyhedralLike where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.1)

attribute [instance] IsWeaklyPolyhedralLike.mono

instance (T : Type u) [PartialOrder T] :
    (nerve T).IsWeaklyPolyhedralLike where
  mono := by
    rintro d ⟨x, hx⟩
    dsimp
    rw [PartialOrder.mem_nonDegenerate_iff] at hx
    rw [NatTrans.mono_iff_mono_app]
    intro ⟨n⟩
    induction' n using SimplexCategory.rec with n
    rw [mono_iff_injective]
    intro i j h
    ext k : 1
    apply hx.injective
    exact Functor.congr_obj h k

instance : (B.obj X).IsWeaklyPolyhedralLike := by
  dsimp [B]
  infer_instance

section

variable [X.IsWeaklyPolyhedralLike]

variable {X}

lemma mono_yonedaEquiv_symm {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) :=
  IsWeaklyPolyhedralLike.mono ⟨x, hx⟩

instance (x : X.N) : Mono (yonedaEquiv.symm x.simplex) :=
  mono_yonedaEquiv_symm _ x.nonDegenerate

lemma IsWeaklyPolyhedralLike.isIso_toOfSimplex {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    IsIso (Subcomplex.toOfSimplex x) := by
  have : Mono (Subcomplex.toOfSimplex x) := by
    have := mono_yonedaEquiv_symm x hx
    exact mono_of_mono_fac (Subcomplex.toOfSimplex_ι x)
  apply isIso_of_mono_of_epi

@[simps! hom]
noncomputable def IsWeaklyPolyhedralLike.iso {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Δ[n] ≅ Subcomplex.ofSimplex x :=
  have := IsWeaklyPolyhedralLike.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

instance (x : X.N) : IsIso (sdToB.app x.subcomplex.toSSet) := by
  rw [NatTrans.isIso_app_iff_of_iso _ (IsWeaklyPolyhedralLike.iso _ x.nonDegenerate).symm]
  infer_instance

open MorphismProperty

instance : IsIso (sdToB.app X) :=
  colimitsOfShape_le (W := isomorphisms SSet.{u}) _
    (colimitsOfShape.mk' _ _ _ _ (isColimitOfPreserves sd X.isColimitCoconeN)
      X.isColimitBMapCoconeCoconeN (Functor.whiskerLeft _ sdToB)
      (fun s ↦ (by dsimp; simp only [isomorphisms.iff]; infer_instance)) _ (by simp))

lemma isWeaklyPolyhedralLike_of_mono {Y : SSet.{u}} (f : Y ⟶ X) [Mono f] :
    IsWeaklyPolyhedralLike Y where
  mono {n} x := by
    have := mono_yonedaEquiv_symm (f.app _ x.1) (by
      rw [nonDegenerate_iff_of_mono]
      exact x.2)
    exact mono_of_mono_fac (yonedaEquiv_symm_comp x.1 f)

instance (A : X.Subcomplex) : A.toSSet.IsWeaklyPolyhedralLike :=
  isWeaklyPolyhedralLike_of_mono A.ι

end

instance [X.IsWeaklyPolyhedralLike] : (sd.obj X).IsWeaklyPolyhedralLike :=
  isWeaklyPolyhedralLike_of_mono (asIso (sdToB.app X)).hom

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).IsWeaklyPolyhedralLike :=
  isWeaklyPolyhedralLike_of_mono (X := nerve _) (stdSimplex.partOrdIso.{u}.app n).hom

instance : B.{u}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    rintro ⟨n⟩
    induction' n using SimplexCategory.rec with n
    rw [mono_iff_injective]
    intro s t h
    apply Preorder.nerveExt
    ext i
    exact N.mapN_injective_of_mono f (Functor.congr_obj h i)

open MorphismProperty in
instance (n : ℕ) : Mono (sd.map (boundary.{u} n).ι) :=
  ((monomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (asIso (sdToB.app _)) (asIso (sdToB.app _)))).2
      (monomorphisms.infer_property (B.map (boundary.{u} n).ι))

instance : PreservesWellOrderContinuousOfShape ℕ sd.{u} where

section

open MorphismProperty

instance : IsStableUnderCoproducts.{u} ((monomorphisms SSet).inverseImage sd.{u}) where
  isStableUnderCoproductsOfShape J := by
    simp only [isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
    rintro X Y f hf
    have hsd : ((monomorphisms _).inverseImage sd).map sd.{u} ≤ monomorphisms _ :=
      (map_inverseImage_le _ _).trans (by rw [isoClosure_eq_self])
    apply colimitsOfShape_le _ ((colimitsOfShape_monotone hsd _) _
      (MorphismProperty.map_colimitsOfShape  _ hf sd))

open MorphismProperty modelCategoryQuillen in
instance : sd.{u}.PreservesMonomorphisms where
  preserves {X Y} i _ := by
    have : (coproducts.{u} I).pushouts ≤ (monomorphisms _).inverseImage sd.{u} := by
      rw [← MorphismProperty.map_le_iff]
      refine ((coproducts.{u} I).map_pushouts_le sd.{u}).trans ?_
      simp only [pushouts_le_iff, map_le_iff, coproducts_le_iff]
      intro _ _ _ ⟨n⟩
      simp only [inverseImage_iff, monomorphisms.iff]
      infer_instance
    apply transfiniteCompositionsOfShape_le _ _ _
      ((modelCategoryQuillen.transfiniteCompositionOfMono i).ofLE this).map.mem

end

end SSet
