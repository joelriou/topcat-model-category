import TopCatModelCategory.SemiSimplexCategory
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.Gluing
import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.SSet.NonemptyFiniteChains
import TopCatModelCategory.Homeomorph

universe u

open CategoryTheory SSet NNReal Simplicial Topology Limits

namespace SSet.stdSimplex

noncomputable def orderIsoN {n : ℕ} :
    (Δ[n] : SSet.{u}).N ≃o { S : Finset (Fin (n + 1)) // S ≠ ∅ } where
  toEquiv := Equiv.ofBijective (fun s ↦ ⟨Finset.image s.simplex .univ, by
    simp [← Finset.nonempty_iff_ne_empty]⟩) (by
    constructor
    · rintro s₁ s₂ h
      obtain ⟨d₁, s₁, rfl⟩ := s₁.mk_surjective
      obtain ⟨d₂, s₂, rfl⟩ := s₂.mk_surjective
      obtain rfl : d₁ = d₂ := by
        rw [← Nat.add_right_cancel_iff (n := 1)]
        have h₁ := (nonDegenerateEquiv' s₁).2
        have h₂ := (nonDegenerateEquiv' s₂).2
        simp only [Set.mem_setOf_eq, Set.coe_setOf] at h₁ h₂
        rw [← h₁, ← h₂]
        congr 1
        rwa [Subtype.ext_iff] at h
      obtain rfl : s₁ = s₂ := nonDegenerateEquiv'.injective (by
        rwa [Subtype.ext_iff] at h ⊢)
      rfl
    · rintro ⟨S, hS⟩
      obtain ⟨m, hm⟩ : ∃ (m : ℕ), S.card = m + 1 := by
        simpa [Finset.nonempty_iff_ne_empty] using hS
      obtain ⟨⟨s, h₁⟩, h₂⟩ := nonDegenerateEquiv'.{u}.surjective ⟨S, hm⟩
      exact ⟨N.mk s h₁, by rwa [Subtype.ext_iff] at h₂ ⊢⟩)
  map_rel_iff' := by
    rintro s₁ s₂
    rw [N.le_iff_toS_le_toS, Subtype.mk_le_mk, S.le_iff]
    dsimp [S.subcomplex]
    obtain ⟨d₁, s₁, rfl⟩ := s₁.mk_surjective
    obtain ⟨d₂, s₂, rfl⟩ := s₂.mk_surjective
    dsimp
    rw [← face_nonDegenerateEquiv', ← face_nonDegenerateEquiv', face_le_face_iff]
    rfl

end SSet.stdSimplex

namespace SimplexCategory

section

variable (n : ℕ)

noncomputable def affineMap : AffineMap.{_, u} Δ[n] (Fin (n + 1) → ℝ) where
  f s := ⦋n⦌.toTopHomeo s
  isAffine := by
    rw [isAffine_iff_eq_top, stdSimplex.subcomplex_eq_top_iff, mem_isAffine_iff,
      IsAffineAt, AffineMap.isAffineAtφ_toTopHomeo]
    exact stdSimplex.isAffine_dFunLikeCoe _

namespace affineMap

lemma f_eq_comp : (affineMap n).f = Function.comp toTopObjι ⦋n⦌.toTopHomeo := rfl

lemma isClosedEmbedding_f :
    IsClosedEmbedding (affineMap n).f :=
  isClosedEmbedding_toTopObjι.comp ⦋n⦌.toTopHomeo.isClosedEmbedding

end affineMap

end

noncomputable abbrev sdToTop : CosimplicialObject TopCat.{u} :=
  sd ⋙ SSet.toTop

lemma affineMap_stdSimplex_f (n : ℕ) :
    (AffineMap.stdSimplex n).f = DFunLike.coe ∘ toTopHomeo _ := rfl

lemma affineMap_stdSimplex_range_f (n : ℕ) :
    Set.range (AffineMap.stdSimplex n).f = stdSimplex _ _ := by
  simp [affineMap_stdSimplex_f, Set.range_comp]
  change Set.range Subtype.val = _
  simp

end SimplexCategory

namespace SemiSimplexCategory

@[simps!]
noncomputable def toTop : SemiCosimplicialObject TopCat.{u} :=
  CosimplicialObject.toSemiCosimplicialObject (stdSimplex ⋙ SSet.toTop)

noncomputable def sdToTop : SemiCosimplicialObject TopCat.{u} :=
  SimplexCategory.sdToTop.toSemiCosimplicialObject

namespace BIso

section

variable (n : ℕ)

noncomputable abbrev ι := (B.{u}.obj Δ[n]).N

structure ι' where
  d : ℕ
  S (i : Fin (d + 1)) : Finset (Fin (n + 1))
  hS₀ i : Nonempty (S i)
  inter i j (hij : i ≠ j) : Disjoint (S i) (S j)

section

variable {n} (s : ι.{u} n)

noncomputable def ι.finset (i : Fin (s.dim + 1)) : Finset (Fin (n + 1)) :=
  (SSet.stdSimplex.orderIsoN (s.simplex.obj i)).1

lemma ι.strictMono_finset : StrictMono s.finset := by
  intro i j hij
  have := (PartialOrder.mem_nonDegenerate_iff s.simplex).1 s.nonDegenerate hij
  rwa [← stdSimplex.orderIsoN.lt_iff_lt] at this

noncomputable def ι.finsetDiff (i : Fin (s.dim + 1)) : Finset (Fin (n + 1)) :=
  s.finset i \ Finset.biUnion (Finset.filter (fun j ↦ j < i) Finset.univ) s.finset

@[simp]
lemma ι.finsetDiff_zero : s.finsetDiff 0 = s.finset 0 := by
  simp [finsetDiff]

lemma ι.finset_zero_ne_empty : s.finset 0 ≠ ∅ :=
  (SSet.stdSimplex.orderIsoN (s.simplex.obj 0)).2

lemma ι.disjoint_finsetDiff {i j : Fin (s.dim + 1)} (hij : i ≠ j) :
    Disjoint (s.finsetDiff i) (s.finsetDiff j) := by
  wlog h : j < i generalizing i j
  · exact (this hij.symm (by omega)).symm
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext k
  simp only [finsetDiff, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
    Finset.notMem_empty, iff_false, and_imp]
  exact fun _ h₂ h₃ ↦ (h₂ j h h₃).elim

noncomputable def ι.toι' : ι' n where
  d := s.dim
  S := s.finsetDiff
  hS₀ := by
    intro i
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · by_contra!
      exact s.finset_zero_ne_empty (by simpa using this)
    · have := s.strictMono_finset i.castSucc_lt_succ
      obtain ⟨a, h₁, h₂⟩ := (Finset.ssubset_iff_of_subset this.subset).1 this
      simp only [finsetDiff, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, not_exists, not_and, nonempty_subtype]
      refine ⟨a, h₁, fun j hj ↦ ?_⟩
      rw [← Fin.le_castSucc_iff] at hj
      intro h₃
      exact h₂ (s.strictMono_finset.monotone hj h₃)
  inter i j hij := s.disjoint_finsetDiff hij

end

noncomputable def cocone₁ := SSet.toTop.mapCocone (B.{u}.obj Δ[n]).coconeN'

noncomputable def isColimit₁ : IsColimit (cocone₁.{u} n) :=
  isColimitOfPreserves _ (B.obj Δ[n]).isColimitCoconeN'

lemma isColimit₁' : ((Functor.coconeTopEquiv _).symm (cocone₁.{u} n)).IsColimit :=
  (TopCat.isColimit_iff_coconeTopIsColimit (c := cocone₁.{u} n)).1 ⟨isColimit₁ n⟩

@[simps]
noncomputable def toStdSimplex (n : ℕ) :
    C(|B.obj (Δ[n] : SSet.{u})|, stdSimplex ℝ (Fin (n + 1))) where
  toFun x := ⟨(AffineMap.stdSimplex n).b.f x, by
    rw [← SimplexCategory.affineMap_stdSimplex_range_f.{u}]
    exact (AffineMap.stdSimplex.{u} n).range_b_f_subset_range_f (by simp)⟩
  continuous_toFun := (AffineMap.stdSimplex n).b.continuous.subtype_mk _

noncomputable def cocone₂ : ((B.{u}.obj Δ[n]).functorN' ⋙ SSet.toTop).CoconeTop :=
  ((Functor.coconeTopEquiv _).symm (cocone₁.{u} n)).postcomp (toStdSimplex.{u} n)

variable {n} in
lemma injective_cocone₂_ι (i : ι.{u} n) :
    Function.Injective ((cocone₂ n).ι i) := by
  dsimp [cocone₂, Functor.coconeTopEquiv, cocone₁, Functor.CoconeTop.postcomp,
    toStdSimplex]
  sorry

variable {n} in
lemma exists_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    ∃ (i : ι.{u} n), ∀ (j : ι.{u} n), x ∈ Set.range ((cocone₂ n).ι j) ↔
      i ≤ j :=
  sorry

instance (s : ι.{u} n) :
    CompactSpace ((((B.obj Δ[n]).functorN' ⋙ SSet.toTop) ⋙ forget TopCat).obj s) := by
  change CompactSpace (SSet.toTop.obj Δ[s.dim])
  infer_instance

instance : T2Space (cocone₂.{u} n).pt := by
  dsimp [cocone₂]
  infer_instance

variable {n} in
lemma isClosedEmbedding_cocone₂_ι (i : ι.{u} n) :
    IsClosedEmbedding ((cocone₂ n).ι i) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    ((cocone₂ n).continuous_ι i) (injective_cocone₂_ι i) ?_
  apply ((cocone₂ n).continuous_ι i).isClosedMap


lemma isColimit₂ : (cocone₂.{u} n).IsColimit := by
  refine (cocone₂.{u} n).isColimit_of_isClosedEmbedding
    ?_ isClosedEmbedding_cocone₂_ι ?_
  · ext x
    obtain ⟨i, hi⟩ := exists_iff.{u} x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_range]
    obtain ⟨y, hy⟩ := (hi i).2 le_rfl
    exact ⟨i, y, hy⟩
  · intro i₁ i₂ x₁ x₂ h
    generalize hy : (cocone₂ n).ι i₁ x₁ = y
    obtain ⟨i, hi⟩ := exists_iff.{u} y
    have h₁ := (hi i₁).1 ⟨x₁, hy⟩
    have h₂ := (hi i₂).1 ⟨x₂, by rw [← hy, h]⟩
    obtain ⟨z, hz⟩ := (hi i).2 le_rfl
    exact ⟨i, homOfLE h₁, homOfLE h₂, z,
      injective_cocone₂_ι i₁
        (((cocone₂ n).ι_naturality_apply (homOfLE h₁) z).trans (by rw [hz, hy])),
      injective_cocone₂_ι i₂
        (((cocone₂ n).ι_naturality_apply (homOfLE h₂) z).trans (by rw [hz, ← hy, h]))⟩

noncomputable def homeomorph :
    |B.obj (Δ[n] : SSet.{u})| ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (isColimit₁'.{u} n).ptUnique (isColimit₂ _)

lemma homeomorph_apply (x) : homeomorph.{u} n x = toStdSimplex.{u} n x := by
  apply (isColimit₁'.{u} n).funext'
  intro i
  ext x
  dsimp [homeomorph]
  erw [Functor.CoconeTop.IsColimit.ptUnique_ι]
  rfl

lemma isHomeomorph : IsHomeomorph (toStdSimplex.{u} n) := by
  convert (homeomorph.{u} n).isHomeomorph
  ext x : 1
  exact (homeomorph_apply.{u} n x).symm

end

lemma toStdSimplex_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) (x : |B.{u}.obj Δ[n]|) :
    toStdSimplex m (SSet.toTop.map (B.map (toSSet.map f)) x) =
      stdSimplex.map f.toOrderEmbedding (toStdSimplex n x) := by
  sorry

noncomputable def toStdSimplex' (n : ℕ) :
    |B.obj (Δ[n] : SSet.{u})| ⟶ toTop.obj ⦋n⦌ₛ :=
  TopCat.ofHom (⦋n⦌.toTopHomeo.symm.continuousMap.comp (toStdSimplex n))

lemma f_comp_toStdSimplex' (n : ℕ) :
    (AffineMap.stdSimplex n).f ∘ toStdSimplex' n =
      (AffineMap.stdSimplex n).b.f := by
  ext f : 1
  dsimp [toStdSimplex']
  erw [AffineMap.stdSimplex_f_toTopHomeo_symm]
  rfl

lemma f_comp_toStdSimplex'_apply {n : ℕ} (x) :
    (AffineMap.stdSimplex n).f (toStdSimplex' n x) =
      (AffineMap.stdSimplex n).b.f x :=
  congr_fun (f_comp_toStdSimplex' n) x

lemma toStdSimplex'_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) :
    SSet.toTop.map (B.map (toSSet.map f)) ≫ toStdSimplex' m =
      toStdSimplex' n ≫ toTop.map f := by
  ext x
  dsimp [toStdSimplex']
  erw [toStdSimplex_naturality f x,
    SimplexCategory.toTopHomeo_symm_naturality_apply (toSimplexCategory.map f)]
  rfl

instance (n : ℕ) : IsIso (toStdSimplex'.{u} n) :=
  (TopCat.isoOfHomeo ((isHomeomorph.{u} n).homeomorph.trans ⦋n⦌.toTopHomeo.symm)).isIso_hom

end BIso

noncomputable def BIso : toSSet ⋙ B ⋙ SSet.toTop ≅ toTop :=
  NatIso.ofComponents (fun n ↦ by
    induction n using SemiSimplexCategory.rec with | _ n =>
    exact asIso (BIso.toStdSimplex' n)) (by
    intro n m f
    induction n using SemiSimplexCategory.rec with | _ n =>
    induction m using SemiSimplexCategory.rec with | _ m =>
    exact BIso.toStdSimplex'_naturality f)

open Functor in
noncomputable def sdIso : sdToTop.{u} ≅ toTop :=
  isoWhiskerLeft _ (isoWhiskerRight stdSimplexCompBIso.symm _ ≪≫ (associator _ _ _)) ≪≫
    (associator _ _ _).symm ≪≫ BIso

end SemiSimplexCategory
