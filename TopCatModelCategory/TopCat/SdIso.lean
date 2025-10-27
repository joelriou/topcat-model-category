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

@[simp]
lemma orderIsoN_card {n : ℕ} (σ : (Δ[n] : SSet.{u}).N) :
    (orderIsoN σ).1.card = σ.dim + 1 := by
  simp [orderIsoN, Finset.card_image_of_injective (f := σ.simplex) _
    (nonDegenerateEquiv ⟨σ.simplex, σ.nonDegenerate⟩).injective]

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

lemma stdSimplex.isAffine_map {d : ℕ} {X : Type*} [Fintype X]
    (f : Fin (d + 1) → X) :
    stdSimplex.IsAffine (Subtype.val ∘ stdSimplex.map (S := ℝ) f) := by
  classical
  intro g
  ext x
  simp [map, FunOnFinite.linearMap_apply_apply]
  conv_rhs => rw [← Finset.sum_subset (s₁ := { y | f y = x}) (by simp) (by aesop)]
  exact Finset.sum_congr rfl (by aesop)

namespace SSet.AffineMap

variable {n : ℕ}

lemma stdSimplex_vertex_vertexOfSimplex
    {d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (stdSimplex n).vertex (vertexOfSimplex s i) = Pi.single (s i) 1 := by
  let α := (⦋0⦌.const ⦋n⦌ (s i))
  refine ((stdSimplex n).precomp_vertex
    (SSet.stdSimplex.{u}.map α) default).symm.trans ?_
  simp [AffineMap.vertex, AffineMap.φ, IsAffineAt.φ, precomp, stdSimplex]
  erw [SimplexCategory.toTopHomeo_naturality_apply α]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0),
    stdSimplex.map_vertex]
  rfl

lemma stdSimplex_vertex {n : ℕ} (s : Δ[n] _⦋0⦌) :
    (AffineMap.stdSimplex.{u} n).vertex s = Pi.single (stdSimplex.obj₀Equiv s) 1 := by
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective s
  exact stdSimplex_vertex_vertexOfSimplex (stdSimplex.obj₀Equiv.symm i) 0

lemma stdSimplex_φ {d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    (AffineMap.stdSimplex n).φ s = Subtype.val ∘ _root_.stdSimplex.map s := by
  refine stdSimplex.IsAffine.ext ?_ ?_ (fun i ↦ ?_)
  · exact (stdSimplex n).isAffine s
  · exact stdSimplex.isAffine_map s
  · simp [AffineMap.φ_vertex, stdSimplex_vertex_vertexOfSimplex]

end SSet.AffineMap

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
  hS₀ i : (S i).Nonempty
  disjoint {i j} (hij : i ≠ j) : Disjoint (S i) (S j)

variable {n} in
noncomputable def isobary (S : Finset (Fin (n + 1))) (a : Fin (n + 1)) : ℝ :=
  if a ∈ S then S.card⁻¹ else 0

variable {n} in
lemma isobary_apply_eq_zero (S : Finset (Fin (n + 1))) (a : Fin (n + 1))
    (ha : a ∉ S) :
    isobary S a = 0 :=
  if_neg ha

variable {n} in
lemma isobary_apply_eq (S : Finset (Fin (n + 1))) (a : Fin (n + 1))
    (ha : a ∈ S) :
    isobary S a = (S.card⁻¹ : ℝ) :=
  if_pos ha

variable {n} in
lemma isobary_orderIsoN_apply (σ : Δ[n].N) :
    isobary (SSet.stdSimplex.orderIsoN σ).1 =
      (AffineMap.stdSimplex n).isobarycenter σ.toS := by
  ext a
  have ha : a ∈ (SSet.stdSimplex.orderIsoN σ).1 ↔ a ∈ Set.range σ.simplex := by
    simp [SSet.stdSimplex.orderIsoN]
  by_cases ha' : a ∈ (SSet.stdSimplex.orderIsoN σ).1
  · rw [isobary_apply_eq _ _ ha']
    rw [ha, Set.mem_range] at ha'
    obtain ⟨i, rfl⟩ := ha'
    simp only [ne_eq, stdSimplex.orderIsoN_card, Nat.cast_add, Nat.cast_one]
    dsimp [AffineMap.isobarycenter]
    rw [SSet.AffineMap.stdSimplex_φ]
    dsimp
    rw [FunOnFinite.linearMap_apply_apply_of_injective _ _ _
      (by exact (stdSimplex.nonDegenerateEquiv ⟨σ.simplex, σ.nonDegenerate⟩).injective)]
    dsimp [stdSimplex.isobarycenter]
    rw [Finset.sum_eq_single (a := i) _ (by simp),
      Fintype.card_fin, Nat.cast_add, Nat.cast_one, one_div, Pi.single_eq_same, mul_one]
    intro j _ hj
    simp [Pi.single_eq_of_ne' hj]
  · rw [isobary_apply_eq_zero _ _ ha']
    rw [ha] at ha'
    dsimp only [AffineMap.isobarycenter]
    rw [SSet.AffineMap.stdSimplex_φ]
    dsimp
    rw [FunOnFinite.linearMap_apply_apply, Finset.sum_eq_zero]
    intro i hi
    exact (ha' ⟨i, by simpa using hi⟩).elim

namespace ι

variable {n} (s : ι.{u} n)

noncomputable def finset (i : Fin (s.dim + 1)) : Finset (Fin (n + 1)) :=
  (SSet.stdSimplex.orderIsoN (s.simplex.obj i)).1

lemma strictMono_finset : StrictMono s.finset := by
  intro i j hij
  have := (PartialOrder.mem_nonDegenerate_iff s.simplex).1 s.nonDegenerate hij
  rwa [← stdSimplex.orderIsoN.lt_iff_lt] at this

lemma monotone_finset : Monotone s.finset := s.strictMono_finset.monotone

noncomputable def finsetDiff (i : Fin (s.dim + 1)) : Finset (Fin (n + 1)) :=
  s.finset i \ Finset.biUnion (Finset.filter (fun j ↦ j < i) Finset.univ) s.finset

lemma notMem_finsetDiff {j i : Fin (s.dim + 1)} {x : Fin (n + 1)} (hj : x ∈ s.finset j)
    (h : j < i):
    x ∉ s.finsetDiff i := by
  intro hx
  simp only [finsetDiff, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, not_exists, not_and] at hx
  exact hx.2 _ h hj

@[simp]
lemma finsetDiff_zero : s.finsetDiff 0 = s.finset 0 := by
  simp [finsetDiff]

lemma finsetDiff_subset_finset (i : Fin (s.dim + 1)) :
    s.finsetDiff i ⊆ s.finset i :=
  Finset.sdiff_subset

lemma finset_eq_biUnion (i : Fin (s.dim + 1)) :
    s.finset i = Finset.biUnion { j | j ≤ i } s.finsetDiff := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    let S : Finset (Fin (s.dim + 1)) := {j | x ∈ s.finset j}
    have hS : S.Nonempty := ⟨i, by simpa [S]⟩
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨S.min' hS, S.min'_le _ (by simpa [S]), ?_⟩
    simp only [finsetDiff, Finset.lt_min'_iff, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    exact ⟨by simpa [S] using S.min'_mem hS,
      fun k hk hk' ↦ (lt_self_iff_false k).1
        (lt_of_lt_of_le (hk _ (S.min'_mem hS)) (S.min'_le k (by simpa [S])))⟩
  · simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    intro j h
    exact (s.finsetDiff_subset_finset j).trans (s.monotone_finset h)

@[simp]
lemma finset_ne_empty (i : Fin (s.dim + 1)) :
    ¬ s.finset i = ∅ :=
  (SSet.stdSimplex.orderIsoN (s.simplex.obj i)).2

lemma disjoint_finsetDiff {i j : Fin (s.dim + 1)} (hij : i ≠ j) :
    Disjoint (s.finsetDiff i) (s.finsetDiff j) := by
  wlog h : j < i generalizing i j
  · exact (this hij.symm (by omega)).symm
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext k
  simp only [finsetDiff, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
    Finset.notMem_empty, iff_false, and_imp]
  exact fun _ h₂ h₃ ↦ (h₂ j h h₃).elim

lemma pairwiseDisjoint_finsetDiff :
    Set.PairwiseDisjoint (.univ : Finset (Fin (s.dim + 1))) s.finsetDiff :=
  fun _ _ _ _ ↦ s.disjoint_finsetDiff

lemma card_finset_eq_sum (i : Fin (s.dim + 1)) :
    (s.finset i).card = ∑ j with j ≤ i, (s.finsetDiff j).card := by
  rw [← Finset.card_disjiUnion _ _ (fun _ _ _ _ ↦ s.disjoint_finsetDiff),
    Finset.disjiUnion_eq_biUnion, finset_eq_biUnion]

lemma nonempty_finsetDiff (i) : (s.finsetDiff i).Nonempty := by
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simp [Finset.nonempty_iff_ne_empty]
  · have := s.strictMono_finset i.castSucc_lt_succ
    obtain ⟨a, h₁, h₂⟩ := (Finset.ssubset_iff_of_subset this.subset).1 this
    simp [Finset.nonempty_def, finsetDiff]
    refine ⟨a, h₁, fun j hj ↦ ?_⟩
    rw [← Fin.le_castSucc_iff] at hj
    intro h₃
    exact h₂ (s.monotone_finset hj h₃)

noncomputable def toι' : ι' n where
  d := s.dim
  S := s.finsetDiff
  hS₀ := s.nonempty_finsetDiff
  disjoint := s.disjoint_finsetDiff

end ι

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

@[simps! pt]
noncomputable def cocone₂ : ((B.{u}.obj Δ[n]).functorN' ⋙ SSet.toTop).CoconeTop :=
  ((Functor.coconeTopEquiv _).symm (cocone₁.{u} n)).postcomp (toStdSimplex.{u} n)

namespace ι

variable {n} (σ : ι.{u} n)
noncomputable def affineMap :=
  (AffineMap.stdSimplex n).b.precomp (yonedaEquiv.symm σ.simplex)

lemma cocone₂_ι :
    Subtype.val ∘ (cocone₂ n).ι σ = σ.affineMap.f :=
  rfl

noncomputable def φ :
    _root_.stdSimplex ℝ (Fin (σ.dim + 1)) → (Fin (n + 1) → ℝ) :=
  (AffineMap.stdSimplex n).b.φ σ.simplex

lemma φ_eq : σ.φ = stdSimplex.affineMap (fun s ↦ isobary (σ.finset s)) := by
  simp only [φ, AffineMap.b_φ, AffineMap.b.affineMap]
  congr
  ext s : 1
  rw [← isobary_orderIsoN_apply]
  rfl

lemma φ_vertex (s : Fin (σ.dim + 1)) :
    σ.φ (stdSimplex.vertex s) = isobary (σ.finset s) := by
  simp [φ_eq]

lemma val_comp_cocone₂_ι :
    Subtype.val ∘ ((cocone₂ n).ι σ) = σ.φ ∘ ⦋σ.dim⦌.toTopHomeo := by
  ext x : 1
  dsimp at x
  simp [cocone₂, Functor.coconeTopEquiv, cocone₁, φ, toStdSimplex, AffineMap.φ, IsAffineAt.φ]
  apply congr_arg
  apply congr_arg
  exact (⦋σ.dim⦌.toTopHomeo.symm_apply_apply x).symm

lemma mem_range_cocone₂_ι_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    x ∈ Set.range ((cocone₂ n).ι σ) ↔ x.1 ∈ Set.range σ.φ := by
  constructor
  · rintro ⟨x, rfl⟩
    have := congr_fun (σ.val_comp_cocone₂_ι) x
    dsimp at this
    rw [this]
    apply Set.mem_range_self
  · obtain ⟨x, hx⟩ := x
    rintro ⟨x, rfl⟩
    dsimp
    refine ⟨⦋σ.dim⦌.toTopHomeo.symm x, ?_⟩
    rw [Subtype.ext_iff]
    have := congr_fun (σ.val_comp_cocone₂_ι) (⦋σ.dim⦌.toTopHomeo.symm x)
    dsimp at this ⊢
    rw [this]
    erw [Homeomorph.apply_symm_apply]

lemma φ_apply_eq_zero (v : stdSimplex ℝ (Fin (σ.dim + 1))) (i : Fin (n + 1))
    (hi : ∀ a, i ∉ σ.finsetDiff a) :
    σ.φ v i = 0 := by
  simp only [φ_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_zero]
  intro j _
  rw [isobary_apply_eq_zero, mul_zero]
  rw [finset_eq_biUnion]
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
  tauto

lemma φ_apply (v : stdSimplex ℝ (Fin (σ.dim + 1))) {i : Fin (n + 1)} {a : Fin (σ.dim + 1)}
    (h : i ∈ σ.finsetDiff a) :
    σ.φ v i = ∑ (b : Fin (σ.dim + 1)) with a ≤ b, v b * ((σ.finset b).card : ℝ)⁻¹ := by
  simp only [φ_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_subset (s₁ := { b | a ≤ b}) (by simp) (fun b _ hb ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hb
    rw [isobary_apply_eq_zero, mul_zero]
    intro hb'
    exact σ.notMem_finsetDiff hb' hb h)]
  refine Finset.sum_congr rfl (fun b hb ↦ ?_)
  simp at hb
  congr 1
  rw [isobary_apply_eq]
  have := σ.finsetDiff_subset_finset a h
  exact σ.monotone_finset hb (σ.finsetDiff_subset_finset a h)

lemma eq_of_mem_finsetDiff_last
    (v : stdSimplex ℝ (Fin (σ.dim + 1))) {i : Fin (n + 1)}
    (h : i ∈ σ.finsetDiff (Fin.last _)) :
    v (Fin.last _) = (σ.finset (Fin.last _)).card * σ.φ v i := by
  rw [σ.φ_apply v h, Finset.sum_eq_single (a := Fin.last _) (by simp) (by simp),
    mul_comm (v _), ← mul_assoc, mul_inv_cancel₀ (by simp), one_mul]

lemma _root_.Finset.filter_finCastSucc_le {n : ℕ} (a : Fin n):
    Finset.filter (fun b ↦ a.castSucc ≤ b) .univ =
      insert a.castSucc (Finset.filter (fun b ↦ a.succ ≤ b) .univ) := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    obtain h | rfl := h.lt_or_eq
    · exact Or.inr (by rwa [← Fin.castSucc_lt_iff_succ_le])
    · exact Or.inl rfl
  · rintro (h | h)
    · rw [h]
    · exact a.castSucc_le_succ.trans h

lemma eq_of_mem_finsetDiff_succ
    (v : stdSimplex ℝ (Fin (σ.dim + 1))) {i j : Fin (n + 1)} {a : Fin σ.dim}
    (hi : i ∈ σ.finsetDiff a.castSucc) (hj : j ∈ σ.finsetDiff a.succ) :
    v a.castSucc = (σ.finset a.castSucc).card * (σ.φ v i - σ.φ v j) := by
  rw [σ.φ_apply _ hi, σ.φ_apply _ hj, Finset.filter_finCastSucc_le,
    Finset.sum_insert (by simp), add_sub_cancel_right, mul_comm (v _),
    ← mul_assoc, mul_inv_cancel₀ (by simp), one_mul]

lemma injective_φ : Function.Injective σ.φ := by
  intro v₁ v₂ hv
  choose i hi using fun a ↦ σ.nonempty_finsetDiff a
  ext a
  induction a using Fin.reverseInduction with
  | last =>
    rw [σ.eq_of_mem_finsetDiff_last v₁ (hi _),
      σ.eq_of_mem_finsetDiff_last v₂ (hi _), hv]
  | cast a ha =>
    rw [σ.eq_of_mem_finsetDiff_succ v₁ (hi a.castSucc) (hi a.succ),
      σ.eq_of_mem_finsetDiff_succ v₂ (hi a.castSucc) (hi a.succ), hv]

lemma injective_cocone₂_ι :
    Function.Injective ((cocone₂ n).ι σ) := by
  apply Function.Injective.of_comp (f := Subtype.val)
  rw [val_comp_cocone₂_ι]
  exact Function.Injective.comp σ.injective_φ (Homeomorph.injective _)

lemma _root_.Fin.exists_sum_ge {A : Type*} [AddCommGroup A] {n : ℕ}
    (f : Fin (n + 1) → A) :
    ∃ (g : Fin (n + 1) → A),
      ∀ (i : Fin (n + 1)), f i = ∑ j with i ≤ j, g j :=
  ⟨Fin.reverseInduction (f (Fin.last _))
    (fun i _ ↦ f i.castSucc - f i.succ), by
      intro i
      induction i using Fin.reverseInduction with
      | last =>
        rw [Finset.sum_eq_single (a := Fin.last _) (by simp) (by simp)]
        simp
      | cast i hi =>
        simp [Finset.filter_finCastSucc_le, ← hi]⟩

lemma mem_range_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    x ∈ Set.range ((cocone₂ n).ι σ) ↔
      ∃ (f : Fin (σ.dim + 1) → ℝ) (_ : Antitone f),
        (∀ (i : Fin (σ.dim + 1)),
          ∀ (j : Fin (n + 1)), j ∈ σ.finsetDiff i → x j = f i) ∧
        ∀ (j : Fin (n + 1)) (_ : ∀ (i : Fin (σ.dim + 1)), j ∉ σ.finsetDiff i), x j = 0 := by
  rw [mem_range_cocone₂_ι_iff]
  choose i hi using fun a ↦ σ.nonempty_finsetDiff a
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, h₁⟩ := x
    obtain ⟨x, rfl⟩ := h
    refine ⟨fun a ↦ σ.φ x (i a), ?_, fun a k ha ↦ ?_, σ.φ_apply_eq_zero _ ⟩
    · rw [Fin.antitone_iff_succ_le]
      intro a
      rw [σ.φ_apply _ (hi _), σ.φ_apply _ (hi _), Finset.filter_finCastSucc_le]
      simp only [Finset.mem_filter, Finset.mem_univ, Fin.succ_le_castSucc_iff, lt_self_iff_false,
        and_false, not_false_eq_true, Finset.sum_insert, le_add_iff_nonneg_left]
      exact mul_nonneg (by simp) (by positivity)
    · dsimp only [DFunLike.coe]
      rw [σ.φ_apply _ ha, σ.φ_apply _ (hi a)]
  · rintro ⟨f, hf, h₁, h₂⟩
    obtain ⟨g, hg⟩ := Fin.exists_sum_ge f
    refine ⟨⟨fun a ↦ g a * (σ.finset a).card, fun a ↦ ?_, ?_⟩, ?_⟩
    · refine mul_nonneg ?_ (by simp)
      obtain ⟨a, rfl⟩ | rfl := a.eq_castSucc_or_eq_last
      · simpa [hg, Finset.filter_finCastSucc_le] using hf a.castSucc_le_succ
      · have := hg (Fin.last _)
        rw [Finset.sum_eq_single (a := Fin.last _) (by simp) (by simp)] at this
        rw [← this, ← h₁ _ _ (hi (Fin.last _))]
        exact x.2.1 _
    · trans ∑ j, (σ.finsetDiff j).card * f j
      · simp only [hg, card_finset_eq_sum, Nat.cast_sum, Finset.mul_sum]
        rw [Finset.sum_sigma' (t := fun j ↦ { i | i ≤ j }) (f := fun i j ↦
          g i * (σ.finsetDiff j).card),
          Finset.sum_sigma' (t := fun j ↦ { i | j ≤ i }) (f := fun i j ↦
           (σ.finsetDiff i).card * g j)]
        exact Finset.sum_equiv (e :=
          { toFun x := ⟨x.2, x.1⟩
            invFun x := ⟨x.2, x.1⟩
            left_inv _ := rfl
            right_inv _ := rfl }) (by simp) (fun _ _ ↦ mul_comm _ _)
      · rw [← x.2.2, ← Finset.sum_subset
          (s₁ := Finset.disjiUnion _ _ (σ.pairwiseDisjoint_finsetDiff))
          (by simp) (fun i _ hi ↦ by exact h₂ _ (by simpa using hi)),
          Finset.sum_disjiUnion]
        congr 1
        ext i
        trans (∑ j ∈ σ.finsetDiff i, 1) * f i
        · simp
        · simp only [Finset.sum_mul, one_mul]
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact (h₁ i j hj).symm
    · ext j
      by_cases hj : ∃ a, j ∈ σ.finsetDiff a
      · obtain ⟨a, ha⟩ := hj
        dsimp
        rw [σ.φ_apply _ ha, h₁ _ _ ha]
        simp only [hg]
        dsimp only [DFunLike.coe]
        apply Finset.sum_congr rfl
        intro b hb
        rw [mul_assoc, mul_inv_cancel₀ (by simp), mul_one]
      · simp at hj
        have := h₂ j hj
        dsimp only [DFunLike.coe] at this
        rw [this, σ.φ_apply_eq_zero _ _ hj]

end ι

namespace ι'

variable {n} (t : ι' n)

def finset (i : Fin (t.d + 1)) : Finset (Fin (n + 1)) :=
  Finset.biUnion {j | j ≤ i} t.S

lemma subset_finset_of_le {i j : Fin (t.d + 1)} (h : j ≤ i) :
    t.S j ⊆ t.finset i := by
  intro x hx
  simp only [finset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, h, hx⟩

lemma nonempty_finset (i : Fin (t.d + 1)) : (t.finset i).Nonempty :=
  Finset.Nonempty.mono (t.subset_finset_of_le (Fin.zero_le i)) (t.hS₀ 0)

noncomputable def simplexObj (k : Fin (t.d + 1)) :=
  stdSimplex.orderIsoN.symm ⟨t.finset k, by
    simpa only [Finset.nonempty_iff_ne_empty] using t.nonempty_finset k⟩

lemma strictMono_simplexObj : StrictMono t.simplexObj := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  dsimp only [simplexObj]
  simp only [ne_eq, OrderIso.lt_iff_lt, Subtype.mk_lt_mk, Finset.lt_eq_subset, Finset.ssubset_iff]
  obtain ⟨x, hx⟩ := t.hS₀ i.succ
  refine ⟨x, ?_, fun y hy ↦ ?_⟩
  · simp only [finset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists, not_and]
    intro j hj h
    exact (Finset.disjoint_iff_ne.1 (t.disjoint (by rintro rfl; simp at hj))) _ h _ hx rfl
  · simp only [finset, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and] at hy
    obtain rfl | ⟨j, hj, hj'⟩ := hy
    · exact t.subset_finset_of_le le_rfl hx
    · exact t.subset_finset_of_le (hj.trans i.castSucc_le_succ) hj'

noncomputable def simplex : (B.{u}.obj Δ[n]) _⦋t.d⦌ :=
  t.strictMono_simplexObj.monotone.functor

lemma nonDegenerate : t.simplex ∈ SSet.nonDegenerate _ _ := by
  dsimp [B]
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  exact t.strictMono_simplexObj

noncomputable def toι : ι.{u} n := N.mk t.simplex t.nonDegenerate

end ι'

namespace exists'

variable {n} (x : stdSimplex ℝ (Fin (n + 1)))

noncomputable def values : Finset ℝ := (Finset.image x .univ) \ {0}

variable {x} in
lemma exists_of_mem_values {y : ℝ} (hy : y ∈ values x) :
    (∃ i, x i = y) ∧ y ≠ 0 := by
  simpa [values] using hy

lemma nonempty_values : (values x).Nonempty  := by
  sorry

lemma exists_card_values_eq_succ :
    ∃ (d : ℕ), (values x).card = d + 1 := by
  simpa using nonempty_values x

variable {x}

lemma exists_strictAnti {d : ℕ} (hd : (values x).card = d + 1) :
    ∃ (φ : Fin (d + 1) ≃ values x), StrictAnti φ := sorry

variable {d : ℕ} (φ : Fin (d + 1) ≃ values x)

noncomputable def S (a : Fin (d + 1)) : Finset (Fin (n + 1)) :=
  { i | x i = φ a }

@[simp]
lemma mem_S_iff (a : Fin (d + 1)) (i : Fin (n + 1)) :
    i ∈ S φ a ↔ x i = φ a := by
  simp [S]

lemma nonempty_S (a : Fin (d + 1)) :
    (S φ a).Nonempty := by
  obtain ⟨⟨i, h₁⟩, h₂⟩ := exists_of_mem_values (φ a).2
  exact ⟨i, by simpa⟩

variable {φ} (hφ : StrictAnti φ)

noncomputable def t : ι' n where
  d := d
  S := S φ
  hS₀ := nonempty_S φ
  disjoint {i j} hij := by
    rw [Finset.disjoint_iff_ne]
    rintro a h₁ _ h₂ rfl
    simp only [mem_S_iff] at h₁ h₂
    exact hij (hφ.injective (by rw [Subtype.ext_iff, ← h₁, h₂]))

lemma mem_range : x ∈ Set.range ((cocone₂ n).ι (t hφ).toι) := by
  rw [ι.mem_range_iff]
  refine ⟨fun i ↦ φ i, hφ.antitone, ?_, ?_⟩
  · sorry
  · sorry

end exists'

open exists' in
variable {n} in
lemma exists' (x : stdSimplex ℝ (Fin (n + 1))) :
    ∃ (σ₀ : ι.{u} n) (h₀ : x ∈ Set.range ((cocone₂ n).ι σ₀)),
      ∀ (σ : ι.{u} n), x ∈ Set.range ((cocone₂ n).ι σ) → σ₀ ≤ σ := by
  obtain ⟨d, hd⟩ := exists_card_values_eq_succ x
  obtain ⟨φ, hφ⟩ := exists_strictAnti hd
  refine ⟨(t hφ).toι, mem_range hφ, ?_⟩
  sorry

variable {n} in
lemma exists_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    ∃ (σ₀ : ι.{u} n), ∀ (σ : ι.{u} n), x ∈ Set.range ((cocone₂ n).ι σ) ↔ σ₀ ≤ σ := by
  obtain ⟨σ₀, h₀, h⟩ := exists'.{u} x
  refine ⟨σ₀, fun σ ↦ ⟨h σ, fun hσ ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := h₀
  exact ⟨_, (cocone₂ n).ι_naturality_apply (homOfLE hσ) x⟩

instance (σ : ι.{u} n) :
    CompactSpace ((((B.obj Δ[n]).functorN' ⋙ SSet.toTop) ⋙ forget TopCat).obj σ) := by
  change CompactSpace (SSet.toTop.obj Δ[σ.dim])
  infer_instance

instance : T2Space (cocone₂.{u} n).pt := by
  dsimp [cocone₂]
  infer_instance

variable {n} in
lemma isClosedEmbedding_cocone₂_ι (σ : ι.{u} n) :
    IsClosedEmbedding ((cocone₂ n).ι σ) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    ((cocone₂ n).continuous_ι σ) σ.injective_cocone₂_ι ?_
  apply ((cocone₂ n).continuous_ι σ).isClosedMap


lemma isColimit₂ : (cocone₂.{u} n).IsColimit := by
  refine (cocone₂.{u} n).isColimit_of_isClosedEmbedding ?_ isClosedEmbedding_cocone₂_ι ?_
  · ext x
    obtain ⟨i, hi⟩ := exists_iff.{u} x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_range]
    obtain ⟨y, hy⟩ := (hi i).2 le_rfl
    exact ⟨i, y, hy⟩
  · intro (i₁ : ι _) (i₂ : ι n) x₁ x₂ h
    generalize hy : (cocone₂ n).ι i₁ x₁ = y
    obtain ⟨i, hi⟩ := exists_iff.{u} y
    have h₁ := (hi i₁).1 ⟨x₁, hy⟩
    have h₂ := (hi i₂).1 ⟨x₂, by rw [← hy, h]⟩
    obtain ⟨z, hz⟩ := (hi i).2 le_rfl
    exact ⟨i, homOfLE h₁, homOfLE h₂, z,
      i₁.injective_cocone₂_ι
        (((cocone₂ n).ι_naturality_apply (homOfLE h₁) z).trans (by rw [hz, hy])),
      i₂.injective_cocone₂_ι
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

section

variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {X : SSet.{u}}
  (f : X.AffineMap E) (x : X.N)

lemma isAffine_φ_comp_toStdSimplex :
    IsAffine (f.φ x.simplex ∘ toStdSimplex x.dim) := by
  obtain ⟨l, hl⟩ :=
    (f.isAffine x.simplex).exists_linearMap
  simpa only [hl] using ((AffineMap.stdSimplex x.dim).b.isAffine.postcomp l)

lemma b_f_comp_toTop_map [X.IsWeaklyPolyhedralLike] :
    f.b.f ∘ SSet.toTop.map (B.map (yonedaEquiv.symm x.simplex)) =
      f.φ x.simplex ∘ toStdSimplex x.dim := by
  obtain ⟨l, hl : f.φ x.simplex = _⟩ := (f.isAffine x.simplex).exists_linearMap
  have : f.precomp (SSet.yonedaEquiv.symm x.simplex) =
      (AffineMap.stdSimplex.{u} x.dim).postcomp l := by
    ext i
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective i
    have h := f.φ_vertex x.simplex i
    rw [hl] at h
    dsimp at h
    simp only [AffineMap.postcomp_vertex]
    rw [AffineMap.precomp_vertex, AffineMap.stdSimplex_vertex,
      Equiv.apply_symm_apply, h]
    rfl
  suffices f.b.precomp (B.map (yonedaEquiv.symm x.simplex)) =
      (AffineMap.stdSimplex.{u} x.dim).b.postcomp l by
    simpa only [hl] using congr_arg AffineMap.f this
  ext y : 1
  simp
  rw [toS_mapN_of_mono, ← AffineMap.isobarycenter_precomp, this]
  rfl

end

lemma toStdSimplex_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) (y : |B.{u}.obj Δ[n]|) :
    toStdSimplex m (SSet.toTop.map (B.map (toSSet.map f)) y) =
      stdSimplex.map f.toOrderEmbedding (toStdSimplex n y) := by
  let x : (Δ[m] : SSet.{u}).N :=
    N.mk (n := n) (stdSimplex.objEquiv.symm (toSimplexCategory.map f)) (by
      rw [stdSimplex.mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply]
      infer_instance)
  have : toSSet.{u}.map f = yonedaEquiv.symm x.simplex := rfl
  rw [Subtype.ext_iff, this]
  refine (congr_fun (b_f_comp_toTop_map (AffineMap.stdSimplex m) x) y).trans ?_
  rw [AffineMap.stdSimplex_φ]
  rfl

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
