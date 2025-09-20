import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.RelativeT1CellComplex
import TopCatModelCategory.TopCat.CoyonedaPreservesCoproducts
import TopCatModelCategory.TopCat.ToTopDecomposition
import TopCatModelCategory.SSet.ConnectedComponents
import TopCatModelCategory.SSet.IsFiniteCoproducts
import TopCatModelCategory.CellComplex

universe u

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite

namespace SSet

variable {X : SSet.{u}} {K : TopCat.{u}} (f : K ⟶ |X|)

lemma exists_finite_subcomplex_of_compactSpace [CompactSpace K] :
    ∃ (A : X.Subcomplex) (_ : A.toSSet.IsFinite),
      Set.range f ⊆ Set.range (toTop.map A.ι) := by
  let hX := X.relativeCellComplex.map toTop
  let α := { c : hX.Cells // (TopCat.RelativeT₁CellComplex.interiorCell c ∩
    Set.range ⇑(ConcreteCategory.hom f)).Nonempty }
  have : Finite α := TopCat.RelativeT₁CellComplex.finite_inter_interiorCell_of_isCompact hX
    (fun j _ ↦ boundary.t₁Inclusions_toTop_map_ι j) (F := Set.range f) (by aesop)
    (isCompact_range (by continuity))
  let ι : Set X.N := (Sigma.fst ∘ X.sigmaEquivToTop.symm) '' (Set.range f)
  have : Finite ι := by
    let ψ (i : ι) : α := ⟨(X.relativeCellComplex.mapCellsEquiv _).symm
      (X.relativeCellComplexCellsEquiv.symm i.1), by
        obtain ⟨i, x, hx₁, hx₂⟩ := i
        refine ⟨x, ?_, hx₁⟩
        obtain ⟨⟨i', y⟩, rfl⟩ := sigmaEquivToTop.surjective x
        obtain rfl : i = i' := by simpa using hx₂.symm
        exact sigmaToTop_mem_interiorCell ⟨i, y⟩⟩
    refine Finite.of_injective ψ ?_
    rintro ⟨i, _⟩ ⟨i', _⟩ h
    rw [Subtype.ext_iff] at h ⊢
    exact ((X.relativeCellComplex.mapCellsEquiv toTop).trans
      X.relativeCellComplexCellsEquiv).symm.injective h
  let A : X.Subcomplex := ⨆ (s : ι), .ofSimplex s.1.simplex
  refine ⟨A, inferInstance, ?_⟩
  intro x hx
  obtain ⟨⟨s, y⟩, rfl⟩ := sigmaEquivToTop.surjective x
  let φ : Δ[s.dim] ⟶ A := yonedaEquiv.symm ⟨s.simplex, by
    simp only [Subpresheaf.iSup_obj, Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, A]
    refine ⟨s, ?_, 𝟙 _, by simp⟩
    obtain ⟨z, hz⟩ := hx
    exact ⟨f z, Set.mem_range_self z, by simp [hz]⟩⟩
  refine ⟨toTop.map φ (⦋s.dim⦌.toTopHomeo.symm y.1), ?_⟩
  simp only [sigmaEquivToTop_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma exists_factor_thru_finite_of_topCatHom [CompactSpace K] :
    ∃ (A : X.Subcomplex) (_ : A.toSSet.IsFinite)
      (g : K ⟶ |A|), f = g ≫ toTop.map A.ι := by
  obtain ⟨A, _, hA⟩ := exists_finite_subcomplex_of_compactSpace f
  exact ⟨A, inferInstance, TopCat.ofHom (ContinuousMap.comp
    ⟨_, (closedEmbeddings_toObj_map_of_mono A.ι).homeomorphRange.symm.continuous⟩
    ⟨fun k ↦ ⟨f k, hA (by simp)⟩, by continuity⟩), by aesop⟩

lemma exists_factor_thru_finite_of_topCatHom' [CompactSpace K] :
    ∃ (Y : SSet) (_ : Y.IsFinite) (i : Y ⟶ X) (_ : Mono i)
      (g : K ⟶ |Y|), f = g ≫ toTop.map i := by
  obtain ⟨A, _, g, rfl⟩ := exists_factor_thru_finite_of_topCatHom f
  exact ⟨_, inferInstance, A.ι, inferInstance, g, rfl⟩

lemma exists_factor_thru_finite_connected_of_topCatHom
    [CompactSpace K] [PathConnectedSpace K] :
    ∃ (Y : SSet) (_ : Y.IsFinite) (_ : Y.IsConnected) (i : Y ⟶ X) (_ : Mono i)
      (g : K ⟶ |Y|), f = g ≫ toTop.map i := by
  obtain ⟨Z, _, i, _, g, rfl⟩ := exists_factor_thru_finite_of_topCatHom' f
  obtain ⟨⟨c⟩, φ, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op (TopCat.of K)))
      (isColimitOfPreserves toTop (π₀.isColimitCofan Z))) g
  exact ⟨_, inferInstance, inferInstance, c.component.ι ≫ i, inferInstance, φ, by simp⟩

end SSet
