import TopCatModelCategory.SSet.Subdivision
import TopCatModelCategory.SemiSimplexCategory

universe u

open CategoryTheory Simplicial Limits

abbrev SemiSimplexCategory.toSSet : SemiSimplexCategory ⥤ SSet.{u} :=
  toSimplexCategory ⋙ SSet.stdSimplex

namespace SSet

variable (X : SSet.{u}) [IsWeaklyPolyhedralLike X]
  {Y : SSet.{u}} [IsWeaklyPolyhedralLike Y]

namespace N

section

variable {X} {x y z : X.N}

lemma existsUnique_of_le (h : x ≤ y) :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2 :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := (le_iff_exists ..).1 h
    exact ⟨f, inferInstance, hf⟩) (by
    rintro f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩
    exact injective_map_of_nonDegenerate _ y.nonDegenerate (by rw [hf₁, hf₂]))

noncomputable def monoOfLE (h : x ≤ y) : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_of_le h).exists.choose

instance (h : x ≤ y) : Mono (monoOfLE h) :=
  (existsUnique_of_le h).exists.choose_spec.1

@[simp]
lemma map_monoOfLE (h : x ≤ y) : X.map (monoOfLE h).op y.simplex = x.simplex :=
  (existsUnique_of_le h).exists.choose_spec.2

@[simp]
lemma stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (h : x ≤ y) :
    stdSimplex.map (monoOfLE h) ≫ yonedaEquiv.symm y.simplex =
      yonedaEquiv.symm x.simplex := by
  rw [← SSet.yonedaEquiv_symm_map, map_monoOfLE]

lemma monoOfLE_eq_iff (h : x ≤ y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g] :
    monoOfLE h = g ↔ X.map g.op y.simplex = x.simplex :=
  ⟨by rintro rfl; simp,
    fun h' ↦ (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

variable (x) in
@[simp]
lemma monoOfLE_refl : monoOfLE (le_refl x) = 𝟙 _ := by
  simp [monoOfLE_eq_iff]

@[reassoc (attr := simp)]
lemma monoOfLE_comp (h : x ≤ y) (h' : y ≤ z) :
    monoOfLE h ≫ monoOfLE h' = monoOfLE (h.trans h') := by
  symm
  simp [monoOfLE_eq_iff]

end

@[simps obj map]
noncomputable def toSemiSimplexCategory : X.N ⥤ SemiSimplexCategory where
  obj s := ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono' (monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

end N

noncomputable abbrev functorN' : X.N ⥤ SSet :=
    N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSSet.{u}

noncomputable def functorN'Iso : X.functorN' ≅ X.functorN :=
  NatIso.ofComponents (fun x ↦ IsWeaklyPolyhedralLike.iso _ x.nonDegenerate)

@[simps]
noncomputable def coconeN' : Cocone X.functorN' where
  pt := X
  ι := { app s := yonedaEquiv.symm s.simplex }

noncomputable def isColimitCoconeN' : IsColimit X.coconeN' :=
  (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocones.ext (Iso.refl _))).1 X.isColimitCoconeN

instance : PreservesColimit X.functorN' B :=
  preservesColimit_of_iso_diagram _ X.functorN'Iso.symm

end SSet
