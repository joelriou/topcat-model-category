import TopCatModelCategory.SemiSimplicial.SdIso

universe u

open CategoryTheory Simplicial Limits

abbrev SemiSimplexCategory.toSSet : SemiSimplexCategory ⥤ SSet.{u} :=
  toSimplexCategory ⋙ SSet.stdSimplex

namespace SSet

variable (X : SSet.{u}) [IsWeaklyPolyhedralLike X]

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

@[simps]
noncomputable def toSemiSimplexCategory : X.N ⥤ SemiSimplexCategory where
  obj s := ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono' (monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

end N

noncomputable abbrev functorN' : X.N ⥤ SSet :=
    N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSSet

open Functor in
@[simps! hom_app inv_app]
noncomputable def functorN'CompSdCompToTopIso :
    X.functorN' ⋙ sd ⋙ toTop ≅ X.functorN' ⋙ toTop :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _ ≪≫
    isoWhiskerLeft _ ((associator _ _ _).symm ≪≫
    isoWhiskerRight stdSimplex.sdIso.{u} toTop) ≪≫
    SemiSimplexCategory.sdIso ≪≫
    (isoWhiskerLeft _ toTopSimplex.symm ≪≫ (associator _ _ _).symm)) ≪≫
    (associator _ _ _).symm

noncomputable def functorN'Iso : X.functorN' ≅ X.functorN :=
  NatIso.ofComponents (fun x ↦ IsWeaklyPolyhedralLike.iso _ x.nonDegenerate)

@[simps]
noncomputable def coconeN' : Cocone X.functorN' where
  pt := X
  ι := { app s := yonedaEquiv.symm s.simplex }

noncomputable def isColimitCoconeN' : IsColimit X.coconeN' :=
  (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocones.ext (Iso.refl _))).1 X.isColimitCoconeN

@[simps! pt ι_app]
noncomputable def toTopSdIsoCocone : Cocone (X.functorN' ⋙ toTop) :=
  (Cocones.precompose X.functorN'CompSdCompToTopIso.inv).obj
    ((sd ⋙ toTop).mapCocone X.coconeN')

noncomputable def isColimitToTopSdIsoCocone : IsColimit X.toTopSdIsoCocone :=
  (IsColimit.precomposeInvEquiv X.functorN'CompSdCompToTopIso _).2
    (isColimitOfPreserves (sd ⋙ toTop) X.isColimitCoconeN')

noncomputable def toTopSdIso : |sd.obj X| ≅ |X| :=
  IsColimit.coconePointUniqueUpToIso X.isColimitToTopSdIsoCocone
    (isColimitOfPreserves toTop X.isColimitCoconeN')

variable {X} in
@[reassoc]
lemma N.toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom (x : X.N) :
    toTop.map (sd.map (yonedaEquiv.symm x.simplex)) ≫ X.toTopSdIso.hom =
    toTop.map (stdSimplex.sdIso.hom.app _) ≫ SemiSimplexCategory.sdIso.hom.app ⦋x.dim⦌ₛ ≫
      toTopSimplex.inv.app ⦋x.dim⦌ ≫ toTop.map (yonedaEquiv.symm x.simplex) := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom X.isColimitToTopSdIsoCocone
    (isColimitOfPreserves toTop X.isColimitCoconeN') x
  dsimp at this ⊢
  simp only [toTopSdIsoCocone_ι_app, Category.assoc] at this
  simp only [toTopSdIso, ← this, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc]

@[reassoc]
lemma toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) :
    toTop.map (sd.map (yonedaEquiv.symm x)) ≫ X.toTopSdIso.hom =
    toTop.map (stdSimplex.sdIso.hom.app _) ≫ SemiSimplexCategory.sdIso.hom.app ⦋n⦌ₛ ≫
      toTopSimplex.inv.app ⦋n⦌ ≫ toTop.map (yonedaEquiv.symm x) :=
  (N.mk _ hx).toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom

end SSet
