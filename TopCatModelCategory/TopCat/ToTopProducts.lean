import TopCatModelCategory.Convenient.SSet
import TopCatModelCategory.Convenient.Product
import TopCatModelCategory.Interval.Iso
import TopCatModelCategory.Flat

universe u

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X Y : C)

lemma preservesLimit_pair [PreservesLimit (pair X Y) F] :
    PreservesLimit (pair Y X) F := by
  let e : pair Y X ≅ (Discrete.equivalence WalkingPair.swap).functor ⋙ pair X Y :=
    mapPairIso (Iso.refl _) (Iso.refl _)
  exact preservesLimit_of_iso_diagram F e.symm

lemma preservesLimit_pair_iff_swap :
    PreservesLimit (pair X Y) F ↔ PreservesLimit (pair Y X) F := by
  constructor <;> apply preservesLimit_pair

lemma preservesLimit_pair_iff_of_cartesianMonoidal [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] :
    PreservesLimit (pair X Y) F ↔
      ∃ (e : F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y),
        e.hom ≫ fst _ _ = F.map (fst _ _) ∧
        e.hom ≫ snd _ _ = F.map (snd _ _) := by
  constructor
  · intro h
    let h₁ := (isLimitMapConeBinaryFanEquiv _ _ _).1
      (isLimitOfPreserves F (tensorProductIsBinaryProduct X Y))
    let h₂ := tensorProductIsBinaryProduct (F.obj X) (F.obj Y)
    exact ⟨h₁.conePointUniqueUpToIso h₂,
      (h₁.conePointUniqueUpToIso_hom_comp h₂) ⟨.left⟩,
      (h₁.conePointUniqueUpToIso_hom_comp h₂) ⟨.right⟩⟩
  · rintro ⟨e, h₁, h₂⟩
    exact preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct X Y)
      ((isLimitMapConeBinaryFanEquiv _ _ _).2
      (IsLimit.ofIsoLimit (tensorProductIsBinaryProduct (F.obj X) (F.obj Y))
      (BinaryFan.ext e h₁.symm h₂.symm).symm))

end CategoryTheory.Limits

namespace SSet

noncomputable def toTopSimplexForget :
    stdSimplex ⋙ (toTop.{u} ⋙ forget _) ≅ SimplexCategory.toTop ⋙ forget _ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight toTopSimplex.{u} (forget _)

instance : (toTop.{u} ⋙ forget _).IsLeftKanExtension toTopSimplexForget.inv := by
  rw [Presheaf.isLeftKanExtension_along_uliftYoneda_iff']
  constructor <;> infer_instance

instance : PreservesFiniteLimits (toTop.{u} ⋙ forget _) := by
  let τ : uliftYoneda.{u} ⋙ (toTop.{u} ⋙ forget _) ≅ SimplexCategory.toTop ⋙ forget _ :=
    toTopSimplexForget
  have : (toTop ⋙ forget TopCat).IsLeftKanExtension τ.inv :=
    inferInstanceAs ((toTop.{u} ⋙ forget _).IsLeftKanExtension toTopSimplexForget.inv)
  exact Presheaf.preservesFiniteLimits_of_isCofiltered_elements τ.inv

instance (p q : ℕ) : T2Space ((toTop.{u}.obj Δ[p] ⊗ toTop.{u}.obj Δ[q] :) : Type _) := by
  change T2Space (_ × _)
  infer_instance

instance preservesLimit_pair_stdSimplex_toTop (p q : ℕ) :
    PreservesLimit (pair Δ[p] Δ[q]) toTop.{u} := by
  have hpq : PreservesLimit (pair Δ[p] Δ[q]) (toTop.{u} ⋙ forget _) := inferInstance
  rw [preservesLimit_pair_iff_of_cartesianMonoidal ] at hpq ⊢
  obtain ⟨e, he₁, he₂⟩ := hpq
  let e : toTop.{u}.obj (Δ[p] ⊗ Δ[q]) ≃
    toTop.{u}.obj Δ[p] × toTop.{u}.obj Δ[q] := Iso.toEquiv e
  have he : Continuous e := by
    convert (CartesianMonoidalCategory.prodComparison toTop.{u} Δ[p] Δ[q]).hom.continuous
    ext x
    · exact congr_fun he₁ x
    · exact congr_fun he₂ x
  refine ⟨TopCat.isoOfHomeo (Continuous.homeoOfEquivCompactToT2 he), ?_, ?_⟩
  · ext x
    exact congr_fun he₁ x
  · ext x
    exact congr_fun he₂ x

instance preservesLimit_pair_stdSimplex_toDeltaGenerated (p q : ℕ) :
    PreservesLimit (pair Δ[p] Δ[q]) toDeltaGenerated.{u} :=
  preservesLimit_of_natIso _ toDeltaGeneratedIso.symm

lemma preservesLimit_pair_toDeltaGenerated' (X : SSet.{u})
    (hX : ∀ n, PreservesLimit (pair X Δ[n]) toDeltaGenerated) (Y : SSet.{u}) :
    PreservesLimit (pair X Y) toDeltaGenerated := by
  simp only [preservesLimit_pair_iff_of_cartesianMonoidal] at hX ⊢
  choose e₀ h₁ h₂ using hX
  have e₀_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
      toDeltaGenerated.map (X ◁ SSet.stdSimplex.map f) ≫ (e₀ m).hom =
        (e₀ n).hom ≫ toDeltaGenerated.obj X ◁ toDeltaGenerated.map (SSet.stdSimplex.map f) := by
    ext : 1
    · rw [Category.assoc, Category.assoc, h₁, whiskerLeft_fst, h₁,
        ← Functor.map_comp, whiskerLeft_fst]
    · rw [Category.assoc, Category.assoc, h₂, whiskerLeft_snd, reassoc_of% h₂,
        ← Functor.map_comp, whiskerLeft_snd, Functor.map_comp]
  let e₁ : stdSimplex ⋙ tensorLeft X ⋙ toDeltaGenerated ≅
      stdSimplex ⋙ toDeltaGenerated ⋙ tensorLeft (toDeltaGenerated.obj X) :=
    NatIso.ofComponents (fun n ↦ by
      induction n using SimplexCategory.rec with | _ n
      exact e₀ n) (fun {n m} f ↦ by
      induction n using SimplexCategory.rec with | _ n
      induction m using SimplexCategory.rec with | _ m
      apply e₀_naturality)
  have e₁_hom_app_fst (n : SimplexCategory) : e₁.hom.app n ≫ fst _ _ =
      toDeltaGenerated.map (fst _ _) := by
    induction n using SimplexCategory.rec with | _ n
    apply h₁
  have e₁_hom_app_snd (n : SimplexCategory) : e₁.hom.app n ≫ snd _ _ =
      toDeltaGenerated.map (snd _ _) := by
    induction n using SimplexCategory.rec with | _ n
    apply h₂
  let hc := Presheaf.colimitOfRepresentable Y
  let hc₁ := isColimitOfPreserves (tensorLeft X ⋙ toDeltaGenerated) hc
  let hc₂ := isColimitOfPreserves (toDeltaGenerated ⋙ tensorLeft (toDeltaGenerated.obj X)) hc
  let e₂ : Presheaf.functorToRepresentables Y ⋙ tensorLeft X ⋙ toDeltaGenerated ≅
      Presheaf.functorToRepresentables Y ⋙ toDeltaGenerated ⋙ tensorLeft (toDeltaGenerated.obj X) :=
    Functor.isoWhiskerLeft (CategoryOfElements.π Y).leftOp e₁
  let hc₂' := (IsColimit.precomposeHomEquiv e₂ _).2 hc₂
  have (j : Y.Elementsᵒᵖ) := hc₁.comp_coconePointUniqueUpToIso_hom hc₂' j
  dsimp at this
  refine ⟨hc₁.coconePointUniqueUpToIso hc₂', hc₁.hom_ext (fun j ↦ ?_), hc₁.hom_ext (fun j ↦ ?_)⟩
  · dsimp [e₂]
    rw [reassoc_of% this, ← Functor.map_comp]
    erw [e₁_hom_app_fst]
    rfl
  · dsimp [e₂]
    rw [reassoc_of% this, ← Functor.map_comp, whiskerLeft_snd, whiskerLeft_snd]
    erw [reassoc_of% e₁_hom_app_snd]
    rw [← Functor.map_comp]
    rfl

instance preservesLimit_pair_toDeltaGenerated (X Y : SSet.{u}) :
    PreservesLimit (pair X Y) toDeltaGenerated.{u} := by
  apply preservesLimit_pair_toDeltaGenerated'
  intro q
  rw [preservesLimit_pair_iff_swap]
  apply preservesLimit_pair_toDeltaGenerated'
  intro p
  infer_instance

instance : PreservesLimitsOfShape (Discrete WalkingPair) toDeltaGenerated.{u} where
  preservesLimit := preservesLimit_of_iso_diagram _ (diagramIsoPair _).symm

section

open DeltaGenerated' in
instance preservesLimit_pair_deltaGeneratedToTopCat (X Y : DeltaGenerated'.{u})
    [DeltaGeneratedSpace' ((DeltaGenerated'.toTopCat.obj X) × (DeltaGenerated'.toTopCat.obj Y))] :
    PreservesLimit (pair X Y) DeltaGenerated'.toTopCat := by
  let c : BinaryFan X Y := BinaryFan.mk
    (P := .of (toTopCat.obj X × toTopCat.obj Y)) (fst (C := TopCat) _ _) (snd (C := TopCat) _ _)
  let hc : IsLimit c := BinaryFan.IsLimit.mk _
    (fun f₁ f₂ ↦ lift (C := TopCat) f₁ f₂) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by
      intro _ f₁ f₂ m h₁ h₂
      ext t : 2
      apply Prod.ext
      · exact ConcreteCategory.congr_hom h₁ t
      · exact ConcreteCategory.congr_hom h₂ t)
  exact preservesLimit_of_preserves_limit_cone hc
    ((isLimitMapConeBinaryFanEquiv _ _ _).2
    (tensorProductIsBinaryProduct (toTopCat.obj X) (toTopCat.obj Y)))

variable (X Y : SSet.{u})

instance [DeltaGeneratedSpace' (|X| × |Y|)] :
    PreservesLimit (pair X Y) toTop :=
  preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct X Y) (by
    have : PreservesLimit (pair (GeneratedByTopCat.of ↑(toTop.obj X)) (GeneratedByTopCat.of ↑(toTop.obj Y)))
      DeltaGenerated'.toTopCat := by
        apply (config := { allowSynthFailures := true })
          preservesLimit_pair_deltaGeneratedToTopCat
        assumption
    have : PreservesLimit (pair X Y ⋙ toDeltaGenerated) DeltaGenerated'.toTopCat := by
      let e : pair X Y ⋙ toDeltaGenerated ≅
        pair (.of |X|) (.of |Y|) := mapPairIso (Iso.refl _) (Iso.refl _)
      exact preservesLimit_of_iso_diagram _ e.symm
    change IsLimit (DeltaGenerated'.toTopCat.mapCone
      (toDeltaGenerated.mapCone (BinaryFan.mk (fst X Y) (snd X Y))))
    apply isLimitOfPreserves
    apply isLimitOfPreserves
    apply tensorProductIsBinaryProduct)

end

end SSet
