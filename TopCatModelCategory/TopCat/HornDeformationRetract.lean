import TopCatModelCategory.TopCat.Adj

open CategoryTheory MorphismProperty TopCat Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen

namespace SSet

instance (n : ℕ) : T2Space |Δ[n]| := ⦋n⦌.toTopHomeo.symm.t2Space

def horn.deformationRetractToTopMap {n : ℕ} (i : Fin (n + 2)) :
    TopCat.DeformationRetract |horn (n + 1) i| |Δ[n + 1]| := sorry

@[simp]
lemma horn.deformationRetractToTopMap_i {n : ℕ} (i : Fin (n + 2)) :
    (horn.deformationRetractToTopMap i).i = toTop.map (horn (n + 1) i).ι := sorry

@[reassoc (attr := simp)]
lemma horn.ι_deformationRetractToTopMap_r {n : ℕ} (i : Fin (n + 2)) :
    toTop.map (horn (n + 1) i).ι ≫ (horn.deformationRetractToTopMap i).r = 𝟙 _ := by
  simpa only [deformationRetractToTopMap_i]
    using (horn.deformationRetractToTopMap i).retract


instance (Z : TopCat.{0}) : IsFibrant (TopCat.toSSet.obj Z) := by
  rw [isFibrant_iff, fibration_iff]
  intro _ _ _ hi
  simp only [J, iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  constructor
  intro t _ sq
  refine ⟨⟨
    { l := sSetTopAdj.homEquiv _ _
        ((horn.deformationRetractToTopMap i).r ≫ (sSetTopAdj.homEquiv _ _).symm t)
      fac_left := by
        simp [← Adjunction.homEquiv_naturality_left]
      fac_right := Subsingleton.elim _ _ }⟩⟩

end SSet
