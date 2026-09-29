module

public import TopCatModelCategory.SSet.Pseudofunctor
public import TopCatModelCategory.PseudoFunctor.MorphismProperty
public import TopCatModelCategory.SSet.KanComplexW

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen Simplicial

namespace SSet

namespace KanComplex

open MorphismProperty

section

variable {X X' Y Y' : SSet.{u}} [IsFibrant X] [IsFibrant X'] [IsFibrant Y] [IsFibrant Y']
  {f : X ⟶ X'} {g : Y ⟶ Y'} (r : RetractArrow f g)

include r

lemma isEquivalence_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).IsEquivalence] :
    (mapFundamentalGroupoid f).IsEquivalence := by
  let W := MorphismProperty.ofPseudofunctor FundamentalGroupoid.pseudofunctor.{u}
  let f' : KanComplexCat.mk X ⟶ KanComplexCat.mk X' := f
  let g' : KanComplexCat.mk Y ⟶ KanComplexCat.mk Y' := g
  have hg' : W g' := by assumption
  change W f'
  exact of_retract
    { i := Arrow.homMk (by exact r.left.i) (by exact r.right.i) r.i.w
      r := Arrow.homMk (by exact r.left.r) (by exact r.right.r) r.r.w
      retract := by
        ext
        · exact r.left.retract
        · exact r.right.retract } hg'
end

instance : W.{u}.IsStableUnderRetracts where
  of_retract {X X' Y Y' f g} r hg := by
    have := hg.isFibrant_src
    have := hg.isFibrant_tgt
    have := isFibrant_of_retract r.left
    have := isFibrant_of_retract r.right
    refine W.mk _ ?_ ?_
    · have := hg.isEquivalence
      exact isEquivalence_mapFundamentalGroupoid_of_retract r
    · intro n x x' h
      rw [← isIso_iff_bijective]
      apply of_retract (P := isomorphisms (Type u))
        (retractArrowMapπ r n x x' h _ _ rfl rfl)
      simp only [isomorphisms.iff]
      rw [isIso_iff_bijective]
      apply hg.bijective

end KanComplex

end SSet
