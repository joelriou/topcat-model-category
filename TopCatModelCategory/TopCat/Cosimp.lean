import TopCatModelCategory.II
import TopCatModelCategory.TopCat.TopologyOrderHom
import Mathlib.Topology.Category.TopCat.Basic

universe u

open CategoryTheory

lemma Topology.IsInducing.subtype {X : Type*} [TopologicalSpace X] (p : X → Prop) :
    Topology.IsInducing (Subtype.val (p := p)) where
  eq_induced := rfl

namespace TopCat

variable (I : Type u) [Preorder I] [TopologicalSpace I]
  [OrderBot I] [OrderTop I]

namespace cosimp

abbrev obj (n : SimplexCategory) : Type u :=
  { f : Fin (n.len + 2) →o I // f 0 = ⊥ ∧ f (Fin.last _) = ⊤ }

@[continuity]
lemma continuous_apply {n : SimplexCategory} (a : Fin (n.len + 2)) :
    Continuous (fun (f : obj I n) ↦ f.1 a) :=
  (OrderHom.continuous_apply I a).comp continuous_induced_dom

variable {n m : SimplexCategory}

@[simps]
def map (f : n ⟶ m) : obj I n → obj I m :=
  fun g ↦ ⟨g.1.comp (SimplexCategory.II.map f).unop.toOrderHom,
    by simpa [SimplexCategory.II] using g.2.1,
    by simpa [SimplexCategory.II] using g.2.2⟩

lemma continuous_map (f : n ⟶ m) : Continuous (map I f) := by
  rw [(Topology.IsInducing.subtype _).continuous_iff,
    OrderHom.continuous_iff]
  continuity

end cosimp

def cosimp : CosimplicialObject TopCat.{u} where
  obj n := TopCat.of (cosimp.obj I n)
  map f := ConcreteCategory.ofHom ⟨cosimp.map I f, cosimp.continuous_map I f⟩

end TopCat
