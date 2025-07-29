import TopCatModelCategory.TopCat.Cosimp

universe u

open CategoryTheory Simplicial

namespace TopCat

variable (I : Type u) [Preorder I] [TopologicalSpace I]
  [OrderBot I] [OrderTop I]

namespace cosimp

def interior (n : SimplexCategory) : Set (obj I n) :=
  fun f ↦ StrictMono f.1

def map_mem_interior {m n : SimplexCategory} (f : m ⟶ n) [Epi f]
    (x : obj I m) (hx : x ∈ interior I m) :
    map I f x ∈ interior I n := by
  intro i j h
  exact hx (SimplexCategory.II.strictMono_map_unop f h)

def injective_map_interior_of_epi {m n : SimplexCategory} (f g : m ⟶ n) [Epi f] [Epi g]
    (x : obj I m) (hx : x ∈ interior I m)
    (h : map I f x = map I g x) : f = g := by
  apply SimplexCategory.II.map_injective
  apply Quiver.Hom.unop_inj
  ext i : 3
  apply hx.injective
  rw [Subtype.ext_iff] at h
  exact DFunLike.congr_fun h i

end cosimp

end TopCat
