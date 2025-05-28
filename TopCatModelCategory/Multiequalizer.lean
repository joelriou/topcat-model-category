import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
# Preservation of multicoequalizers

Let `J : MultispanShape` and `d : MultispanIndex J C`.
If `F : C ⥤ D`, we define `d.map F : MultispanIndex J D` and
an isomorphism of functors `(d.map F).multispan ≅ d.multispan ⋙ F`
(see `MultispanIndex.multispanMapIso`).
If `c : Multicofork d`, we define `c.map F : Multicofork (d.map F)` and
obtain a bijection `IsColimit (F.mapCocone c) ≃ IsColimit (c.map F)`
(see `Multicofork.isColimitMapEquiv`). As a result, if `F` preserves
the colimit of `d.multispan`, we deduce that if `c` is a colimit,
then `c.map F` also is (see `Multicofork.isColimitMapOfPreserves`).

-/

universe w w' v u

/-namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Limits

variable {J : MultispanShape.{w, w'}} (d : MultispanIndex J C)
  (c : Multicofork d) (F : C ⥤ D)

variable {d} in
/-- Constructor for isomorphisms between multicoforks. -/
@[simps!]
def Multicofork.ext {K K' : Multicofork d}
    (e : K.pt ≅ K'.pt) (h : ∀ (i : J.R), K.π i ≫ e.hom = K'.π i := by aesop_cat) :
    K ≅ K' :=
  Cocones.ext e (by rintro (i | j) <;> simp [h])

/-- The multispan index obtained by applying a functor. -/
@[simps]
def MultispanIndex.map : MultispanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

/-- If `d : MultispanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multispan ≅ d.multispan ⋙ F`. -/
@[simps!]
def MultispanIndex.multispanMapIso : (d.map F).multispan ≅ d.multispan ⋙ F :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

variable {d}

/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
this is the induced multicofork of `d.map F`. -/
@[simps!]
def Multicofork.map : Multicofork (d.map F) :=
  Multicofork.ofπ _ (F.obj c.pt) (fun i ↦ F.map (c.π i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
the cocone `F.mapCocone c` is colimit iff the multicofork `c.map F` is. -/
def Multicofork.isColimitMapEquiv :
    IsColimit (F.mapCocone c) ≃ IsColimit (c.map F) :=
  (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multicofork.π]; simp)))

/-- If `d : MultispanIndex J C`, `c : Multicofork d` is a colimit multicofork,
and `F : C ⥤ D` is a functor which preserves the colimit of `d.multispan`,
then the multicofork `c.map F` is colimit, -/
noncomputable def Multicofork.isColimitMapOfPreserves
    [PreservesColimit d.multispan F] (hc : IsColimit c) : IsColimit (c.map F) :=
  (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

end Limits

end CategoryTheory-/

namespace CategoryTheory

namespace Limits

variable {C D : Type*} [Category C] [Category D]

variable {J : MultispanShape.{w, w'}} {d₁ d₂ : MultispanIndex J C}
  (c₂ : Multicofork d₂) (φ : d₁.multispan ⟶ d₂.multispan)

namespace Multicofork

namespace isColimitPrecomposeObjOfIsIsoOfEpi

noncomputable abbrev multicofork
    (hR : ∀ (i : J.R), IsIso (φ.app (.right i)))
    (hL : ∀ (i : J.L), Epi (φ.app (.left i)))
    (s : Multicofork d₁) : Multicofork d₂ :=
  Multicofork.ofπ _ s.pt (fun i ↦ (inv (φ.app (.right i))) ≫ s.π i) (fun i ↦ by
    have h₁ := φ.naturality (WalkingMultispan.Hom.fst i)
    have h₂ := φ.naturality (WalkingMultispan.Hom.snd i)
    rw [← cancel_epi (φ.app (.left i))]
    dsimp at h₁ h₂ ⊢
    rw [← reassoc_of% h₁, ← reassoc_of% h₂,
      IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc, condition])

end isColimitPrecomposeObjOfIsIsoOfEpi

open isColimitPrecomposeObjOfIsIsoOfEpi in
variable {c₂} in
noncomputable def isColimitPrecomposeObjOfIsIsoOfEpi (hc₂ : IsColimit c₂)
    (hR : ∀ (i : J.R), IsIso (φ.app (.right i)))
    (hL : ∀ (i : J.L), Epi (φ.app (.left i))) :
    IsColimit ((Cocones.precompose φ).obj c₂) :=
  Multicofork.IsColimit.mk _ (fun s ↦ hc₂.desc (multicofork φ hR hL s))
    (fun s i ↦ by
      have := hc₂.fac (multicofork φ hR hL s) (.right i)
      dsimp at this
      dsimp [Cocones.precompose]
      rw [← cancel_epi (inv (φ.app (.right i))), ← this, Multicofork.π]
      simp)
    (fun s m hm ↦ Multicofork.IsColimit.hom_ext hc₂ (fun i ↦ by
      have := hc₂.fac (multicofork φ hR hL s) (.right i)
      dsimp at this ⊢
      rw [this, ← hm]
      dsimp only [Cocones.precompose, Multicofork.π]
      simp))

end Multicofork

namespace MultispanIndex.multispan

@[simps]
def homMk (l : ∀ i, d₁.left i ⟶ d₂.left i) (r : ∀ i, d₁.right i ⟶ d₂.right i)
    (h₁ : ∀ i, d₁.fst i ≫ r (J.fst i) = l i ≫ d₂.fst i)
    (h₂ : ∀ i, d₁.snd i ≫ r (J.snd i) = l i ≫ d₂.snd i) :
    d₁.multispan ⟶ d₂.multispan where
  app i := match i with
    | .left i => l i
    | .right i => r i
  naturality := by rintro (i | i) (j | j) (_ | _ | _) <;> aesop

end MultispanIndex.multispan

end Limits

end CategoryTheory
