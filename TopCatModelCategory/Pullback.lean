import Mathlib.CategoryTheory.Comma.Over.Pullback

universe u

open CategoryTheory

namespace Types

variable {E B : Type u} (f : E → B)

@[simps]
def overPullback : Over B ⥤ Over E where
  obj S := Over.mk (Y := { x : S.left × E // S.hom x.1 = f x.2}) (fun x ↦ x.1.2)
  map φ := Over.homMk (fun x ↦ ⟨⟨φ.left x.1.1, x.1.2⟩, by
    simpa only [← x.2] using congr_fun (Over.w φ) x.1.1⟩)

@[simps]
def overPushout : Over E ⥤ Over B where
  obj T := Over.mk
    (Y := Σ (b : B), { g : f ⁻¹' {b} → T.left // ∀ e, T.hom (g e) = e.1 }) Sigma.fst
  map {T T'} φ := Over.homMk (fun ⟨b, g, hg⟩ ↦ ⟨b, φ.left.comp g, fun e ↦ by
    simpa [hg] using congr_fun (Over.w φ) (g e)⟩)

variable {f} in
lemma overPushout_left_ext {T : Over E} {t t' : ((overPushout f).obj T).left}
    (h₁ : t.1 = t'.1) (h₂ : ∀ (e : E) (he : f e = t.1),
      t.2.1 ⟨e, he⟩ = t'.2.1 ⟨e, by simp [h₁, he]⟩): t = t' := by
  obtain ⟨t, g, _⟩ := t
  obtain ⟨t', g', _⟩ := t'
  obtain rfl : t = t' := h₁
  obtain rfl : g = g' := by ext ⟨e, he⟩; apply h₂
  rfl

def overPushoutAdjunction : overPullback f ⊣ overPushout f :=
  .mkOfHomEquiv
    { homEquiv S T :=
        { toFun φ := Over.homMk (fun s ↦ ⟨S.hom s, fun ⟨x, hx⟩ ↦ φ.left ⟨⟨s, x⟩, by aesop⟩,
              fun _ ↦ congr_fun (Over.w φ) _⟩)
          invFun ψ := Over.homMk
            (fun ⟨⟨s, e⟩, h⟩ ↦ (ψ.left s).2.1 ⟨e, h.symm.trans (congr_fun (Over.w ψ).symm _)⟩) (by
              ext ⟨⟨s, e⟩, h⟩
              exact (ψ.left s).2.2 ⟨e, h.symm.trans (congr_fun (Over.w ψ).symm _)⟩)
          left_inv _ := rfl
          right_inv ψ := by
            ext s
            exact overPushout_left_ext (congr_fun (Over.w ψ).symm s) (fun e he ↦ rfl)
            }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

end Types
