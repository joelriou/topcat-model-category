module

public import TopCatModelCategory.SSet.PtSimplex

@[expose] public section

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite
  SSet.modelCategoryQuillen

universe u

namespace SSet

namespace KanComplex

def π (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  Subcomplex.RelativeMorphism.HomotopyClass
    (boundary n) (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

def π.mk {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
  (f : X.PtSimplex n x) : π n X x := f.homotopyClass

lemma π.mk_surjective {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌} :
    Function.Surjective (π.mk : _ → π n X x) :=
  Quot.mk_surjective

instance (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : One (π n X x) where
  one := Subcomplex.RelativeMorphism.const.homotopyClass

section

variable {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
  (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y)

def mapπ (p : π n X x) : π n Y y :=
  p.postcomp (.ofSimplex₀ f x y h) (by rw [comp_const])

@[simp]
lemma mapπ_mk (z : X.PtSimplex n x) :
    mapπ f n x y h (π.mk z) = π.mk (z.pushforward f y h) := rfl

variable {Z : SSet.{u}} (g : Y ⟶ Z) (z : Z _⦋0⦌) (h' : g.app _ y = z)

lemma mapπ_mapπ (p : π n X x) :
    mapπ g n y z h' (mapπ f n x y h p) =
      mapπ (f ≫ g) n x z (by simp [h, h']) p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

lemma mapπ_comp_mapπ :
    mapπ g n y z h' ∘ mapπ f n x y h = mapπ (f ≫ g) n x z (by simp [h, h']) := by
  ext
  apply mapπ_mapπ

@[simp]
lemma mapπ_id (p : π n X x) :
    mapπ (𝟙 X) n x x rfl p = p := by
  obtain ⟨h, rfl⟩ := p.eq_homotopyClass
  rfl

@[simps]
def mapπEquivOfIso (e : X ≅ Y) (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : e.hom.app _ x = y) :
    π n X x ≃ π n Y y where
  toFun := mapπ e.hom n x y h
  invFun := mapπ e.inv n y x (by simp [← h])
  left_inv _ := by simp [mapπ_mapπ]
  right_inv _ := by simp [mapπ_mapπ]

end

namespace π

variable {X : SSet.{u}}  {x : X _⦋0⦌} {n : ℕ} [IsFibrant X]

-- assume we do not already not that the general homotopy relation
-- is an equivalence relation
lemma mk_eq_mk_iff {p q : X.PtSimplex n x} :
    mk p = mk q ↔ Nonempty (p.RelStruct₀ q) := by
  apply Quot.eq.trans
  constructor
  · intro r
    induction r with
    | rel p q h =>
      change Nonempty (p.Homotopy q) at h
      exact ⟨h.some.relStruct₀⟩
    | refl p => exact ⟨.refl _⟩
    | symm _ _ _ h => exact ⟨h.some.symm⟩
    | trans _ _ _ _ _ h₁ h₂ => exact ⟨h₁.some.trans h₂.some⟩
  · rintro ⟨h⟩
    exact Relation.EqvGen.rel _ _ ⟨h.homotopy⟩

lemma mk_eq_one_iff (p : X.PtSimplex n x) :
    mk p = 1 ↔ Nonempty (p.RelStruct₀ .const) :=
  mk_eq_mk_iff

noncomputable def mul' (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    X.PtSimplex (n + 1) x :=
  (PtSimplex.MulStruct.nonempty p q i).choose

noncomputable def mulStruct (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    PtSimplex.MulStruct p q (mul' p q i) i :=
  (PtSimplex.MulStruct.nonempty p q i).choose_spec.some

noncomputable def mul (i : Fin (n + 1)) (g₁ g₂ : π (n + 1) X x) : π (n + 1) X x := by
  refine Quot.lift₂ (fun p q ↦ mk (mul' p q i)) ?_ ?_ g₁ g₂
  · rintro p q q' ⟨h : q.Homotopy q'⟩
    rw [mk_eq_mk_iff]
    exact ⟨PtSimplex.MulStruct.unique (mulStruct p q i) (mulStruct p q' i)
      (.refl p) h.relStruct₀⟩
  · rintro p p' q ⟨h : p.Homotopy p'⟩
    rw [mk_eq_mk_iff]
    exact ⟨PtSimplex.MulStruct.unique (mulStruct p q i) (mulStruct p' q i)
      h.relStruct₀ (.refl q)⟩

lemma mul_eq_of_mulStruct {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ i) : mul i (mk g₁) (mk g₂) = mk g₁₂ := by
  change mk _ = mk _
  rw [mk_eq_mk_iff]
  exact ⟨PtSimplex.MulStruct.unique (mulStruct g₁ g₂ i) h (.refl g₁) (.refl g₂)⟩

lemma mul_mk_eq_iff {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    mul i (mk g₁) (mk g₂) = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ i) := by
  constructor
  · intro h
    change mk _ = mk _ at h
    rw [mk_eq_mk_iff] at h
    exact ⟨PtSimplex.MulStruct.unique' (mulStruct g₁ g₂ i) h.some⟩
  · rintro ⟨h⟩
    exact mul_eq_of_mulStruct h

lemma mul_assoc (i : Fin (n + 1)) (g₁ g₂ g₃ : π (n + 1) X x) :
    mul i (mul i g₁ g₂) g₃ = mul i g₁ (mul i g₂ g₃) := by
  obtain ⟨p₁, rfl⟩ := g₁.mk_surjective
  obtain ⟨p₂, rfl⟩ := g₂.mk_surjective
  obtain ⟨p₃, rfl⟩ := g₃.mk_surjective
  exact mul_eq_of_mulStruct
    (PtSimplex.MulStruct.assoc (mulStruct p₁ p₂ i) (mulStruct p₂ p₃ i)
      (mulStruct p₁ (mul' p₂ p₃ i) i))

@[simp]
lemma one_mul (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i 1 g = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.oneMul p i)

@[simp]
lemma mul_one (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i g 1 = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.mulOne p i)

lemma exists_left_inverse (i : Fin (n + 1)) (f : π (n + 1) X x) :
    ∃ g, mul i g f = 1 := by
  obtain ⟨p, rfl⟩ := f.mk_surjective
  obtain ⟨q, ⟨h⟩⟩ := PtSimplex.MulStruct.exists_left_inverse p i
  exact ⟨_, mul_eq_of_mulStruct h⟩

noncomputable def inv (i : Fin (n + 1)) (f : π (n + 1) X x) : π (n + 1) X x :=
  (exists_left_inverse i f).choose

@[simp]
lemma inv_mul (i : Fin (n + 1)) (f : π (n + 1) X x) :
    mul i (inv i f) f = 1 := (exists_left_inverse i f).choose_spec

noncomputable instance : Mul (π (n + 1) X x) where
  mul := mul (Fin.last _)

noncomputable instance : Group (π (n + 1) X x) where
  mul_assoc := mul_assoc (Fin.last _)
  one_mul := one_mul (Fin.last _)
  mul_one := mul_one (Fin.last _)
  inv := inv (Fin.last _)
  inv_mul_cancel _ := inv_mul _ _

end π

section

variable {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (n : ℕ)
  (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y)

lemma mapπ_mul' (i : Fin (n + 1)) (p q : π (n + 1) X x) :
    mapπ f (n + 1) x y h (π.mul i p q) =
    π.mul i (mapπ f (n + 1) x y h p) (mapπ f (n + 1) x y h q) := by
  obtain ⟨p, rfl⟩ := p.mk_surjective
  obtain ⟨q, rfl⟩ := q.mk_surjective
  exact (π.mul_eq_of_mulStruct ((π.mulStruct p q i).pushforward f y h)).symm

lemma mapπ_mul (p q : π (n + 1) X x) :
    mapπ f (n + 1) x y h (p * q) =
      mapπ f (n + 1) x y h p * mapπ f (n + 1) x y h q := by
  apply mapπ_mul'

omit [IsFibrant X] [IsFibrant Y] in
@[simp]
lemma mapπ_one : mapπ f n x y h 1 = 1 := by
  change π.mk _ = π.mk _
  congr 1
  aesop

lemma mapπ_inv (p : π (n + 1) X x) :
    mapπ f (n + 1) x y h (p⁻¹) = (mapπ f (n + 1) x y h p)⁻¹ := by
  symm
  rw [← inv_mul_eq_one, inv_inv, ← mapπ_mul, mul_inv_cancel, mapπ_one]

end


end KanComplex

open KanComplex

lemma PtSimplex.MulStruct.mul_eq {X : SSet.{u}} [IsFibrant X] {n : ℕ} {x : X _⦋0⦌}
    {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ (Fin.last _)) : π.mk g₁ * π.mk g₂ = π.mk g₁₂ :=
  KanComplex.π.mul_eq_of_mulStruct h

end SSet
