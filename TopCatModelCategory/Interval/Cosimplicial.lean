import TopCatModelCategory.Interval.Basic

universe u

open CategoryTheory Simplicial

lemma bot_ne_top_of_nontrivial (X : Type*) [PartialOrder X] [OrderBot X] [OrderTop X]
    [Nontrivial X] :
    (⊥ : X) ≠ ⊤ := by
  intro h
  have {x y : X} : x ≤ y := le_top.trans (le_trans (by rw [h]) bot_le)
  have : Subsingleton X := ⟨fun _ _ ↦ le_antisymm this this⟩
  exact false_of_nontrivial_of_subsingleton X

lemma nontrivial_subtype_of_orderBot_of_orderTop {X : Type*}
    [PartialOrder X] [OrderBot X] [OrderTop X] [Nontrivial X]
    (J : X → Prop) [OrderBot (Subtype J)] [OrderTop (Subtype J)]
    (hbot : (⊥ : Subtype J).1 = ⊥) (htop : (⊤ : Subtype J).1 = ⊤) :
    Nontrivial (Subtype J) where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦ bot_ne_top_of_nontrivial X
    (by rwa [Subtype.ext_iff, hbot, htop] at h)⟩

@[simps]
def OrderIso.toIntervalHom {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    [OrderBot X] [OrderBot Y] [OrderTop X] [OrderTop Y]
    (e : X ≃o Y) :
    IntervalHom X Y where
  orderHom := e.toOrderEmbedding.toOrderHom

def Fintype.exists_orderIso_fin_add_two_of_nontrivial
    (J : Type u) [Fintype J] [LinearOrder J] [Nontrivial J] :
    ∃ (n : ℕ), Nonempty (Fin (n + 2) ≃o J) := by
  generalize hn : Fintype.card J = n
  obtain _ | _ | n := n
  · simp at hn
  · simp only [zero_add] at hn
    have := (Fintype.orderIsoFinOfCardEq J hn).surjective.subsingleton
    exact (false_of_nontrivial_of_subsingleton J).elim
  exact ⟨n, ⟨Fintype.orderIsoFinOfCardEq J (by simpa)⟩⟩

namespace CategoryTheory

namespace Interval

def toCosimplicialObjectFunctor :
    Interval.{u} ⥤ CosimplicialObject (Type u) :=
  (SimplexCategory.toInterval.{u} ⋙ coyoneda).flip

variable (X : Interval.{u})

abbrev toCosimplicialObject : CosimplicialObject (Type u) :=
  toCosimplicialObjectFunctor.obj X

variable {X} in
def toCosimplicialObjectObjEquiv {n : SimplexCategory} :
    X.toCosimplicialObject.obj n ≃ IntervalHom (Fin (n.len + 2)) X where
  toFun f := f.hom.comp .toULift
  invFun g := homMk (g.comp .fromULift)

instance : Nonempty X.toCosimplicialObject.Elements :=
  ⟨⟨⦋0⦌, toCosimplicialObjectObjEquiv.symm (default : IntervalHom (Fin 2) X)⟩⟩

instance [Nontrivial X] :
    IsCofiltered X.toCosimplicialObject.Elements where
  cone_objs := by
    rintro ⟨x, f⟩ ⟨y, g⟩
    obtain ⟨f, rfl⟩ := toCosimplicialObjectObjEquiv.symm.surjective f
    obtain ⟨g, rfl⟩ := toCosimplicialObjectObjEquiv.symm.surjective g
    obtain ⟨J, hf, hg⟩ : ∃ (J : Finset X), (∀ i, f i ∈ J) ∧ (∀ i, g i ∈ J) :=
      ⟨Finset.image f .univ ⊔ Finset.image g .univ, by aesop⟩
    let _ : OrderBot J := Subtype.orderBot (by simpa using hf ⊥)
    let _ : OrderTop J := Subtype.orderTop (by simpa using hf ⊤)
    have : Nontrivial J := nontrivial_subtype_of_orderBot_of_orderTop _ rfl rfl
    obtain ⟨n, ⟨e⟩⟩ := Fintype.exists_orderIso_fin_add_two_of_nontrivial J
    let ι : IntervalHom J X := { orderHom := OrderHom.Subtype.val _ }
    let f' : IntervalHom (Fin (x.len + 2)) J :=
      { orderHom := ⟨fun i ↦ ⟨_, hf i⟩, fun _ _ h ↦ f.orderHom.monotone h ⟩ }
    let g' : IntervalHom (Fin (y.len + 2)) J :=
      { orderHom := ⟨fun i ↦ ⟨_, hg i⟩, fun _ _ h ↦ g.orderHom.monotone h ⟩ }
    obtain ⟨φ, hφ⟩ := (e.symm.toIntervalHom.comp f').exists_simplexCategoryHom
    obtain ⟨φ', hφ'⟩ := (e.symm.toIntervalHom.comp g').exists_simplexCategoryHom
    refine ⟨.mk ⦋n⦌ (toCosimplicialObjectObjEquiv.symm (ι.comp e.toIntervalHom)),
      CategoryOfElements.homMk _ _ φ ?_,
      CategoryOfElements.homMk _ _ φ' ?_, ⟨⟩⟩
    · dsimp
      sorry
    · dsimp
      sorry
  cone_maps := sorry

end Interval

end CategoryTheory
