import TopCatModelCategory.II
import TopCatModelCategory.TopCat.TopologyOrderHom
import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Fin.Tuple

universe u

open CategoryTheory Simplicial

lemma Topology.IsInducing.subtype {X : Type*} [TopologicalSpace X] (p : X → Prop) :
    Topology.IsInducing (Subtype.val (p := p)) where
  eq_induced := rfl

namespace TopCat

section

variable (I : Type u) [Preorder I] [TopologicalSpace I]
  [OrderBot I] [OrderTop I]

namespace cosimp

abbrev obj (n : SimplexCategory) : Type u :=
  { f : Fin (n.len + 2) →o I // f 0 = ⊥ ∧ f (Fin.last _) = ⊤ }

variable {I} in
@[simps]
def obj₁OrderIso : I ≃o obj I ⦋1⦌ where
  toFun x := ⟨⟨![⊥, x, ⊤], by aesop⟩, by aesop⟩
  invFun f := f.1 1
  left_inv _ := rfl
  right_inv f := by
    ext i
    fin_cases i
    · exact f.2.1.symm
    · rfl
    · exact f.2.2.symm
  map_rel_iff' {f g} := by simp [OrderHom.le_def, Fin.forall_fin_succ]

variable {I} in
@[simps]
def obj₂Equiv : { x : I × I // x.1 ≤ x.2} ≃ obj I ⦋2⦌ where
  toFun x := ⟨⟨![⊥, x.1.1, x.1.2, ⊤], by aesop⟩, by aesop⟩
  invFun f := ⟨⟨f.1 1, f.1 2⟩, f.1.2 (by simp)⟩
  left_inv _ := rfl
  right_inv f := by
    ext i
    fin_cases i
    · exact f.2.1.symm
    · rfl
    · rfl
    · exact f.2.2.symm

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

@[simps]
def cosimp : CosimplicialObject TopCat.{u} where
  obj n := TopCat.of (cosimp.obj I n)
  map f := ConcreteCategory.ofHom ⟨cosimp.map I f, cosimp.continuous_map I f⟩

end

section

variable {I₁ I₂ I₃ : Type u}
  [Preorder I₁] [TopologicalSpace I₁] [OrderBot I₁] [OrderTop I₁]
  [Preorder I₂] [TopologicalSpace I₂] [OrderBot I₂] [OrderTop I₂]
  [Preorder I₃] [TopologicalSpace I₃] [OrderBot I₃] [OrderTop I₃]
  (f : I₁ →o I₂) (hf : Continuous f) (hf₀ : f ⊥ = ⊥) (hf₁ : f ⊤ = ⊤)

def cosimp.action (n : SimplexCategory) :
    cosimp.obj I₁ n → cosimp.obj I₂ n :=
  fun x ↦ ⟨f.comp x.1, by simp [x.2.1, hf₀], by simp [x.2.2, hf₁]⟩

include hf in
lemma cosimp.continuous_action (n : SimplexCategory) :
    Continuous (cosimp.action f hf₀ hf₁ n) := by
  rw [(Topology.IsInducing.subtype _).continuous_iff,
    OrderHom.continuous_iff]
  continuity

@[simps]
def cosimpAction : cosimp I₁ ⟶ cosimp I₂ where
  app n := ConcreteCategory.ofHom ⟨cosimp.action f hf₀ hf₁ n,
    cosimp.continuous_action f hf hf₀ hf₁ n⟩

@[reassoc]
lemma cosimpAction_comp (g : I₂ →o I₃) (hg : Continuous g) (hg₀ : g ⊥ = ⊥) (hg₁ : g ⊤ = ⊤) :
      cosimpAction f hf hf₀ hf₁ ≫ cosimpAction g hg hg₀ hg₁ =
    cosimpAction (g.comp f) (hg.comp hf) (by simp [hf₀, hg₀]) (by simp [hf₁, hg₁]) :=
  rfl

variable (I₁) in
lemma cosimpAction_id :
    cosimpAction (OrderHom.id : I₁ →o I₁) (by continuity) rfl rfl = 𝟙 _ :=
  rfl

lemma cosimpAction_injective
    (g : I₁ →o I₂) (hg : Continuous g) (hg₀ : g ⊥ = ⊥) (hg₁ : g ⊤ = ⊤)
    (H : cosimpAction f hf hf₀ hf₁ = cosimpAction g hg hg₀ hg₁) : f = g := by
  ext x
  exact congr_arg cosimp.obj₁OrderIso.symm
    (congr_fun ((forget _).congr_map (NatTrans.congr_app H ⦋1⦌))
    (cosimp.obj₁OrderIso x))

namespace cosimp

def φ {n : ℕ} (i : Fin (n + 2)) :
    ⦋n⦌ ⟶ ⦋1⦌ :=
  SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{0} i)

lemma φ_eq_zero {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    φ i j = 0 :=
  if_pos h

lemma φ_eq_one {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    φ i j = 1 :=
  if_neg (by simpa using h)

omit [TopologicalSpace I₁] in
lemma hφ {n : ℕ} (i : Fin (n + 1)) (x : obj I₁ ⦋n⦌) :
    cosimp.map I₁ (cosimp.φ i.castSucc) x = cosimp.obj₁OrderIso (x.1 i.castSucc) := by
  apply cosimp.obj₁OrderIso.symm.injective
  rw [OrderIso.symm_apply_apply]
  dsimp
  erw [obj₁OrderIso_symm_apply]
  dsimp [map]
  congr
  dsimp [SimplexCategory.II]
  rw [SimplexCategory.II.map'_eq_castSucc_iff]
  constructor
  · erw [φ_eq_one] <;> simp
  · intro j hj
    erw [φ_eq_zero]
    · simp
    · simpa

end cosimp

lemma cosimp_comp_forget_hom_ext
    {f g : cosimp I₁ ⋙ forget _ ⟶ cosimp I₂ ⋙ forget _}
    (h : f.app ⦋1⦌ = g.app ⦋1⦌) : f = g := by
  ext n x
  induction' n using SimplexCategory.rec with n
  dsimp
  apply Subtype.ext
  ext i
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · have (α : cosimp I₁ ⋙ forget TopCat ⟶ cosimp I₂ ⋙ forget TopCat) :
      (α.app ⦋n⦌ x).1 i.castSucc =
          cosimp.obj₁OrderIso.symm (α.app ⦋1⦌ (cosimp.obj₁OrderIso (x.1 i.castSucc))) := by
        have : α.app _ (cosimp.map I₁ (cosimp.φ i.castSucc) x) =
            (cosimp.map I₂ (cosimp.φ i.castSucc) (α.app _ x)) :=
          congr_fun ((forget _).congr_map (α.naturality (cosimp.φ i.castSucc))) x
        dsimp at this
        rw [cosimp.hφ, cosimp.hφ] at this
        rw [this, OrderIso.symm_apply_apply]
    simp only [this, h]
  · exact (f.app ⦋n⦌ x).2.2.trans ((g.app ⦋n⦌ x).2.2).symm

lemma cosimp_hom_ext
    {f g : cosimp I₁ ⟶ cosimp I₂}
    (h : f.app ⦋1⦌ = g.app ⦋1⦌) : f = g := by
  have : whiskerRight f (forget _) = whiskerRight g (forget _) :=
    cosimp_comp_forget_hom_ext ((forget _).congr_map h)
  ext n x
  exact congr_fun (NatTrans.congr_app this n) x

end

variable {I₁ I₂ I₃ : Type u}
  [PartialOrder I₁] [TopologicalSpace I₁] [OrderBot I₁] [OrderTop I₁]
  [PartialOrder I₂] [TopologicalSpace I₂] [OrderBot I₂] [OrderTop I₂]
  [PartialOrder I₃] [TopologicalSpace I₃] [OrderBot I₃] [OrderTop I₃]

namespace cosimpAction_surjective

section

variable (φ : cosimp I₁ ⟶ cosimp I₂)

def f : I₁ → I₂ :=
  Function.comp cosimp.obj₁OrderIso.symm (((forget _).map (φ.app ⦋1⦌)).comp
    cosimp.obj₁OrderIso)

lemma monotone_f : Monotone (f φ) := by
  intro x₁ x₂ h
  let y := cosimp.obj₂Equiv ⟨⟨x₁, x₂⟩, h⟩
  convert (cosimp.obj₂Equiv.symm ((φ.app _ y))).2
  · have := (congr_fun ((forget _).congr_map (φ.naturality (cosimp.φ (1 : Fin 3).castSucc))) y)
    simp [cosimp.hφ, -Fin.castSucc_one, -Fin.reduceCastSucc] at this
    apply cosimp.obj₁OrderIso.injective
    dsimp at this
    simp [f, ← this]
    rfl
  · have := (congr_fun ((forget _).congr_map (φ.naturality (cosimp.φ (2 : Fin 3).castSucc))) y)
    simp [cosimp.hφ, -Fin.castSucc_one, -Fin.reduceCastSucc] at this
    apply cosimp.obj₁OrderIso.injective
    dsimp at this
    simp [f, ← this]
    rfl

end

variable (I₁) in
@[simp]
lemma f_id (x : I₁) :
    f (𝟙 (cosimp I₁)) x = x := rfl

@[simp]
lemma f_f (φ : cosimp I₁ ⟶ cosimp I₂) (ψ : cosimp I₂ ⟶ cosimp I₃) (x : I₁) :
    f ψ (f φ x) = f (φ ≫ ψ) x := by
  simp [f]

variable (φ : cosimp I₁ ≅ cosimp I₂)

@[simps]
def orderIso : I₁ ≃o I₂ where
  toFun := f φ.hom
  invFun := f φ.inv
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := ⟨fun h ↦ by simpa using monotone_f φ.inv h, fun h ↦ monotone_f φ.hom h⟩

end cosimpAction_surjective

open cosimpAction_surjective in
lemma cosimpAction_surjective [OrderTopology I₁] [OrderTopology I₂]
    (φ : cosimp I₁ ≅ cosimp I₂) :
    ∃ (f : I₁ →o I₂) (hf : Continuous f) (hf₀ : f ⊥ = ⊥) (hf₁ : f ⊤ = ⊤),
    cosimpAction f hf hf₀ hf₁ = φ.hom := by
  refine ⟨(orderIso φ).toOrderEmbedding.toOrderHom, (orderIso φ).continuous, by simp, by simp, ?_⟩
  · apply ((whiskeringRight SimplexCategory _ _).obj (forget TopCat)).map_injective
    apply cosimp_comp_forget_hom_ext
    ext x : 1
    apply cosimp.obj₁OrderIso.symm.injective
    change cosimp.obj₁OrderIso.symm (φ.hom.app _
      (cosimp.obj₁OrderIso (cosimp.obj₁OrderIso.symm x))) =
        cosimp.obj₁OrderIso.symm (φ.hom.app _ x)
    rw [OrderIso.apply_symm_apply]

end TopCat
