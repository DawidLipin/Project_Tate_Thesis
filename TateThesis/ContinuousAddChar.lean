/-
Many of the thoerems and their proofs in this file are based on the following mathlib files:
Mathlib.Topology.Algebra.ContinuousMonoidHom,
Mathlib.Algebra.Group.AddChar
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!

# Continuous Additive Characters

This file defines the space of continuous additive characters between two topological groups.

-/

open Pointwise Function AddChar

variable (A B C D E F G H : Type*)
  [AddMonoid A] [AddMonoid B] [Monoid C] [Monoid D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [AddMonoid E] [CommGroup F] [TopologicalSpace E]
  [CommGroup F] [TopologicalSpace F] [TopologicalGroup F]
  [AddCommGroup G] [TopologicalSpace G] [TopologicalAddGroup G]
  [CommMonoid H] [TopologicalSpace H]


/-- Definition of ContinuousAddChar. -/
structure ContinuousAddChar (A B : Type*) [AddMonoid A] [Monoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends (AddChar A B) where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun


namespace ContinuousAddChar

variable {A B C D E}

/-- Define coercion to a function. -/
instance funLike : FunLike (ContinuousAddChar A C) A C where
  coe f := f.toFun
  coe_injective' f g h := by
    cases' f with f hf
    cases' g with g hg
    simp only [mk.injEq]
    simp at *
    exact AddChar.instFunLike.proof_1 f g h


theorem ext {f g : ContinuousAddChar A C} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem ext' {f g : ContinuousAddChar A C}: (∀ x, f x = g x) ↔ f = g := by
  constructor
  · exact ext
  · intro h1 x
    exact congrFun (congrArg DFunLike.coe h1) x

/-- Reinterpret a `ContinuousAddChar` as a `ContinuousMap`. -/
def toContinuousMap (f : ContinuousAddChar A C) : C(A, C) :=
  { f with }

theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, C)) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h

/-- Construct a `ContinuousAddChar` from a `Continuous` `AddChar`. -/
def mk' (f : AddChar A C) (hf : Continuous f) : ContinuousAddChar A C :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}

@[simp]
lemma mk_apply (f : AddChar A C) (hf : Continuous f) (a : A) : ContinuousAddChar.mk f hf a = f a := rfl

/-- Product of two continuous additive characters on the same space. -/
def prod (f : ContinuousAddChar A C) (g : ContinuousAddChar A D) :
    ContinuousAddChar A (C × D) where
  toFun := Pi.prod f g
  map_zero_one' := by
    simp only [Pi.prod, AddChar.map_zero_one, Prod.mk_eq_one]
    exact ⟨f.map_zero_one, g.map_zero_one⟩
  map_add_mul' := by
    simp only [Pi.prod, Prod.mk_mul_mk, Prod.mk.injEq]
    intro a B
    exact ⟨f.map_add_mul a B, g.map_add_mul a B⟩
  continuous_toFun := by
    cases' f with f hf
    cases' g with g hg
    exact Continuous.prod_mk hf hg


/-- Product of two continuous additive characters on different spaces. -/
def prod_map (f : ContinuousAddChar A C) (g : ContinuousAddChar B D) :
    ContinuousAddChar (A × B) (C × D) :=
  mk' ({
    toFun := fun x => (f x.1, g x.2)
    map_zero_one' := by
      simp only [Prod.fst_zero, Prod.snd_zero]
      cases' f with f hf
      cases' g with g hg
      simp only [mk_apply, map_zero_one, Prod.mk_eq_one, and_self]
    map_add_mul' := by
      intro a b
      cases' f with f hf
      cases' g with g hg
      simp only [mk_apply, Prod.mk_mul_mk, Prod.mk.injEq]
      constructor
      · exact map_add_mul f a.1 b.1
      · exact map_add_mul g a.2 b.2
  }) (f.continuous_toFun.prod_map g.continuous_toFun)

/-- The trivial continuous additive characters. -/
def one : ContinuousAddChar A C :=
  mk' 1 continuous_const

instance instOne : One (ContinuousAddChar A C) := ⟨1, continuous_const⟩

@[simp] lemma one_apply (a : A) : (1 : ContinuousAddChar A C) a = 1 := rfl

instance : Inhabited (ContinuousAddChar A C) :=
  ⟨one⟩

/-- Coproduct of two continuous additive characters to the same space. -/
def coprod (f : ContinuousAddChar A F) (g : ContinuousAddChar B F) :
    ContinuousAddChar (A × B) F where
      toFun := fun x => f x.1 * g x.2
      map_zero_one' := by
        simp only [Prod.fst_zero, Prod.snd_zero]
        cases' f with f hf
        cases' g with g hg
        simp only [mk_apply, map_zero_one, mul_one]
      map_add_mul' := by
        intro a b
        cases' f with f hf
        cases' g with g hg
        simp only [Prod.fst_add, mk_apply, Prod.snd_add, mul_mul_mul_comm]
        simp only [map_add_mul]
      continuous_toFun := by
        cases' f with f hf
        cases' g with g hg
        simp only
        apply Continuous.mul
        · exact Continuous.comp hf (Continuous.fst continuous_id)
        · exact Continuous.comp hg (Continuous.snd continuous_id)


instance instCommMonoid : CommMonoid (ContinuousAddChar A F) where
  mul f g := {
    toFun := f.toFun * g.toFun,
    map_zero_one' := by
      simp only [Pi.mul_apply]
      cases' f with f hf
      cases' g with g hg
      simp only
      have h1 : f.toFun 0 = 1 := by exact AddChar.map_zero_one f
      have h2 : g.toFun 0 = 1 := by exact AddChar.map_zero_one g
      rw [h1, h2]
      exact Units.instOneUnits.proof_1
    map_add_mul' := by
      intro a b
      cases' f with f hf
      cases' g with g hg
      simp only [Pi.mul_apply]
      have h1 : f.toFun (a + b) = f.toFun a * f.toFun b := by exact AddChar.map_add_mul f a b
      have h2 : g.toFun (a + b) = g.toFun a * g.toFun b := by exact AddChar.map_add_mul g a b
      rw [h1, h2]
      exact mul_mul_mul_comm (f.toFun a) (f.toFun b) (g.toFun a) (g.toFun b)
    continuous_toFun := by
      cases' f with f hf
      cases' g with g hg
      simp only [Pi.mul_apply]
      apply Continuous.mul
      · exact Continuous.comp hf continuous_id
      · exact Continuous.comp hg continuous_id
  }
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one := one
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)


instance : TopologicalSpace (ContinuousAddChar A C) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

theorem inducing_toContinuousMap : Inducing (toContinuousMap : ContinuousAddChar A C → C(A, C)) :=
  ⟨rfl⟩

theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousAddChar A C → C(A, C)) :=
  ⟨inducing_toContinuousMap, toContinuousMap_injective⟩

lemma range_toContinuousMap :
    Set.range (toContinuousMap : ContinuousAddChar A C → C(A, C)) =
      {f : C(A, C) | f 0 = 1 ∧ ∀ x y, f (x + y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f ↦ ⟨map_zero_one f.toAddChar, map_add_mul f.toAddChar⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_zero_one' := h1, map_add_mul' := hmul }, rfl⟩

theorem closedEmbedding_toContinuousMap [ContinuousMul C] [T2Space C] :
    ClosedEmbedding (toContinuousMap : ContinuousAddChar A C → C(A, C)) where
  toEmbedding := embedding_toContinuousMap
  isClosed_range := by
    simp only [range_toContinuousMap, Set.setOf_and, Set.setOf_forall]
    refine .inter (isClosed_singleton.preimage (ContinuousMap.continuous_eval_const 0)) <|
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (ContinuousMap.continuous_eval_const (x + y)) <|
      .mul (ContinuousMap.continuous_eval_const x) (ContinuousMap.continuous_eval_const y)


instance [T2Space C] : T2Space (ContinuousAddChar A C) :=
  (embedding_toContinuousMap).t2Space

/-- Equivalence between `ContinuousAddChar` and `ContinuousMonoidHom` with multiplicative domain. -/
def toContinuousMonoidHomEquiv : ContinuousAddChar A C ≃ (ContinuousMonoidHom (Multiplicative A) C) where
  toFun φ := ⟨φ.toMonoidHom, φ.2⟩
  invFun f :=
  { toFun := f.toFun
    continuous_toFun := f.continuous_toFun
    map_zero_one' := f.map_one'
    map_add_mul' := f.map_mul' }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence between `ContinuousAddChar` and `ContinuousMonoidHom` with additive codomain. -/
def toContinuousAddMonoidHomEquiv : ContinuousAddChar A C ≃ (ContinuousAddMonoidHom A (Additive C)) where
  toFun φ := ⟨φ.toAddMonoidHom, φ.2⟩
  invFun f :=
  { toFun := f.toFun
    continuous_toFun := f.continuous_toFun
    map_zero_one' := f.map_zero'
    map_add_mul' := f.map_add' }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Convert `ContinuousAddChar` to `ContinuousMonoidHom` with additive codomain. -/
def toContinuousAddMonoidHom (φ : ContinuousAddChar A C) : (ContinuousAddMonoidHom A (Additive C)) where
  toFun := toContinuousAddMonoidHomEquiv φ
  continuous_toFun := φ.continuous_toFun
  map_zero' := φ.map_zero_one'
  map_add' := φ.map_add_mul'

/-- The natural equivalence to `(Multiplicative A →* F)` is a monoid isomorphism
under stronger assumptions on codomain than `toContinuousMonoidHomEquiv`. -/
def toMonoidHomMulEquiv : AddChar A F ≃* (Multiplicative A →* F) :=
  { toMonoidHomEquiv A F with map_mul' := fun φ ψ ↦ by rfl }

/-- Additive characters `A → F` are the same thing as additive homomorphisms from `A` to
`Additive F` under stronger assumptions on codomain than `toContinuousAddMonoidHomEquiv`. -/
def toAddMonoidAddEquiv : Additive (AddChar A F) ≃+ (A →+ Additive F) :=
  { toAddMonoidHomEquiv A F with map_add' := fun φ ψ ↦ by rfl }

/-- Composition of `ContinuousAddChar` with `ContinuousAddMonoidHom` is an `ContinuousAddChar`. -/
def compAddMonoidHom (φ : ContinuousAddChar B C) (f : ContinuousAddMonoidHom A B) : ContinuousAddChar A C :=
  (toContinuousAddMonoidHomEquiv).symm ((toContinuousAddMonoidHom φ).comp f)

lemma map_add_mul (ψ : ContinuousAddChar A C) (x y : A) : ψ (x + y) = ψ x * ψ y := ψ.map_add_mul' x y

lemma mul_apply (ψ φ : ContinuousAddChar A F) (a : A) : (ψ * φ) a = ψ a * φ a := rfl

instance : CommGroup (ContinuousAddChar G F) :=
  { instCommMonoid F with
    inv := fun ψ ↦ (ψ.compAddMonoidHom (ContinuousAddMonoidHom.neg G))
    mul_left_inv := by
      intro ψ
      apply ext
      intro x
      simp only
      have h1 : (compAddMonoidHom ψ (ContinuousAddMonoidHom.neg G) x) * (ψ x) = (compAddMonoidHom ψ (ContinuousAddMonoidHom.neg G) * ψ) x := rfl
      have h2 : (ContinuousAddMonoidHom.neg G) x = -x := rfl
      have h3 : (compAddMonoidHom ψ (ContinuousAddMonoidHom.neg G) x) = ψ ((ContinuousAddMonoidHom.neg G) x) := rfl
      rw [← h1, h3, h2]
      simp only [← map_add_mul, add_left_neg]
      have h4 :  ψ 0 = 1 := ψ.map_zero_one'
      rw [h4]
      rfl
      }

@[simp]
lemma inv_apply (ψ : ContinuousAddChar G F) (x : G) : ψ⁻¹ x = ψ (-x) := rfl

@[simp]
lemma map_neg_inv (ψ : ContinuousAddChar G F) (a : G) : ψ (-a) = (ψ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_mul, add_left_neg, map_zero_one]
  exact ψ.map_zero_one'

lemma inv_apply' (ψ : ContinuousAddChar G F) (x : G) : ψ⁻¹ x = (ψ x)⁻¹ := by
  simp only [inv_apply, map_neg_inv]


instance : ContinuousInv (ContinuousAddChar G F) where
  continuous_inv := by
    have hi : Inducing (toContinuousMap : ContinuousAddChar G F → C(G, F)):= inducing_toContinuousMap
    rw [hi.continuous_iff]
    have foo := (continuous_inv.comp hi.continuous)
    convert foo
    ext φ g
    simp only [comp_apply, ContinuousMap.inv_apply]
    exact inv_apply' F G φ g

instance : TopologicalGroup (ContinuousAddChar G F) :=
  have hi := inducing_toContinuousMap
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
  }

theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A → ContinuousAddChar B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (inducing_toContinuousMap).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)


end ContinuousAddChar
