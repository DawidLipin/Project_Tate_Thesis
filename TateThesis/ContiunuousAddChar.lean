import Mathlib.Algebra.Group.AddChar
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.Algebra.ContinuousMonoidHom

open Pointwise Function AddChar

variable (A B C D E F G H : Type*)
  [AddMonoid A] [AddMonoid B] [Monoid C] [Monoid D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  -- [AddMonoid E] [Monoid E] [TopologicalSpace E]
  [CommGroup F] [TopologicalSpace F] [TopologicalGroup F]
  [AddCommGroup G] [TopologicalSpace G]
  [CommMonoid H] [TopologicalSpace H]


structure ContinuousAddChar (A B : Type*) [AddMonoid A] [Monoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends (AddChar A B) where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun


-- -- /-- Reinterpret a `ContinuousAddChar` as a `AddChar`. -/
-- add_decl_doc ContinuousAddChar.toAddChar

-- -- /-- Reinterpret a `ContinuousAddChar` as an `AddChar`. -/
-- add_decl_doc ContinuousAddChar.toAddChar

namespace ContinuousAddChar

variable {A B C D E}

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


def toContinuousMap (f : ContinuousAddChar A C) : C(A, C) :=
  { f with }

theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, C)) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h

def mk' (f : AddChar A C) (hf : Continuous f) : ContinuousAddChar A C :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}


-- Need .prod in AddChar and .prodmap


/-- Product of two continuous homomorphisms on the same space. -/
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


/-- Product of two continuous homomorphisms on different spaces. -/
def prod_map (f : ContinuousAddChar A C) (g : ContinuousAddChar B D) :
    ContinuousAddChar (A × B) (C × D) :=
  mk' ({
    toFun := fun x => (f x.1, g x.2)
    map_zero_one' := by
      simp only [Prod.fst_zero, Prod.snd_zero]
      cases' f with f hf
      cases' g with g hg
      have h1 : f 0 = 1 := by exact map_zero_one f
      have h2 : g 0 = 1 := by exact map_zero_one g
      simp only [Prod.mk_eq_one]
      exact ⟨h1, h2⟩
    map_add_mul' :=
      sorry
  }) (f.continuous_toFun.prod_map g.continuous_toFun)

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
def one : ContinuousAddChar A C :=
  mk' 1 continuous_const

instance : Inhabited (ContinuousAddChar A C) :=
  ⟨one A C⟩

-- Everything below is not true since we need f 0 = 1

-- /-- The identity continuous homomorphism. -/
-- def id [Monoid A] : ContinuousAddChar A A :=
--   mk' (AddChar.id A) continuous_id

-- /-- The continuous homomorphism given by projection onto the first factor. -/
-- def fst : ContinuousAddChar (A × B) A :=
--   mk' (AddChar.fst A B) continuous_fst

-- /-- The continuous homomorphism given by projection onto the second factor. -/
-- def snd : ContinuousAddChar (A × B) B :=
--   mk' (AddChar.snd A B) continuous_snd

-- /-- The continuous homomorphism given by inclusion of the first factor. -/
-- def inl : ContinuousAddChar A (A × B) :=
--   prod (id A) (one A B)

-- /-- The continuous homomorphism given by inclusion of the second factor. -/
-- def inr : ContinuousAddChar B (A × B) :=
--   prod (one B A) (id B)

-- /-- The continuous homomorphism given by the diagonal embedding. -/
-- def diag : ContinuousAddChar A (A × A) :=
--   prod (id A) (id A)

-- /-- The continuous homomorphism given by swapping components. -/
-- def swap : ContinuousAddChar (A × B) (B × A) :=
--   prod (snd A B) (fst A B)

-- /-- The continuous homomorphism given by multiplication. -/
-- def mul : ContinuousAddChar (F × F) F :=
--   mk' mulAddChar continuous_mul

-- /-- The continuous homomorphism given by inversion. -/
-- def inv : ContinuousAddChar E E :=
--   mk' invAddChar continuous_inv

-- variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
def coprod (f : ContinuousAddChar A F) (g : ContinuousAddChar B F) :
    ContinuousAddChar (A × B) F where
      toFun := fun x => f x.1 * g x.2
      map_zero_one' := by
        simp only [Prod.fst_zero, Prod.snd_zero]
        cases' f with f hf
        cases' g with g hg
        have h1 : f 0 = 1 := AddChar.map_zero_one f
        have h2 : g 0 = 1 := AddChar.map_zero_one g
        have h3 : f 0 * g 0 = 1 := by simp only [map_zero_one, mul_one]
        exact h3
      map_add_mul' := by
        intro a b
        cases' f with f hf
        cases' g with g hg
        simp only [Prod.fst_add, Prod.snd_add]
        have h1 : f (a.1 + b.1) = f a.1 * f b.1 := AddChar.map_add_mul f a.1 b.1
        have h2 : g (a.2 + b.2) = g a.2 * g b.2 := AddChar.map_add_mul g a.2 b.2
        have h3 : f (a.1 + b.1) * g (a.2 + b.2) = f a.1 * f b.1 * (g a.2 * g b.2) := by simp only [h1, h2]
        -- have h4 : f a.1 * f b.1 * (g a.2 * g b.2) = f a.1 * (g a.2 * f b.1) * g b.2 := by sorry
        -- have h5 : f a.1 * (g a.2 * f b.1) * g b.2 = f a.1 * g a.2 * f b.1 * g b.2 := by sorry
        -- have h6 : f a.1 * f b.1 * (g a.2 * g b.2) = f a.1 * g a.2 * f b.1 * g b.2 := by sorry
        have h7 : f (a.1 + b.1) * g (a.2 + b.2) = f a.1 * g a.2 * f b.1 * g b.2 := sorry
        -- exact h7 doesn't work?
        sorry
      continuous_toFun := by
        cases' f with f hf
        cases' g with g hg
        simp only
        apply Continuous.mul
        · exact Continuous.comp hf (Continuous.fst continuous_id)
        · exact Continuous.comp hg (Continuous.snd continuous_id)

-- Already have AddCharinstCommGroup
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
  one := one A F
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)


instance : TopologicalSpace (ContinuousAddChar A C) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

theorem inducing_toContinuousMap : Inducing (toContinuousMap : ContinuousAddChar A C → C(A, C)) :=
  ⟨rfl⟩

theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousAddChar A C → C(A, C)) :=
  ⟨inducing_toContinuousMap A C, toContinuousMap_injective⟩

lemma range_toContinuousMap :
    Set.range (toContinuousMap : ContinuousAddChar A C → C(A, C)) =
      {f : C(A, C) | f 0 = 1 ∧ ∀ x y, f (x + y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f ↦ ⟨map_zero_one f.toAddChar, map_add_mul f.toAddChar⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_zero_one' := h1, map_add_mul' := hmul }, rfl⟩

theorem closedEmbedding_toContinuousMap [ContinuousMul C] [T2Space C] :
    ClosedEmbedding (toContinuousMap : ContinuousAddChar A C → C(A, C)) where
  toEmbedding := embedding_toContinuousMap A C
  isClosed_range := by
    simp only [range_toContinuousMap, Set.setOf_and, Set.setOf_forall]
    refine .inter (isClosed_singleton.preimage (ContinuousMap.continuous_eval_const 0)) <|
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (ContinuousMap.continuous_eval_const (x + y)) <|
      .mul (ContinuousMap.continuous_eval_const x) (ContinuousMap.continuous_eval_const y)


instance [T2Space C] : T2Space (ContinuousAddChar A C) :=
  (embedding_toContinuousMap A C).t2Space

----------------------------------------- Extra stuff

def toContinuousMonoidHomEquiv : ContinuousAddChar A C ≃ (ContinuousMonoidHom (Multiplicative A) C) where
  toFun φ := ⟨φ.toMonoidHom, φ.2⟩
  invFun f :=
  { toFun := f.toFun
    continuous_toFun := f.continuous_toFun
    map_zero_one' := f.map_one'
    map_add_mul' := f.map_mul' }
  left_inv _ := rfl
  right_inv _ := rfl

def toContinuousAddMonoidHomEquiv : ContinuousAddChar A C ≃ (ContinuousAddMonoidHom A (Additive C)) where
  toFun φ := ⟨φ.toAddMonoidHom, φ.2⟩
  invFun f :=
  { toFun := f.toFun
    continuous_toFun := f.continuous_toFun
    map_zero_one' := f.map_zero'
    map_add_mul' := f.map_add' }
  left_inv _ := rfl
  right_inv _ := rfl

def toContinuousAddMonoidHom (φ : ContinuousAddChar A C) : (ContinuousAddMonoidHom A (Additive C)) where
  toFun := ⟨φ.toFun, φ.2⟩
  continuous_toFun := f.continuous_toFun
  map_zero' := φ.map_zero_one'
  map_add' := φ.map_add_mul'

def compAddMonoidHom (φ : ContinuousAddChar B C) (f : A →+ B) : ContinuousAddChar A C :=
  (toContinuousAddMonoidHomEquiv A C).symm (φ.toContinuousAddMonoidHom.comp f)

instance instCommGroup : CommGroup (ContinuousAddChar G F) :=
  { instCommMonoid G F with
    inv := fun ψ ↦ ⟨ψ.compAddMonoidHom negAddMonoidHom, ψ.2⟩
    mul_left_inv := fun ψ ↦ by ext1 x; simp [negAddMonoidHom, ← map_add_mul]}

instance instCommGroup : CommGroup (ContinuousAddChar G F) := sorry

-----------------------------------------

instance : TopologicalGroup (ContinuousAddChar G F) :=
  let hi := inducing_toContinuousMap A F
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

-- @[to_additive]
-- theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
--     (f : A → ContinuousAddChar B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
--     Continuous f :=
--   (inducing_toContinuousMap _ _).continuous_iff.mpr
--     (ContinuousMap.continuous_of_continuous_uncurry _ h)
-- #align continuous_monoid_hom.continuous_of_continuous_uncurry ContinuousAddChar.continuous_of_continuous_uncurry
-- #align continuous_add_monoid_hom.continuous_of_continuous_uncurry ContinuousAddChar.continuous_of_continuous_uncurry

-- @[to_additive]
-- theorem continuous_comp [LocallyCompactSpace B] :
--     Continuous fun f : ContinuousAddChar A B × ContinuousAddChar B C => f.2.comp f.1 :=
--   (inducing_toContinuousMap A C).continuous_iff.2 <|
--     ContinuousMap.continuous_comp'.comp
--       ((inducing_toContinuousMap A B).prod_map (inducing_toContinuousMap B C)).continuous
-- #align continuous_monoid_hom.continuous_comp ContinuousAddChar.continuous_comp
-- #align continuous_add_monoid_hom.continuous_comp ContinuousAddChar.continuous_comp

-- @[to_additive]
-- theorem continuous_comp_left (f : ContinuousAddChar A B) :
--     Continuous fun g : ContinuousAddChar B C => g.comp f :=
--   (inducing_toContinuousMap A C).continuous_iff.2 <|
--     f.toContinuousMap.continuous_comp_left.comp (inducing_toContinuousMap B C).continuous
-- #align continuous_monoid_hom.continuous_comp_left ContinuousAddChar.continuous_comp_left
-- #align continuous_add_monoid_hom.continuous_comp_left ContinuousAddChar.continuous_comp_left

-- @[to_additive]
-- theorem continuous_comp_right (f : ContinuousAddChar B C) :
--     Continuous fun g : ContinuousAddChar A B => f.comp g :=
--   (inducing_toContinuousMap A C).continuous_iff.2 <|
--     f.toContinuousMap.continuous_comp.comp (inducing_toContinuousMap A B).continuous
-- #align continuous_monoid_hom.continuous_comp_right ContinuousAddChar.continuous_comp_right
-- #align continuous_add_monoid_hom.continuous_comp_right ContinuousAddChar.continuous_comp_right

-- variable (E)

-- /-- `ContinuousAddChar _ f` is a functor. -/
-- @[to_additive "`ContinuousAddChar _ f` is a functor."]
-- def compLeft (f : ContinuousAddChar A B) :
--     ContinuousAddChar (ContinuousAddChar B E) (ContinuousAddChar A E) where
--   toFun g := g.comp f
--   map_one' := rfl
--   map_mul' _g _h := rfl
--   continuous_toFun := f.continuous_comp_left
-- #align continuous_monoid_hom.comp_left ContinuousAddChar.compLeft
-- #align continuous_add_monoid_hom.comp_left ContinuousAddChar.compLeft

-- variable (A) {E}

-- /-- `ContinuousAddChar f _` is a functor. -/
-- @[to_additive "`ContinuousAddChar f _` is a functor."]
-- def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
--     (f : ContinuousAddChar B E) :
--     ContinuousAddChar (ContinuousAddChar A B) (ContinuousAddChar A E) where
--   toFun g := f.comp g
--   map_one' := ext fun _a => map_one f
--   map_mul' g h := ext fun a => map_mul f (g a) (h a)
--   continuous_toFun := f.continuous_comp_right
-- #align continuous_monoid_hom.comp_right ContinuousAddChar.compRight
-- #align continuous_add_monoid_hom.comp_right ContinuousAddChar.compRight

-- end ContinuousAddChar
