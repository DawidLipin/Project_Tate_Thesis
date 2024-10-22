import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNorm
import Mathlib.Data.Set.Basic

/-!

# Isomorphism of the adele ring and its Pontryagin dual as an additive gorup.

This file is still a work in progress.
The goal is to prove that the adele ring and its Pontryagin dual are isomorphic as additive groups.
This is a key step in the proof of the main theorem.

TODO:
- Adjust the construction below to work with a general field K with
  assumptions that hold for a general local field.
  The argument can then be adjusted to specific cases such as infinite and finite places.
- Then use the local proofs to prove the global isomorphism.

-/


noncomputable section

open NumberField DedekindDomain VectorFourier MeasureTheory.Measure IsDedekindDomain ContinuousAddChar IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]




-- Isomorphism on the infinite places

variable (v1 : InfinitePlace K)
variable (v2 : (HeightOneSpectrum (𝓞 K)))
variable (ψ : ContinuousAddChar (v2.adicCompletion K) circle)

lemma mul_cont (a : v2.adicCompletion K):
    Continuous (AddChar.mulShift ψ.toAddChar a) := by
  exact (ψ.2).comp (continuous_mul_left a)


-- This abbreviation and the following two lemmas need to be generalised as in ContMulShiftAdd.
-- However they are kept here for now until lemmas for ContMulShiftAdd have been proven.

/-- Homomorphism between a completion at an infinite place and its Pontryagin dual. -/
abbrev ContMulShift: (v2.adicCompletion K) → (ContinuousAddChar (v2.adicCompletion K) circle) :=
  fun a ↦ ⟨AddChar.mulShift ψ.toAddChar a, (mul_cont K v2 ψ a)⟩

/-- Proof that a shifted trivial character is trivial if a≠0 -/
lemma ContMulShiftTrivFunTriv (a : v2.adicCompletion K) (ha: a ≠ 0): (ContMulShift K v2 ψ a) = 1 ↔ ψ = 1 := by
  constructor <;> intro h1 <;> rw [← ContinuousAddChar.ext'] at * <;> intro x
  <;> simp only [ContinuousAddChar.one_apply] at *
  · specialize h1 (a⁻¹*x)
    unfold ContMulShift at h1
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply] at h1
    rw [← mul_assoc a (a⁻¹) x, mul_inv_cancel ha, one_mul] at h1
    exact h1
  · specialize h1 (a*x)
    unfold ContMulShift
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply]
    exact h1

/-- Proof that a set of all shifted trivial characters contains only the trivial character. -/
lemma ψ_set_triv (a : v2.adicCompletion K) (ha: a ≠ 0):
    {φ | ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} = {1} := by
  have h1: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) |
      ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} ⊇ {1} := by
    intro f hf x
    have h1_1: f=1 := hf
    rw [h1_1]
    rfl
  have h2: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) |
      ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} ⊆ {1} := by
    intro f hf
    by_contra hcontr
    simp at hcontr
    rw [← ne_eq] at hcontr
    have h3: ∀ (x : v2.adicCompletion K), (ContMulShift K v2 f a) x = 1 := by exact hf
    have h4: ContMulShift K v2 f a = 1 := by
      rw [← ContinuousAddChar.ext']
      exact h3
    have h5: f = 1 := by
      rw [ContMulShiftTrivFunTriv K v2 f a ha] at h4
      exact h4
    exact hcontr h5

  exact Set.Subset.antisymm h2 h1



/-- Stronger version of ContMulShift as it shows we have an additive
homomorphism rather than just a homomorphism. -/
abbrev ContMulShiftAdd: (v2.adicCompletion K) →+ Additive (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := fun a ↦ ⟨AddChar.mulShift ψ.toAddChar a, (mul_cont K v2 ψ a)⟩
  map_zero' := by
    rw [← ext']
    intro x
    simp only [mk_apply]
    rw [AddChar.mulShift_apply]
    rw [zero_mul]
    simp only [AddChar.map_zero_one]
    rfl
  map_add' := by
    intro a b
    rw [← ext']
    intro x
    simp only [mk_apply]
    rw [AddChar.mulShift_apply]
    rw [add_mul]
    simp only [AddChar.map_add_mul]
    rfl

/-- Proof that a shifted trivial character is trivial (additive version)-/
lemma ContMulShiftTrivFunTrivAdd (a : v2.adicCompletion K) (ha: a ≠ 0): (ContMulShiftAdd K v2 ψ a) = 0 ↔ ψ = 1 := by
  exact ContMulShiftTrivFunTriv K v2 ψ a ha

/-- Proof that our function ContMulShiftAdd is injective (additive version)-/
lemma MulShiftAddInjective (hψ : ψ ≠ 1): Function.Injective (ContMulShiftAdd K v2 ψ) := by
  rw [injective_iff_map_eq_zero]
  intro a h1
  by_contra h2
  rw [← ne_eq] at h2
  rw [ContMulShiftTrivFunTrivAdd K v2 ψ a h2] at h1
  exact hψ h1



-- TODO: This definition needs to be adjusted to be defined for closed subgroups rather than sets.
/-- Function between a subset of a completion at an infinite place and a subset of its pontryagin dual.
This will be used to show that X = {0} iff Φ(X) is the whole space of Pontryagin duals.
From this fact it will follow that the closure of the range of ContMulShiftAdd
is equal to the whole space of Pontryagin duals, hence the range is dense. -/
def Φ: (Set (v2.adicCompletion K)) → (Set (ContinuousAddChar (v2.adicCompletion K) circle)) :=
  fun X ↦ {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ x ∈ X, φ x = 1}

instance test (hψ : ψ ≠ 1) (X : (AddSubgroup (v2.adicCompletion K))):
    AddGroup {φ : Additive (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : X), φ x = 1} := by
      -- where
      sorry
      -- add := _
      -- add_assoc := _
      -- zero := _
      -- zero_add := _
      -- add_zero := _
      -- nsmul := _
      -- nsmul_zero := _
      -- nsmul_succ := _
      -- neg := _
      -- sub := _
      -- sub_eq_add_neg := _
      -- zsmul := _
      -- zsmul_zero' := _
      -- zsmul_succ' := _
      -- zsmul_neg' := _
      -- add_left_neg := _

-- def Φ2: (AddSubgroup (v2.adicCompletion K)) → (AddSubgroup (Additive (ContinuousAddChar (v2.adicCompletion K) circle))) :=
--   fun X ↦ {φ : Additive (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : X), φ x = 1}

/-- Proof that the range of ContMulShiftAdd is dense. -/
lemma DanseRangeContMulShiftAdd (hψ : ψ ≠ 1):
    DenseRange (ContMulShiftAdd K v2 ψ)  := by
  unfold DenseRange
  unfold Dense
  intro φ S h1
  cases' h1 with h1 h2
  sorry

/-- Proof that the range of ContMulShiftAdd is closed. -/
lemma IsClosedRangeContMulShiftAdd (hψ : ψ ≠ 1):
    IsClosed (Set.range (ContMulShiftAdd K v2 ψ))  := by
  -- Use isClosed_iff_nhds
  sorry

/-- Proof that the range of ContMulShiftAdd is the whole space of Pontryagin duals. -/
lemma DenseClosedEq (hψ : ψ ≠ 1) :
    Set.range (ContMulShiftAdd K v2 ψ) = Set.univ := by
  have h1 : DenseRange ((ContMulShiftAdd K v2 ψ)) := by
    exact DanseRangeContMulShiftAdd K v2 ψ hψ
  unfold DenseRange at h1
  rw [← Dense.closure_eq h1, eq_comm, closure_eq_iff_isClosed]
  exact IsClosedRangeContMulShiftAdd K v2 ψ hψ

/-- Proof that ContMulShiftAdd has a left and right inverse. -/
lemma ContMulShiftAddInv (hψ : ψ ≠ 1):
    ∃ (g : (ContinuousAddChar (v2.adicCompletion K) circle) → (v2.adicCompletion K)),
    Function.LeftInverse g (ContMulShiftAdd K v2 ψ) ∧ Function.RightInverse g (ContMulShiftAdd K v2 ψ) := by
  rw [← Function.bijective_iff_has_inverse]
  constructor
  · exact MulShiftAddInjective K v2 ψ hψ
  · rw [← Set.range_iff_surjective]
    exact DenseClosedEq K v2 ψ hψ

/-- Isomorphism between a completion at an infinite place and its Pontryagin dual as an additive group. -/
def LocalHatIso (hψ : ψ ≠ 1): (v2.adicCompletion K) ≃ (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := ContMulShiftAdd K v2 ψ
  invFun := (ContMulShiftAddInv K v2 ψ hψ).choose
  left_inv := (ContMulShiftAddInv K v2 ψ hψ).choose_spec.left
  right_inv := (ContMulShiftAddInv K v2 ψ hψ).choose_spec.right

/-- Isomorphism between a completion at an infinite place and its Pontryagin dual as an additive group. -/
def LocalHatIsoAdd (hψ : ψ ≠ 1): (v2.adicCompletion K) ≃+ Additive (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := ContMulShiftAdd K v2 ψ
  invFun := (ContMulShiftAddInv K v2 ψ hψ).choose
  left_inv := (ContMulShiftAddInv K v2 ψ hψ).choose_spec.left
  right_inv := (ContMulShiftAddInv K v2 ψ hψ).choose_spec.right
  map_add' := by simp only [_root_.map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, forall_const]
