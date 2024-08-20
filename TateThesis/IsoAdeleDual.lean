import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNorm
import Mathlib.Data.Set.Basic


noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure
open IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]






-- Local fields case ------------



variable (v1 : InfinitePlace K)
variable (v2 : (HeightOneSpectrum (𝓞 K)))
variable (ψ : ContinuousAddChar (v2.adicCompletion K) circle)


-- instance: TopologicalSpace v1.completion := by exact UniformSpace.toTopologicalSpace
-- instance: TopologicalSpace circle := by exact instTopologicalSpaceSubtype

lemma mul_cont (a : v2.adicCompletion K):
    Continuous (AddChar.mulShift ψ.toAddChar a) := by
  exact (ψ.2).comp (continuous_mul_left a)

abbrev ContMulShift: (v2.adicCompletion K) → (ContinuousAddChar (v2.adicCompletion K) circle) :=
  fun a => ⟨AddChar.mulShift ψ.toAddChar a, (mul_cont K v2 ψ a)⟩

lemma ContMulShiftTrivFunTriv (a : v2.adicCompletion K) (ha: a ≠ 0): (ContMulShift K v2 ψ a) = 1 ↔ ψ = 1 := by
  constructor <;> intro h1 <;> rw [← ContinuousAddChar.ext'] at * <;> intro x
  <;> simp only [ContinuousAddChar.one_apply] at *
  · specialize h1 (a⁻¹*x)
    unfold ContMulShift at h1
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply] at h1
    -- simp at h1
    -- weird bug with simp?
    rw [← mul_assoc a (a⁻¹) x, mul_inv_cancel ha, one_mul] at h1
    exact h1
  · specialize h1 (a*x)
    unfold ContMulShift
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply]
    exact h1

lemma ψ_set_triv (a : v2.adicCompletion K) (ha: a ≠ 0):
    {φ | ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} = {1} := by
  have h1: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} ⊇ {1} := by
    intro f hf x
    have h1_1: f=1 := hf
    rw [h1_1]
    rfl
  have h2: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : v2.adicCompletion K), (ContMulShift K v2 φ a) x = 1} ⊆ {1} := by
    intro f hf
    by_contra hcontr

    -- rw [ContMulShiftTrivFunTriv K v2 _ a] at hf
    sorry
  exact Set.Subset.antisymm h2 h1

-------- Do I really have to do all this multiplication vs addition stuff? -------------



open ContinuousAddChar

abbrev ContMulShiftAdd: (v2.adicCompletion K) →+ Additive (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := fun a => ⟨AddChar.mulShift ψ.toAddChar a, (mul_cont K v2 ψ a)⟩
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

-- I can change def of ContMulShift to something like below if needed for proof of injectivity

-- abbrev ContMulShifttest: (v2.adicCompletion K) → (ContinuousAddChar (v2.adicCompletion K) circle) :=
--   fun a => (Additive.toMul (ContMulShiftAdd K v2 ψ a))


lemma ContMulShiftTrivFunTrivAdd (a : v2.adicCompletion K) (ha: a ≠ 0): (ContMulShiftAdd K v2 ψ a) = 0 ↔ ψ = 1 := by
  constructor <;> intro h1 <;> rw [← ContinuousAddChar.ext'] at * <;> intro x
  <;> simp only [ContinuousAddChar.one_apply] at *
  · specialize h1 (a⁻¹*x)
    unfold ContMulShiftAdd at h1
    -- rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply] at h1
    -- -- simp at h1
    -- -- weird bug with simp?
    -- rw [← mul_assoc a (a⁻¹) x, mul_inv_cancel ha, one_mul] at h1
    -- exact h1
    sorry
  · specialize h1 (a*x)
    -- unfold ContMulShift
    -- rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply]
    -- exact h1
    sorry

lemma test123( hψ : ψ ≠ 1): Function.Injective (ContMulShiftAdd K v2 ψ) := by
  -- by_contra h1
  -- unfold Function.Injective at h1
  -- simp at h1
  -- cases' h1 with x h1
  -- cases' h1 with y h1
  -- cases' h1 with h1 h2
  -- have h3: (∀ z, (AddChar.mulShift ψ.toAddChar x) z = (AddChar.mulShift ψ.toAddChar y) z) := by
  --   intro z
  --   rw [h1]
  -- specialize h3 y⁻¹
  -- rw [AddChar.mulShift_apply, AddChar.mulShift_apply] at h3

  -- intro x y h1
  -- unfold ContMulShift at h1
  -- rw [← ContinuousAddChar.ext'] at h1

  -- rw [Setoid.injective_iff_ker_bot]
  -- rw [Setoid.ker]

  rw [injective_iff_map_eq_zero]
  intro a h1
  by_contra h2
  rw [← ne_eq] at h2
  -- Why this won't work?
  rw [ContMulShiftTrivFunTrivAdd K v2 ψ a h2] at h1
  exact hψ h1




-------

lemma InjContMulShift (hψ : ψ ≠ 1): Function.Injective (ContMulShift K v2 ψ) := by
  -- This should be easy once I get the thing above to work
  sorry



--
--
--
-- Closed subgroups not sets!!!!!!!!!!!
--
--
--

def Λ: (Set (v2.adicCompletion K)) → (Set (ContinuousAddChar (v2.adicCompletion K) circle)) :=
  fun X => {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ x ∈ X, φ x = 1}

lemma test (a : v2.adicCompletion K): ∀ X : Set (v2.adicCompletion K), X={0} ↔ (Λ K v2) X = ⊤ := by
  intro X
  constructor
  · intro h1
    rw [h1]
    unfold Λ
    simp only [Set.mem_singleton_iff, forall_eq, Set.top_eq_univ]

    sorry
  · intro h1
    unfold Λ at h1
    by_contra h2
    --
    have h3: ∃ x, x ∈ X ∧ x ≠ 0 := by
      -- X not empty and not {0}
      sorry
    cases' h3 with x hx1
    cases' hx1 with hx1 hx2
    simp only [Set.top_eq_univ] at h1

    sorry



def isocs: Set (v2.adicCompletion K)  → Set (ContinuousAddChar (v2.adicCompletion K) circle) :=
  fun X => {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ x ∈ X, (φ x) = 1}


lemma DanseRangeContMulShift (hψ : ψ ≠ 1):
    DenseRange (ContMulShift K v2 ψ)  := by
  unfold DenseRange
  unfold Dense
  intro φ S h1
  cases' h1 with h1 h2
  -- have h3 : (Λ K v2)⁻¹ S = {1} := sorry

  sorry

lemma IsClosedRangeContMulShift (hψ : ψ ≠ 1):
    IsClosed (Set.range (ContMulShift K v2 ψ))  := by
  -- Maybe use isClosed_iff_frequently?
  -- Look in Mathlib.Topology.Basic
  -- Possible use isClosed_setOf_clusterPt?
  -- !!!! isClosed_iff_nhds is exactly what I need I think !!!!
  sorry

lemma DenseClosedEq (hψ : ψ ≠ 1) :
    Set.range (ContMulShift K v2 ψ) = Set.univ := by
  have h1 : DenseRange ((ContMulShift K v2 ψ)) := by
    exact DanseRangeContMulShift K v2 ψ hψ
  unfold DenseRange at h1
  rw [← Dense.closure_eq h1, eq_comm, closure_eq_iff_isClosed]
  exact IsClosedRangeContMulShift K v2 ψ hψ

lemma ContMulShiftInv (hψ : ψ ≠ 1):
    ∃ (g : (ContinuousAddChar (v2.adicCompletion K) circle) → (v2.adicCompletion K)), Function.LeftInverse g (ContMulShift K v2 ψ) ∧ Function.RightInverse g (ContMulShift K v2 ψ) := by
  rw [← Function.bijective_iff_has_inverse]
  constructor
  · exact InjContMulShift K v2 ψ hψ
  · rw [← Set.range_iff_surjective]
    exact DenseClosedEq K v2 ψ hψ

def adeleHatIso (hψ : ψ ≠ 1): (v2.adicCompletion K) ≃ (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := ContMulShift K v2 ψ
  invFun := (ContMulShiftInv K v2 ψ hψ).choose
  left_inv := (ContMulShiftInv K v2 ψ hψ).choose_spec.left
  right_inv := (ContMulShiftInv K v2 ψ hψ).choose_spec.right


-- #lint
