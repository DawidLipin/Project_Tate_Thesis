import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNormonA
import Mathlib.Data.Set.Basic


noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure
open IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

-- def adeleRing_hat :=
--   {ψ : (AddChar (adeleRing K) circle) // Continuous ψ}

-- -- Use AddChar.mulShift instead
-- def ψ_a (a : adeleRing K)
--     (ψ : adeleRing_hat K) : (AddChar (adeleRing K) circle) where
--       toFun := fun x => ψ.val (a * x)
--       map_zero_one' := by
--         simp only [mul_zero]
--         exact ψ.val.map_zero_one'
--       map_add_mul' := by
--         intro b c
--         simp only [mul_add]
--         exact ψ.val.map_add_mul' (a * b) (a * c)

-- theorem mul_cont (a : adeleRing K): Continuous fun (x : (adeleRing K)) => (a * x) := by
--   exact continuous_mul_left a

-- theorem psiaContinuous (a : adeleRing K)
--     (ψ : adeleRing_hat K) : Continuous (ψ_a K a ψ) := by
--   unfold ψ_a
--   have h1 : Continuous (fun x => a * x) := mul_cont K a
--   have h2 : Continuous ψ.val := ψ.property
--   exact h2.comp h1

-- def IsoFunAdele (ψ : adeleRing_hat K) : (adeleRing K) → (adeleRing_hat K) :=
--   fun a => ⟨(ψ_a K a ψ), (psiaContinuous K a ψ)⟩


-- instance : TopologicalSpace (adeleRing_hat K) := by
--   sorry

-- def adeleHatIso (ψ : adeleRing_hat K) : adeleRing K ≃* (ContinuousAddChar (adeleRing K) circle) where
--   hom := sorry
--   inv := sorry
--   hom_inv_id := sorry
--   inv_hom_id := sorry


-- Local fields case ------------



variable (v1 : InfinitePlace K)
variable (v2 : (HeightOneSpectrum (𝓞 K)))
#check (v1.completion)
#check (v2.adicCompletion K)
variable (ψ : ContinuousAddChar (v2.adicCompletion K) circle)


-- instance: TopologicalSpace v1.completion := by exact UniformSpace.toTopologicalSpace
-- instance: TopologicalSpace circle := by exact instTopologicalSpaceSubtype

lemma mul_cont (a : v2.adicCompletion K):
    Continuous (AddChar.mulShift ψ.toAddChar a) := by
  exact (ψ.2).comp (continuous_mul_left a)

def ψa: (v2.adicCompletion K) → (ContinuousAddChar (v2.adicCompletion K) circle) :=
  fun a => ⟨AddChar.mulShift ψ.toAddChar a, (mul_cont K v2 ψ a)⟩

lemma ψa_triv_eq_ψ_triv (a : v2.adicCompletion K) (ha: a ≠ 0): (ψa K v2 ψ a) = 1 ↔ ψ = 1 := by
  constructor <;> intro h1 <;> rw [← ContinuousAddChar.ext'] at * <;> intro x
  <;> simp only [ContinuousAddChar.one_apply] at *
  · specialize h1 (a⁻¹*x)
    unfold ψa at h1
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply] at h1
    -- simp at h1
    -- weird bug with simp?
    rw [← mul_assoc a (a⁻¹) x, mul_inv_cancel ha, one_mul] at h1
    exact h1
  · specialize h1 (a*x)
    unfold ψa
    rw [ContinuousAddChar.mk_apply, AddChar.mulShift_apply]
    exact h1

lemma ψ_set_triv (a : v2.adicCompletion K) (hψ : ψ ≠ 1):
    {φ | ∀ (x : v2.adicCompletion K), (ψa K v2 ψ a) x = 1} = {1} := by
  have h1: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : v2.adicCompletion K), (ψa K v2 φ a) x = 1} ⊇ {1} := by
    intro f hf x
    have h1_1: f=1 := hf
    rw [h1_1]
    rfl
  have h2: {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ (x : v2.adicCompletion K), (ψa K v2 φ a) x = 1} ⊆ {1} := by
    intro f hf
    by_contra hcontr
    -- rw [ψa_triv_eq_ψ_triv K v2 _ a] at hf
    sorry
  -- exact Set.Subset.antisymm h2 h1
  sorry


def Λ: (Set (v2.adicCompletion K)) → (Set (ContinuousAddChar (v2.adicCompletion K) circle)) :=
  fun X => {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ x ∈ X, φ x = 1}

lemma test (a : v2.adicCompletion K): ∀ X : Set (v2.adicCompletion K), X={0} ↔ (Λ K v2) X = ⊤ := by
  intro X
  constructor
  · intro h1
    rw [h1]
    unfold Λ

    sorry
  · intro h1
    unfold Λ at h1
    by_contra h2
    --
    have h3: ∃ x, x ∈ X ∧ x ≠ 0 := by
      sorry
    cases' h3 with x hx1
    cases' hx1 with hx1 hx2
    --

    sorry



def isocs: Set (v2.adicCompletion K)  → Set (ContinuousAddChar (v2.adicCompletion K) circle) :=
  fun X => {φ : (ContinuousAddChar (v2.adicCompletion K) circle) | ∀ x ∈ X, (φ x) = 1}


lemma img_dense (a : v2.adicCompletion K) (hψ : ψ ≠ 1):
    DenseRange (ψa K v2 ψ a)  := by
  unfold DenseRange
  unfold Dense
  intro φ S h1
  cases' h1 with h1 h2
  have h3 : Dense (⊤ : Set (v2.adicCompletion K)) := sorry

  sorry

lemma closed_subgroup (hψ : ψ ≠ 1):
    IsClosed (Set.range (ψa K v2 ψ))  := by
  sorry

lemma isclosed_eq_closure {X : Type} [TopologicalSpace X] {S : Set X} (h1: IsClosed S):
    closure S = S := by
  unfold closure
  refine Set.ext ?h
  intro x
  constructor
  · simp only [Set.mem_sInter, Set.mem_setOf_eq, and_imp]
    intro h2
    apply h2
    · exact h1
    · exact fun ⦃a⦄ a ↦ a
  · intro hx T hT
    cases' hT with hT1 hT2
    apply hT2 at hx
    exact hx

lemma Dense_Closed_Eq (hψ : ψ ≠ 1) (h1: DenseRange ((ψa K v2 ψ))) (h2: IsClosed (Set.range (ψa K v2 ψ))):
    (Set.range (ψa K v2 ψ) = (ContinuousAddChar (v2.adicCompletion K) circle)) := by
  unfold DenseRange at h1
  -- unfold Dense at h1
  have h3: closure (Set.range (ψa K v2 ψ)) = Set.univ := by
    rw [Dense.closure_eq]
    exact h1


  sorry

def adeleHatIso: v1.completion ≃* (ContinuousAddChar (v2.adicCompletion K) circle) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry



#lint
