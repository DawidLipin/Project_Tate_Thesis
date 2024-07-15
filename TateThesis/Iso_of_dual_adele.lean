import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

def adeleRing_hat :=
  {ψ : (AddChar (adeleRing K) circle) // Continuous ψ}

-- Use AddChar.mulShift instead
def ψ_a (a : adeleRing K)
    (ψ : adeleRing_hat K) : (AddChar (adeleRing K) circle) where
      toFun := fun x => ψ.val (a * x)
      map_zero_one' := by
        simp only [mul_zero]
        exact ψ.val.map_zero_one'
      map_add_mul' := by
        intro b c
        simp only [mul_add]
        exact ψ.val.map_add_mul' (a * b) (a * c)

theorem mul_cont (a : adeleRing K): Continuous fun (x : (adeleRing K)) => (a * x) := by
  exact continuous_mul_left a

theorem psiaContinuous (a : adeleRing K)
    (ψ : adeleRing_hat K) : Continuous (ψ_a K a ψ) := by
  unfold ψ_a
  have h1 : Continuous (fun x => a * x) := mul_cont K a
  have h2 : Continuous ψ.val := ψ.property
  exact h2.comp h1

def IsoFunAdele (ψ : adeleRing_hat K) : (adeleRing K) → (adeleRing_hat K) :=
  fun a => ⟨(ψ_a K a ψ), (psiaContinuous K a ψ)⟩


instance : TopologicalSpace (adeleRing_hat K) := by
  sorry

def adeleHatIso (ψ : adeleRing_hat K) : adeleRing K ≃+* adeleRing_hat K where
  hom := IsoFunAdele K ψ
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

#lint
