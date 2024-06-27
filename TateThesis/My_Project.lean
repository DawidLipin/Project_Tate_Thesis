import Mathlib
-- import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
-- import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
-- import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

theorem locallyCompactSpace : LocallyCompactSpace (adeleRing K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace (ringOfIntegers K) K
  exact Prod.locallyCompactSpace _ _


----------------------------------------------------------------


-- Show elemeents of PontryaginDual A are same as AddChar?

-- def f_hat
theorem topcomp1 :  TopologicalSpace (adeleRing K) := by
  exact AdeleRing.topologicalSpace K

instance messpc :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

instance grpadl :  Group (adeleRing K) := by
  sorry

-- Is using (AddChar (adeleRing K) circle) instead of (PontryaginDual (adeleRing K)) an issue? I don't think so
-- TO ALIGN WITH BOOK USE IDENTITY ELEMENT FOR w below I think

def f_hat
    (K : Type*) [Field K] [NumberField K]
    (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsHaarMeasure]
    (f : (adeleRing K) → ℂ): (AddChar (adeleRing K) circle) → ((adeleRing K) → ℂ) :=
  fun e => (fun w => (Fourier.fourierIntegral e μ f w))


-- Ideles
#check (adeleRing K)ˣ


-- Condition 1
def Cond1 (f : (adeleRing K) → ℂ) (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsHaarMeasure] (x : (AddChar (adeleRing K) circle)):=
  (MeasureTheory.Memℒp f 1 μ) ∧ (Continuous f)∧ ((MeasureTheory.Memℒp ((f_hat K μ f) x) 1 μ) ∧ (Continuous f))

-- Need Fourier inversion formula for above
--
--
--



-- Condition 2



-- Condition 3



-- Set Z
