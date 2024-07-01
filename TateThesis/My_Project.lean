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

theorem locallyCompactSpace : LocallyCompactSpace (adeleRing K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace (ringOfIntegers K) K
  exact Prod.locallyCompactSpace _ _


----------------------------------------------------------------


-- Show elemeents of PontryaginDual A are same as AddChar?

-- Def f_hat

theorem topcomp1 :  TopologicalSpace (adeleRing K) := by
  exact AdeleRing.topologicalSpace K

instance messpc :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

-- Is using (AddChar (adeleRing K) circle) instead of (PontryaginDual (adeleRing K)) an issue? I don't think so
-- TO ALIGN WITH BOOK USE IDENTITY ELEMENT FOR w below I think

def f_hat
    (K : Type*) [Field K] [NumberField K]
    {AK : Type*} [TopologicalSpace AK] [MeasurableSpace AK]
    [CommRing AK] (μ : MeasureTheory.Measure AK) [μ.IsAddHaarMeasure]
    (f : AK → ℂ) (w : AK): (AddChar AK circle) → ℂ :=
  fun e => (Fourier.fourierIntegral e μ f w)


-- Ideles
#check (adeleRing K)ˣ


-- Condition 1

instance topchar : TopologicalSpace (AddChar (adeleRing K) circle) := by
  sorry

instance messpc_hat :  MeasurableSpace (AddChar (adeleRing K) circle) :=
  by exact borel (AddChar (adeleRing K) circle)

def Cond1 (f : (adeleRing K) → ℂ)
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (AddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] :=
  (MeasureTheory.Memℒp f 1 μ) ∧ (Continuous f) ∧
  ((MeasureTheory.Memℒp (f_hat K μ f w) 1 μ_hat) ∧ (Continuous (f_hat K μ f w)))

-- Need Fourier inversion formula for above
--
--
--



-- Condition 2



-- Condition 3



-- Set Z
