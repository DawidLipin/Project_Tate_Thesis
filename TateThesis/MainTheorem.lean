import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import TateThesis.ContinuousAddChar
-- import TateThesis.SetZ

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


instance adeleRingLocallyCompact : LocallyCompactSpace (adeleRing K) := by
  exact locallyCompactSpace K

instance messpc_hat :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

def ζ (f : (adeleRing K) → ℂ) (c : (ContinuousAddChar (adeleRing K) circle))
    (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsAddHaarMeasure] : ℂ :=
  (Fourier.fourierIntegral c.1 μ f 1)

-- theorem MainTheorem (f : SetZ.ZSet) : 1=1 := sorry
