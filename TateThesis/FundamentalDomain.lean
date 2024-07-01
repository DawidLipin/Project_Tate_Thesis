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

instance adeleRingLocallyCompact : LocallyCompactSpace (adeleRing K) := by
  exact locallyCompactSpace K

---------------------------------------------
