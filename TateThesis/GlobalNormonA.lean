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

instance test1 : TopologicalSpace K := by
  sorry

instance test2 : MeasurableSpace K := by
  exact borel K


def K_comp (G : Type) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] :=
  {f : (G → ℝ) // (Continuous f) ∧ (HasCompactSupport f)}

def K_comp_p (G : Type) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] :=
  {f : (K_comp G) // ∀ x : G, f.val x ≥ 0 ∧ ∃ y : G, f.val y > 0}

def μ_α (G : Type) [Group G] [AddGroup G]
    [LocallyCompactSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (α : Gˣ): AddHaarMeasure :=
  fun f => (fun x => (μ (f.val.val (α * x))))


-- def K_norm (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
--     (α : Kˣ):  :=
--   1=1
