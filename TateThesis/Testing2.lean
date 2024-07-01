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

-----------------------
-- Fourier inversion formula

def f_hat
    (G : Type) [Group G] [AddGroup G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    [CommRing G] -- Why is this needed here but not in the notes?
    (f : G → ℂ) (w : G): (AddChar G circle) → ℂ :=
  fun e => (Fourier.fourierIntegral e μ f w)

def OfPositiveType (G : Type) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] (φ : G → ℂ)
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] :=
  ∀ (f : G → ℂ), HasCompactSupport f →
  -- ∫ t, (∫ s, ((φ (s⁻¹ * t)) * (f s)) ∂μ) * ((starRingEnd ℂ) (f t)) ∂μ ≥ 0
  (∫ t, (∫ s, ((φ (s⁻¹ * t)) * (f s)) ∂μ) * ((starRingEnd ℂ) (f t)) ∂μ  =
  Complex.abs (∫ t, (∫ s, ((φ (s⁻¹ * t)) * (f s)) ∂μ) * ((starRingEnd ℂ) (f t)) ∂μ))

def VG (G : Type) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] :=
  Submodule.span ℂ { φ | OfPositiveType G φ μ }

def V1G (G : Type) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] :=
  {(f : G → ℂ) | (f ∈ Submodule.span ℂ { φ | OfPositiveType G φ μ }) ∧ MeasureTheory.Memℒp f 1 μ}

instance topspc_hat (G : Type) [Group G] [AddGroup G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [CommRing G] :  TopologicalSpace (AddChar G circle) where
  IsOpen :=
    sorry
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry


instance messpc_hat (G : Type) [Group G] [AddGroup G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [CommRing G] :  MeasurableSpace (AddChar G circle) :=
  by exact borel (AddChar G circle)

theorem FourierInversionFormula (G : Type) [Group G] [AddGroup G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [CommRing G] -- Why is this needed here but not in the notes?
    [MeasurableSpace (AddChar G ↥circle)] -- Prove so you don't have to assume?
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (w : G):
    ∃ (μ_hat : MeasureTheory.Measure (AddChar G circle)), μ.IsHaarMeasure ∧
    ∀ (f : G → ℂ), ∀ y : G, f ∈ V1G → f y = ∫ x, (f_hat G μ f w) x ∂μ_hat := by -- What's the issue here?

  sorry
