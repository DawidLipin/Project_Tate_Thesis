import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing

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


instance topspc_hat (G : Type) [Group G] [AddGroup G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [CommRing G]:  TopologicalSpace (AddChar G circle) where
  IsOpen U := ∀ ψ ∈ U, ∃ K : Set G, ∃ V : (nhds (1 : circle)), IsCompact K → U ∈ {χ ∈ AddChar G circle | (χ K) ⊆ V}
    sorry
  isOpen_univ :=
    sorry
  isOpen_inter :=
    sorry
  isOpen_sUnion :=
    sorry
