import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Separation
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNorm


noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

def adeleHatIso: (ContinuousAddChar (adeleRing K) circle) ≃* (adeleRing K) := sorry

def adeleHatIsoInv: (adeleRing K) ≃* (ContinuousAddChar (adeleRing K) circle) := (adeleHatIso K).symm

---------------------------------------------
-- Def f_hat

instance messpc :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

-- def f_hat
--     (K : Type*) [Field K] [NumberField K]
--     (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsAddHaarMeasure]
--     (f : (adeleRing K) → ℂ) (w : (adeleRing K)): (AddChar (adeleRing K) circle) → ℂ :=
--   fun e => (Fourier.fourierIntegral e μ f w)

abbrev FunHat
    (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsAddHaarMeasure]
    (f : (adeleRing K) → ℂ): (adeleRing K) → ℂ :=
  fun e => (Fourier.fourierIntegral  (adeleHatIsoInv K e).1 μ f 1)

-- abbrev FunHat
--     (K : Type*) [Field K] [NumberField K]
--     {AK : Type*} [TopologicalSpace AK] [MeasurableSpace AK]
--     [CommRing AK] (μ : MeasureTheory.Measure AK) [μ.IsAddHaarMeasure]
--     (f : AK → ℂ) (w : AK): (adeleRing K) → ℂ :=
--   fun e => (Fourier.fourierIntegral  (adeleHatIsoInv K e).1 μ f w)

  -- def f_hat2
  --   (K : Type*) [Field K] [NumberField K]
  --   (μ : MeasureTheory.Measure (AddUnits (adeleRing K))) [μ.IsAddHaarMeasure]
  --   (f : (AddUnits (adeleRing K)) → ℂ) (w : (AddUnits (adeleRing K))): (AddChar (AddUnits (adeleRing K)) circle) → ℂ :=
  -- fun e => (Fourier.fourierIntegral e μ f w)


instance messpc_hat :  MeasurableSpace (ContinuousAddChar (adeleRing K) circle) :=
  by exact borel (ContinuousAddChar (adeleRing K) circle)

-- instance messpc_hat2 :  MeasurableSpace (ContinuousAddChar (AddUnits (adeleRing K)) circle) :=
--   by exact borel (ContinuousAddChar (AddUnits (adeleRing K)) circle)

def globalEmbedding : K →+* adeleRing K :=
  RingHom.prod (InfiniteAdeleRing.globalEmbedding K) (FiniteAdeleRing.globalEmbedding _ _)

instance CoeKAK : Coe K (adeleRing K) where
  coe := fun x => globalEmbedding K x

instance CoeAxAK : Coe (adeleRing K)ˣ (adeleRing K) where
  coe := fun x => x.val

open scoped BigOperators

abbrev SummableUnif {α β ι : Type*} [UniformSpace β] [TopologicalSpace α] [AddCommMonoid (α → β)] (F : ι → α → β) : Prop :=
  ∃ f, TendstoLocallyUniformly (fun (s : Finset ι) ↦ ∑ b in s, F b) f Filter.atTop -- Is this the right filter to use?

--------------------------------------------------
-- Set Z as a structure

structure ZSet
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure]
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] (f : ((adeleRing K) → ℂ)) : Prop where
  --- Condition 1
  fLp : MeasureTheory.Memℒp f 1 μ
  fCont : Continuous f
  fHatLp : MeasureTheory.Memℒp (FunHat K μ f) 1 μ
  fHatCont : Continuous (FunHat K μ f)
  -- Condition 2
  sumAbs : ∀ (y : (adeleRing K)ˣ), Summable (fun (i : K) =>
    (fun (x : (adeleRing K)) => f (y • (x + i))))
  sumAbsHat : ∀ (y : (adeleRing K)ˣ), Summable fun (i : K) =>
    (fun (x : (ContinuousAddChar (adeleRing K) circle)) =>
    (FunHat K μ f) (y • ((adeleHatIso K x) + i)))
  sumLocUnif : ∀ (D : Set (adeleRing K)), ∀ (C : Set (adeleRing K)ˣ), (IsCompact D ∧ IsCompact C) →
    ∀ (y : D), SummableUnif (fun (i : K) => (fun (x : C) => f (y * (x + i))))
  sumLocUnifHat : ∀ (D : Set (adeleRing K)), ∀ (C : Set (adeleRing K)ˣ), (IsCompact D ∧ IsCompact C) →
    ∀ (y : D), SummableUnif (fun (i : K) => (fun (x : C) => (FunHat K μ f) (y * (x + i))))
  -- Condition 3
  UnitgLp : ∀ (σ : ℝ), σ > 1 → MeasureTheory.Memℒp (fun (x : (AddUnits (adeleRing K))) =>
    ((f (x)) * (Complex.cpow (GlobalNormAdd K x) σ))) 1 (μ.comap (↑))
  UnitsgHatLp : ∀ (σ : ℝ), σ > 1 → MeasureTheory.Memℒp (fun (x : (AddUnits (adeleRing K))) =>
    ((FunHat K μ f) x) * (Complex.cpow (GlobalNormAdele K x) σ)) 1 (μ.comap (↑))
