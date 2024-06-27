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
-- Def f_hat

theorem topcomp1 :  TopologicalSpace (adeleRing K) := by
  exact AdeleRing.topologicalSpace K

instance messpc :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

instance grpadl :  Group (adeleRing K) := by
  sorry

-- Is using (AddChar (adeleRing K) circle) instead of (PontryaginDual (adeleRing K)) an issue? I don't think so
-- TO ALIGN WITHBOOK USE IDENTITY ELEMENT FOR w below I think

def f_hat_old
    (K : Type*) [Field K] [NumberField K]
    (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsHaarMeasure]
    (f : (adeleRing K) → ℂ): (AddChar (adeleRing K) circle) → ((adeleRing K) → ℂ) :=
  fun e => (fun w => (Fourier.fourierIntegral e μ f w))

-- Replace element with w

-- def f_hat
--     (K : Type*) [Field K] [NumberField K]
--     (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsHaarMeasure]
--     (f : (adeleRing K) → ℂ) (w : (adeleRing K)): (AddChar (adeleRing K) circle) → ℂ :=
--   fun e => (Fourier.fourierIntegral e μ f w)


def f_hat
    (K : Type*) [Field K] [NumberField K]
    {AK : Type*} [TopologicalSpace AK] [MeasurableSpace AK]
    [Group AK] [CommRing AK] (μ : MeasureTheory.Measure AK) [μ.IsHaarMeasure]
    (f : AK → ℂ) (w : AK): (AddChar AK circle) → ℂ :=
  fun e => (Fourier.fourierIntegral e μ f w)


---------------------------------------------
-- Cond 1

variable (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsHaarMeasure] (f : (adeleRing K) → ℂ)

instance topchar : TopologicalSpace (AddChar (adeleRing K) circle) := by
  sorry

instance messpc_hat :  MeasurableSpace (AddChar (adeleRing K) circle) :=
  by exact borel (AddChar (adeleRing K) circle)

def Cond1 (f : (adeleRing K) → ℂ)
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (AddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] :=
  (MeasureTheory.Memℒp f 1 μ) ∧ (Continuous f) ∧
  ((MeasureTheory.Memℒp (f_hat K μ f w) 1 μ_hat) ∧ (Continuous (f_hat K μ f w)))

-- Need Fourier inversion formula for above
--
--
--

---------------------------------------------
-- Cond 2

instance latf : Lattice (adeleRing K → ℂ) := by
  sorry

-- Construct the fundamental domain
--
--
--

variable (D : Set (adeleRing K))

instance smul_adele : SMul K (adeleRing K) := by
  exact { smul := fun _ a => a }

theorem fund_dom :  MeasureTheory.IsFundamentalDomain K D μ := by
  sorry

def globalEmbedding : K →+* adeleRing K :=
  RingHom.prod (InfiniteAdeleRing.globalEmbedding K) (FiniteAdeleRing.globalEmbedding _ _)

instance HSMULAxKA : HSMul (adeleRing K)ˣ K (adeleRing K) := by
  -- use smul_adele
  sorry

-- You can replace those 2 instances by getting ring hom between adeleRing K and Pntryagin dual and (AddChar...)
instance test : HAdd (AddChar (adeleRing K) ↥circle) K (AddChar (adeleRing K) ↥circle) := by
  -- use smul_adele
  sorry

instance test2 : HSMul (adeleRing K)ˣ (AddChar (adeleRing K) ↥circle) (AddChar (adeleRing K) ↥circle) := by
  -- use smul_adele
  sorry

instance KtoC : Lattice (K → ℂ) := by
  sorry

def f_test : K → (adeleRing K) := fun x => globalEmbedding K x

def Cond2 (f : (adeleRing K) → ℂ) (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (AddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] (y : (adeleRing K)ˣ) :=
  -- let g := fun x => f (y • (x))
  -- let g := fun x => ∑' (i : K), f (y • (x + i))
  -- Summable (∑' (i : K), (fun x => |f (y • (x + i))|))
  let f_sum := fun (i : K) => |(fun x => f (y • (x + i)))|
  let f_hat_sum := fun (i : K) => |(fun (x : (AddChar (adeleRing K) circle)) => (f_hat K μ f w) (y • (x + i)))|
  -- Summable (∑' (i : K), (fun x => |f (y • (x + i))|))
  -- ∧ Summable (∑' (i : K), |(fun x => ((f_hat K μ f w) (y • (x + i))))|) -- This is wrong
  Summable f_sum  ∧ Summable f_hat_sum

--







---------------------------------------------
-- Cond 2

-- !!!!!!!!
-- Remove |x| below and identify (adeleRing K)ˣ with (adeleRing K) to make this work
-- !!!!!!!!

-- instance fix_later1 : Lattice (adeleRing K)ˣ := by
--   sorry
-- instance fix_later2 : HPow ℂ ℝ ℂ := by
--   sorry
-- instance fix_later3 : AddGroup (adeleRing K)ˣ := by
--   sorry
-- instance fix_later4 : HPow (adeleRing K)ˣ ℝ ℝ := by
--   sorry
-- instance fix_later5 : Lattice (AddChar (adeleRing K) circle)ˣ := by
--   sorry
-- instance fix_later6 : AddGroup (AddChar (adeleRing K) circle)ˣ := by
--   sorry
-- instance fix_later7 : HPow (AddChar (adeleRing K) circle)ˣ ℝ ℝ := by
--   sorry
-- instance fix_later8 : CommRing (adeleRing K)ˣ := by
--   sorry

-- How is this an issue? Isn't this already defined in lean?
instance CmulR : HMul ℂ ℝ ℂ := by
  sorry



def Cond3 (f : (adeleRing K)ˣ → ℂ) (μ : MeasureTheory.Measure (adeleRing K)ˣ)
    [μ.IsHaarMeasure] (w : (adeleRing K)ˣ)
    (μ_hat : MeasureTheory.Measure (AddChar (adeleRing K)ˣ circle))
    [μ_hat.IsHaarMeasure] (y : (adeleRing K)ˣ) (σ : ℝ) :=
  -- Change |x| below once you define it properly as on page 65
  let g := fun x => ((f (x)) * (|x|^σ))
  let g_hat := fun x => ((f_hat K μ g w) (x)) * (|x|^σ)
  (MeasureTheory.Memℒp g 1 μ) ∧ (MeasureTheory.Memℒp g_hat 1 μ_hat)
