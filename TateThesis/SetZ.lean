import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNormonA

noncomputable section

open NumberField
open DedekindDomain
open VectorFourier
open MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

---------------------------------------------
-- Def f_hat

instance messpc :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

-- def f_hat
--     (K : Type*) [Field K] [NumberField K]
--     (μ : MeasureTheory.Measure (adeleRing K)) [μ.IsAddHaarMeasure]
--     (f : (adeleRing K) → ℂ) (w : (adeleRing K)): (AddChar (adeleRing K) circle) → ℂ :=
--   fun e => (Fourier.fourierIntegral e μ f w)

def f_hat
    (K : Type*) [Field K] [NumberField K]
    {AK : Type*} [TopologicalSpace AK] [MeasurableSpace AK]
    [CommRing AK] (μ : MeasureTheory.Measure AK) [μ.IsAddHaarMeasure]
    (f : AK → ℂ) (w : AK): (ContinuousAddChar AK circle) → ℂ :=
  fun e => (Fourier.fourierIntegral e.1 μ f w)

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

instance HAddAK : HAdd (adeleRing K) K (adeleRing K) := by
  --use def above
  sorry

def adeleHatIso: (ContinuousAddChar (adeleRing K) circle) ≃* (adeleRing K) := sorry

def adeleHatIsoInv: (adeleRing K) ≃* (ContinuousAddChar (adeleRing K) circle) := sorry

--------------------------------------------------
-- Set Z as a structure

structure ZSet (f : (adeleRing K) → ℂ)
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure]
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] where
  --- Condition 1
  fLp : MeasureTheory.Memℒp f 1 μ
  fCont : Continuous f
  fHatLp : MeasureTheory.Memℒp (f_hat K μ f 1) 1 μ_hat
  fHatCont : Continuous (f_hat K μ f 1)
  -- Condition 2
  sumAbs : ∀ (y : (adeleRing K)ˣ), Summable (fun (i : K) => (fun (x : (adeleRing K)) =>
    Complex.abs (f (y • (x + i)))))
  sumAbsHat : ∀ (y : (adeleRing K)ˣ), Summable fun (i : K) =>
    (fun (x : (ContinuousAddChar (adeleRing K) circle)) =>
    Complex.abs ((f_hat K μ f w) (adeleHatIsoInv K (y • ((adeleHatIso K x) + i)))))
  -- sumLoc :
  -- sumLocHat :

  -- Condition 3
  UnitgLp : let g := fun (x : (AddUnits (adeleRing K))) => ((f (x)) * (Complex.cpow (GlobalNormAdele K x) σ))
    MeasureTheory.Memℒp g 1 μ -- why does this work below but not here?
  UnitsgHatLp : let g_hat := fun (x : (ContinuousAddChar (adeleRing K) circle)ˣ) => ((f_hat K μ f 1) x) * (Complex.cpow (GlobalNormAdele K (adeleHatIso K x)) σ)
    MeasureTheory.Memℒp g_hat 1 μ_hat




------------------- Old Versions --------------------------------------------


---------------------------------------------
-- Cond 1

def Cond1 (f : (adeleRing K) → ℂ)
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
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

-- You can replace those 2 instances by getting ring hom between adeleRing K and Pntryagin dual and (AddChar...)
instance test : HAdd (ContinuousAddChar (adeleRing K) circle) K (ContinuousAddChar (adeleRing K) circle) := by
  -- use smul_adele
  sorry

instance test2 : HSMul (adeleRing K)ˣ (ContinuousAddChar (adeleRing K) circle) (ContinuousAddChar (adeleRing K) circle) := by
  -- use smul_adele
  sorry

instance KtoC : HAdd (adeleRing K) K (adeleRing K) := by
  sorry

def f_test : K → (adeleRing K) := fun x => globalEmbedding K x

def Cond2_a (f : (adeleRing K) → ℂ) (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] (y : (adeleRing K)ˣ) :=
  -- let g := fun x => f (y • (x))
  -- let g := fun x => ∑' (i : K), f (y • (x + i))
  -- Summable (∑' (i : K), (fun x => |f (y • (x + i))|))
  let f_sum : K → (adeleRing K) → ℂ := fun (i : K) => (fun x => Complex.abs (f (y • (x + i))))
  let f_hat_sum : K → (ContinuousAddChar (adeleRing K) circle) → ℂ :=
      fun (i : K) => (fun (x : (ContinuousAddChar (adeleRing K) circle)) =>
      Complex.abs ((f_hat K μ f w) (y • (x + i))))
  -- Summable (∑' (i : K), (fun x => |f (y • (x + i))|))
  -- ∧ Summable (∑' (i : K), |(fun x => ((f_hat K μ f w) (y • (x + i))))|) -- This is wrong
  Summable f_sum  ∧ Summable f_hat_sum

instance test1 : HAdd C K (adeleRing K) := by
  sorry

instance test3 :  HSMul C (adeleRing K) (adeleRing K) := by
  sorry

def Cond2_b (f : (adeleRing K) → ℂ) (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure] (w : (adeleRing K))
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure]
    -- Compact set
    (C : Set ((adeleRing K)ˣ)) (h1: IsCompact C)
    (h2: HSMul C K (adeleRing K))
    (h3: HSMul C (ContinuousAddChar (adeleRing K) circle) (ContinuousAddChar (adeleRing K) circle))
    -- Fundamental domain
    (D : Set (adeleRing K)) (h4: MeasureTheory.IsFundamentalDomain K D μ)
    :=
  let f_sum : K → (D × C) → ℂ := fun (i : K) => (fun (z : (D × C)) => f (z.2 • (z.1 + i)))
  -- Here I need to be able to somehow use the isomorphism of A and AddChar...
  let f_hat_sum : K → (D × C) → ℂ := fun (i : K) => (fun (z : (D × C)) => (f_hat K μ f w) (z.2 • (z.1 + i)))
  -- TendstoUniformly (fun (t : Finset K) (z : ((AddChar (adeleRing K) circle)), (y : C))) => ∑ n ∈ t, f n x) (fun (x : β) => ∑' (n : α), f n x) Filter.atTop
  1=1

--







---------------------------------------------
-- Cond 3

-- instance messpc_hat2 :  MeasurableSpace (ContinuousAddChar (AddUnits (adeleRing K)) circle) :=
--   by exact borel (ContinuousAddChar (AddUnits (adeleRing K)) circle)

-- def adeleHatIso: (ContinuousAddChar (adeleRing K) circle) ≃* (adeleRing K) := sorry

def Cond3 (f : (adeleRing K) → ℂ) (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure]
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] (σ : ℝ) (hσ: σ > 1) :=
  let g := fun (x : (AddUnits (adeleRing K))) => ((f (x)) * (Complex.cpow (GlobalNormAdele K x) σ))
  let g_hat := fun (x : (ContinuousAddChar (adeleRing K) circle)ˣ) => ((f_hat K μ f 1) x) * (Complex.cpow (GlobalNormAdele K (adeleHatIso K x)) σ)
  (MeasureTheory.Memℒp g 1 μ) ∧ (MeasureTheory.Memℒp g_hat 1 μ_hat)
  -- Why is this an issue for μ_hat but not μ?
  -- This is slightly cheated. Is that going to be an issue?
