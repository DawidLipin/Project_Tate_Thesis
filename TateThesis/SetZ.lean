import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Separation
import TateThesis.ContinuousAddChar
import TateThesis.GlobalNorm

/-!

# Set Z

This file defines the set Z needed for the main theorem.

-/

noncomputable section

open NumberField DedekindDomain VectorFourier MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]


/-- We assume that we have an isomorphism between the adeleRing and its Pontryagin dual as an additive group. -/
def adeleHatIso: Additive (ContinuousAddChar (adeleRing K) circle) ≃+ (adeleRing K) := sorry

/-- Inverse of adeleHatIso -/
abbrev adeleHatIsoInv: (adeleRing K) ≃+ Additive (ContinuousAddChar (adeleRing K) circle) := (adeleHatIso K).symm



instance :  MeasurableSpace (adeleRing K) :=
  by exact borel (adeleRing K)

instance :  MeasurableSpace (ContinuousAddChar (adeleRing K) circle) :=
  by exact borel (ContinuousAddChar (adeleRing K) circle)


/-- Generalised Fourier transform of f on the adele ring. -/
abbrev FunHatAdele
    (μ : MeasureTheory.Measure (adeleRing K))
    (f : (adeleRing K) → ℂ): (adeleRing K) → ℂ :=
  fun e ↦ (Fourier.fourierIntegral (adeleHatIsoInv K e).1 μ f 1)


/-- Construct embedding of K into the corresponding adele ring to allows for coercion. -/
def globalEmbedding : K →+* adeleRing K :=
  RingHom.prod (InfiniteAdeleRing.globalEmbedding K) (FiniteAdeleRing.globalEmbedding _ _)

instance : Coe K (adeleRing K) where
  coe := fun x ↦ globalEmbedding K x

instance : Coe (adeleRing K)ˣ (adeleRing K) where
  coe := fun x ↦ x.val


open scoped BigOperators

/-- Deinfe local uniform convergence. -/
abbrev SummableUnif {α β ι : Type*} [UniformSpace β] [TopologicalSpace α] [AddCommMonoid β] (F : ι → α → β) : Prop :=
  ∃ f, TendstoLocallyUniformly (fun (s : Finset ι) ↦ ∑ b in s, F b) f Filter.atTop


/-- Set Z defined as a structure -/
structure ZSet
    (μ : MeasureTheory.Measure (adeleRing K))
    [μ.IsAddHaarMeasure]
    (f : ((adeleRing K) → ℂ)) : Prop where
  --- Condition 1
  fLp : MeasureTheory.Memℒp f 1 μ
  fCont : Continuous f
  fHatLp : MeasureTheory.Memℒp (FunHatAdele K μ f) 1 μ
  fHatCont : Continuous (FunHatAdele K μ f)
  -- Condition 2
  sumAbs : ∀ (y : (adeleRing K)ˣ), Summable (fun (i : K) ↦
    (fun (x : (adeleRing K)) ↦ f (y • (x + i))))
  sumAbsHat : ∀ (y : (adeleRing K)ˣ), Summable fun (i : K) ↦
    (fun (x : (ContinuousAddChar (adeleRing K) circle)) ↦
    (FunHatAdele K μ f) (y • ((adeleHatIso K x) + i)))
  sumLocUnif : ∀ (y : (adeleRing K)),
    SummableUnif (fun (i : K) ↦ (fun (x : (adeleRing K)ˣ) ↦ f (y * (x + i))))
  sumLocUnifHat : ∀ (y : (adeleRing K)),
    SummableUnif (fun (i : K) ↦ (fun (x : (adeleRing K)ˣ) ↦ (FunHatAdele K μ f) (y * (x + i))))
  -- Condition 3
  UnitgLp : ∀ (σ : ℝ), σ > 1 → MeasureTheory.Memℒp (fun (x : (AddUnits (adeleRing K))) ↦
    ((f (x)) * (Complex.cpow (GlobalNormAdd K x) σ))) 1 (μ.comap (↑))
  UnitsgHatLp : ∀ (σ : ℝ), σ > 1 → MeasureTheory.Memℒp (fun (x : (AddUnits (adeleRing K))) ↦
    ((FunHatAdele K μ f) x) * (Complex.cpow (GlobalNormAdele K x) σ)) 1 (μ.comap (↑))
