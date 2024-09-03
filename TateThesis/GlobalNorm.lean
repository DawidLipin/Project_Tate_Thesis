import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Quotient

/-!

# Norm on Idele Gorup

This file defines the norm on idele gorup.
The norms is only well defined on the ideles,
however we develop it in the general cases of the
inifite adeles and finite adeles to simplify our work.

-/

noncomputable section

open NumberField DedekindDomain VectorFourier AdeleRing
  MeasureTheory.Measure Multiplicative DiscreteValuation

variable (K : Type*) [Field K] [NumberField K]



-- Norm on the infinite adeles

open InfiniteAdeleRing

open BigOperators

open Classical in
/-- Norm on infinite adeles -/
def infiniteNorm (x : infiniteAdeleRing K) : ℝ := ∏ v, ‖x v‖ ^ (if v.IsReal then 1 else 2)




-- Norm on the finite adeles

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Multiplicative DiscreteValuation

/-- API that allows to work with elements of ℤₘ₀ as 0 and x rather than 'none' and 'some val'. -/
@[elab_as_elim]
protected lemma Zm0.induction_on {motive : ℤₘ₀ → Prop} (zero : motive 0)
  (of_int : ∀ z : ℤ, motive (ofAdd z : Multiplicative ℤ)) (x : ℤₘ₀) : motive x :=
WithZero.recZeroCoe zero of_int x

/-- Coerce elemetns of ℤₘ₀ to ℝ -/
def Zm0.toFun (r : ℝ) (x : ℤₘ₀) : ℝ := WithZero.recZeroCoe 0 (fun z : Multiplicative ℤ ↦ r ^ (toAdd z)) x

variable (r : ℝ)

lemma Zm0.toFun_zero : Zm0.toFun r 0 = 0 := rfl

lemma Zm0.toFun_coe_int (z : ℤ) :Zm0.toFun r (ofAdd z : Multiplicative ℤ) = r ^ z := rfl

lemma Zm0.toFun_coe_mult_int (z : Multiplicative ℤ) :Zm0.toFun r z = r ^ (toAdd z) := rfl

/-- Monoid homomorphism ℤₘ₀ to ℝ -/
def Zm0.toReal (r : ℝ) (h1: 0 < r) : ℤₘ₀ →* ℝ where
  toFun := Zm0.toFun r
  map_one' := by
    suffices toFun r 1 = r ^ 0 by
      convert this
    exact Zm0.toFun_coe_int r 0
  map_mul' := by
    intro x y
    simp only
    induction' x using Zm0.induction_on with x
    · simp only [Zm0.toFun_zero, zero_mul]
    · induction' y using Zm0.induction_on with y
      · simp only [Zm0.toFun_zero, mul_zero]
      · norm_cast
        simp only [toFun_coe_mult_int, toAdd_mul, toAdd_ofAdd]
        have h2: r ^ ((x : ℝ) + (y : ℝ)) = r ^ x * r ^ y := by
          rw [Real.rpow_add h1 x y]
          simp only [Real.rpow_int_cast]
        rw [← h2]
        norm_cast


instance : HasQuotient (𝓞 K) (HeightOneSpectrum (𝓞 K)) where
  quotient' := fun h ↦ 𝓞 K ⧸ h.asIdeal

/-- Size of residue field -/
abbrev NP (I : HeightOneSpectrum (𝓞 K)): ℕ :=
  Ideal.absNorm (I.asIdeal)

lemma NPNeZero (I : HeightOneSpectrum (𝓞 K)): (NP K I) ≠ 0 := by
  rw [NP, ne_eq, Ideal.absNorm_eq_zero_iff]
  exact I.ne_bot

lemma NPGeZero (I : HeightOneSpectrum (𝓞 K)): (0 : ℝ) < (NP K I) := by
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NPNeZero K I))

/-- Norm on finite adeles -/
def finiteNorm (x : finiteAdeleRing (𝓞 K) K): ℝ :=
    ∏ᶠ (v : HeightOneSpectrum (𝓞 K)), (Zm0.toReal (NP K v) (NPGeZero K v) (Valued.v (x.1 v)))



-- Norm on ideles

/-- Norm on ideles as units of adeles -/
def GlobalNorm (x : (adeleRing K)ˣ): ℝ := (finiteNorm K (x.1.2)) * (infiniteNorm K x.1.1)

/-- Norm on ideles as additive units of adeles -/
def GlobalNormAdd (x : (AddUnits (adeleRing K))): ℝ := (finiteNorm K (x.1.2)) * (infiniteNorm K x.1.1)

/-- The norm is only well defined on the ideles. We retain this general defintion
to allow us to work on elements of the adele ring with the idelic considtions
applied separately. -/
def GlobalNormAdele (x : (adeleRing K)): ℝ := (finiteNorm K x.2) * (infiniteNorm K x.1)
