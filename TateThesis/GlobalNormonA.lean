import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

noncomputable section

open NumberField DedekindDomain VectorFourier MeasureTheory.Measure Multiplicative DiscreteValuation

variable (K : Type*) [Field K] [NumberField K]

theorem locallyCompactSpace : LocallyCompactSpace (adeleRing K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace (𝓞 K) K
  exact Prod.locallyCompactSpace _ _

instance adeleRingLocallyCompact : LocallyCompactSpace (adeleRing K) := by
  exact locallyCompactSpace K

-- Norm on Ideles

-- Unit of products is a product of units

def unit_prod_fun (A : Type) [CommRing A]
    (B : Type) [CommRing B]: Aˣ × Bˣ → (A × B) :=
      fun x => ((x.1 : A), (x.2 : B))

def unit_prod_fun2 (A : Type) [CommRing A]
    (B : Type) [CommRing B]: Aˣ × Bˣ → (A × B)ˣ := fun
      | .mk fst snd => {
        val := unit_prod_fun A B (fst, snd)
        inv := unit_prod_fun A B (fst⁻¹, snd⁻¹)
        val_inv := by
          simp only [unit_prod_fun, Prod.mul_def]
          simp only [Units.mul_inv, Prod.mk_eq_one, and_self]
        inv_val := by
          simp only [unit_prod_fun, Prod.mul_def]
          norm_cast
          simp only [mul_left_inv, Units.val_one, Prod.mk_eq_one, and_self]
      }

def unit_prod_fun3 (A : Type) [CommRing A]
    (B : Type) [CommRing B]: (A × B)ˣ → Aˣ × Bˣ := fun
      | .mk val inv val_inv inv_val => {
        fst := {
          val := val.1
          inv := inv.1
          val_inv := by
            have h1: val * inv = 1 := val_inv
            simp [Prod.mul_def] at h1
            cases' h1 with h1
            exact h1
          inv_val := by
            have h1: inv * val = 1 := inv_val
            simp [Prod.mul_def] at h1
            cases' h1 with h1
            exact h1
        }
        snd := {
          val := val.2
          inv := inv.2
          val_inv := by
            have h1: val * inv = 1 := val_inv
            simp [Prod.mul_def] at h1
            cases' h1 with _ h1
            exact h1
          inv_val := by
            have h1: inv * val = 1 := inv_val
            simp [Prod.mul_def] at h1
            cases' h1 with _ h1
            exact h1
        }
      }

def unit_prod (A : Type) [CommRing A]
    (B : Type) [CommRing B]: Aˣ × Bˣ ≃* (A × B)ˣ where
      toFun := unit_prod_fun2 A B
      invFun := unit_prod_fun3 A B
      left_inv := by
        intro x
        exact rfl
      right_inv := by
        intro x
        exact rfl
      map_mul' := by
        intro x y
        exact rfl

-- Norm on infinite adeles

open InfiniteAdeleRing

open Classical in
def infiniteNorm (x : infiniteAdeleRing K) : ℝ := ∏ v, ‖x v‖ ^ (if v.IsReal then 1 else 2)

-- Norm on finite adeles

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Multiplicative DiscreteValuation

#check ℤₘ₀

def Zm0.toFun (r : ℝ) (x : ℤₘ₀) : ℝ := WithZero.recZeroCoe 0 (fun z : Multiplicative ℤ ↦ r ^ (toAdd z)) x

variable (r : ℝ)

lemma Zm0.toFun_zero :Zm0.toFun r 0 = 0 := rfl

lemma Zm0.toFun_coe_int (z : ℤ) :Zm0.toFun r (ofAdd z : Multiplicative ℤ) = r ^ z := rfl

lemma Zm0.toFun_coe_mult_int (z : Multiplicative ℤ) :Zm0.toFun r z = r ^ (toAdd z) := rfl

lemma tdrgdfgh (x : ℤ) (y : ℤ) : r ^ (x) * r ^ (y) = r ^ (x + y) := by
  rw [zpow_add r x y]
  sorry

lemma test1234 (x : Multiplicative ℤ) (y : Multiplicative ℤ) :
    Zm0.toFun r (x * y) = Zm0.toFun r (x) * Zm0.toFun r (y) := by
  rw [Zm0.toFun_coe_mult_int]
  rw [Zm0.toFun_coe_mult_int]
  norm_cast
  rw [Zm0.toFun_coe_mult_int]
  simp only [toAdd_mul]

  sorry

def Zm0.toReal (r : ℝ) : ℤₘ₀ →* ℝ where
  toFun := Zm0.toFun r
  map_one' := by
    suffices toFun r 1 = r ^ 0 by
      convert this
    exact Zm0.toFun_coe_int r 0
  map_mul' := by
    intro x y
    simp only
    cases' x with x
    · have h1: toFun r (0 * y) = toFun r none := rfl
      rw [← h1]
      simp only [zero_mul, Zm0.toFun_zero]
      cases' y
      · rfl
      · rfl
    · cases' y with y
      · have h1: toFun r 0 = toFun r none := rfl
        rw [← h1]
        simp only [zero_mul, Zm0.toFun_zero, mul_zero]
        rfl
      · have h1 : Zm0.toFun r (x * y) = Zm0.toFun r (x) * Zm0.toFun r (y) := test1234 r x y


        exact h1

    -- need to do cases









def NP (P : Ideal (𝓞 K)): ℕ :=
  Nat.card ((𝓞 K) ⧸ P)







#lint
