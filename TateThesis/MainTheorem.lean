import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.AdeleRing
import TateThesis.ContinuousAddChar
import TateThesis.SetZ
import TateThesis.GlobalNorm

/-!

# Main Theorem

This file contains the definition of the zeta function on the ideles
and the statement of the functional equation.

-/

noncomputable section

open NumberField DedekindDomain VectorFourier MeasureTheory.Measure AdeleRing

variable (K : Type*) [Field K] [NumberField K]


instance : HMul (AddChar (Additive (adeleRing K)ˣ) ℂˣ) ((adeleRing K) → ℂ) ((adeleRing K)ˣ → ℂ) where
  hMul := fun c f v ↦ c.1 v * f v

instance : HMul (AddChar (Additive (adeleRing K)ˣ) ℂ) ((adeleRing K) → ℂ) ((adeleRing K)ˣ → ℂ) where
  hMul := fun c f v ↦ c.1 v * f v

instance : HMul ℝ ℂˣ ℂ where
  hMul := fun x y ↦ x * y


/-- Zeta function on the ideles. -/
abbrev ζ (g : (adeleRing K)ˣ → ℂ) (μ : MeasureTheory.Measure (adeleRing K)ˣ) : ℂ :=
  ∫ v, g v ∂μ


-- TODO: Need to adjust the domain of c to be (adeleRing K)ˣ⧸Kˣ both in CharHat and in FunctionalEquation


/-- Character hat on the ideles. -/
abbrev CharHat (c : (ContinuousAddChar (Additive (adeleRing K)ˣ) ℂˣ)): (ContinuousAddChar (Additive (adeleRing K)ˣ) ℂ) where
  toFun := fun x ↦ (GlobalNorm K x) * (c x)⁻¹
  map_zero_one' := by
    suffices (GlobalNorm K 1) * (c 0)⁻¹ = 1 by
      convert this
    sorry
  map_add_mul' := sorry
  continuous_toFun := sorry

/-- Statments of the funcitonal equation. -/
theorem FunctionalEquation (μ_idele : MeasureTheory.Measure (adeleRing K)ˣ) [μ_idele.IsHaarMeasure]
    (μ_adele : MeasureTheory.Measure (adeleRing K)) [μ_adele.IsAddHaarMeasure]
    (μ_hat : MeasureTheory.Measure (ContinuousAddChar (adeleRing K) circle))
    [μ_hat.IsHaarMeasure] (f : ((adeleRing K) → ℂ)) (c : (ContinuousAddChar (Additive (adeleRing K)ˣ) ℂˣ)):
    ζ K (c.1 * f) μ_idele = ζ K ((CharHat K c).1 * (FunHatAdele K μ_adele f)) μ_idele := sorry
