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

-- Norm on Ideles

-- Unit of products is product of units

def unit_prod_fun (A : Type) [CommRing A]
    (B : Type) [CommRing B]: Aˣ × Bˣ → (A × B) :=
      fun x => ((x.1 : A), (x.2 : B))

-- def unit_prod_fun_isunit (A : Type) [CommRing A]
--     (B : Type) [CommRing B] : ∀ (x : (Aˣ × Bˣ)), IsUnit (unit_prod_fun A B x) := by
--   intro x
--   have h1 : IsUnit x.1 := sorry
--   have h1_2 : IsUnit (x.1 : A) := Units.isUnit x.1
--   have h2 : IsUnit x.2 := sorry
--   have h2_2 : IsUnit (x.2 : B) := Units.isUnit x.2
--   have h3 : IsUnit ((x.1 : A), (x.2 : B)) := by
--     simp only [isUnit_iff_exists] at *
--     cases' h1_2 with a h1_2
--     cases' h2_2 with b h2_2
--     use (a, b)
--     simp only [Prod.mk_mul_mk, Prod.mk_eq_one]
--     exact ⟨⟨h1_2.1, h2_2.1⟩ , ⟨h1_2.2, h2_2.2⟩⟩
--   unfold unit_prod_fun
--   exact h3

def unit_prod_fun2 (A : Type) [CommRing A]
    (B : Type) [CommRing B]: Aˣ × Bˣ → (A × B)ˣ := fun
      | .mk fst snd => {
        val := unit_prod_fun A B (fst, snd)
        inv := unit_prod_fun A B (fst⁻¹, snd⁻¹)
        val_inv := by
          simp only [unit_prod_fun, Prod.mul_def]
          have h1 : (fst : A) * fst⁻¹ = 1 := by sorry
          have h2 : (snd : B) * snd⁻¹ = 1 := by sorry
          simp only [h1, h2, Prod.mk_eq_one, and_self]
        inv_val := by
          simp only [unit_prod_fun, Prod.mul_def]
          have h1 : fst⁻¹ * (fst : A) = 1 := by sorry
          have h2 : snd⁻¹ * (snd : B) = 1 := by sorry
          simp only [h1, h2, Prod.mk_eq_one, and_self]
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

lemma unit_prod (A : Type) [CommRing A]
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


-- Testing different notations. Will be deleted in final version
lemma test : (infiniteAdeleRing K) = (Π (v : InfinitePlace K), v.completion) := by
  rfl
lemma test2 : (infiniteAdeleRing K) = (∀ (v : InfinitePlace K), v.completion) := by
  rfl
lemma test3 : (infiniteAdeleRing K) = ((v : InfinitePlace K) → v.completion) := by
  rfl
lemma test4 : (∀ (v : InfinitePlace K), v.completion) := by
  intro v
  unfold InfinitePlace at v
  cases' v with v hv
  -- cases' hv
  sorry

-- Just use the corresponding place?
-- Does this say what I think it says?
def inf_adele_inj_C (v : InfinitePlace K): (v.completion) →+* ℂ :=
  let test := v.2
  sorry


def norm_inf_idele: InfinitePlace K → AbsoluteValue K ℝ := fun x => x.1 -- Is this correct?




-- Finite adeles

def NP (P : Ideal (ringOfIntegers K)): ℕ :=
  Nat.card ((ringOfIntegers K) ⧸ P)



-- This will be the e in P^e
def norm_fin_idele_initial : IsDedekindDomain.HeightOneSpectrum K → ℕ :=

  sorry


def norm_fin_idele : IsDedekindDomain.HeightOneSpectrum K → AbsoluteValue K ℝ := sorry



def norm_fin_idele2 : (finiteAdeleRing (ringOfIntegers K) K) → ℝ := sorry



-- def norm_inf_idele : (infiniteAdeleRing K)ˣ → ((v : InfinitePlace K) → ℝ) :=
--   fun x => ((v : InfinitePlace K) → )




def norm_Idele : (adeleRing K)ˣ → ℝ := fun _ => 1








-- def K_comp (G : Type) [Group G] [TopologicalSpace G]
--     [LocallyCompactSpace G] :=
--   {f : (G → ℝ) // (Continuous f) ∧ (HasCompactSupport f)}

-- def K_comp_p (G : Type) [Group G] [TopologicalSpace G]
--     [LocallyCompactSpace G] :=
--   {f : (K_comp G) // ∀ x : G, f.val x ≥ 0 ∧ ∃ y : G, f.val y > 0}

-- def μ_α (G : Type) [Group G] [AddGroup G]
--     [LocallyCompactSpace G]
--     (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
--     (α : Gˣ): AddHaarMeasure :=
--   fun f => (fun x => (μ (f.val.val (α * x))))


-- def K_norm (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
--     (α : Kˣ):  :=
--   1=1
