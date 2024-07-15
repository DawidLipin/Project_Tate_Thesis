import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum DedekindDomain ProdAdicCompletions DedekindDomain.ProdAdicCompletions.IsFiniteAdele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

local notation "R_hat" => FiniteIntegralAdeles

local notation "K_hat" => ProdAdicCompletions


lemma ProdAdicCompletions.algebraMap_apply' (k : K) :
    algebraMap K (K_hat R K) k v = (k : v.adicCompletion K) := rfl

theorem algebraMap' (k : K) : (_root_.algebraMap K (K_hat R K) k).IsFiniteAdele := by
  rw [IsFiniteAdele, Filter.eventually_cofinite]
  simp_rw [mem_adicCompletionIntegers, ProdAdicCompletions.algebraMap_apply',
    Valued.valuedCompletion_apply, not_le]
  change {v : HeightOneSpectrum R | 1 < v.valuation k}.Finite
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation (_root_.algebraMap R K d : K) < 1}.Finite by
    apply Finite.subset this
    intro v hv
    apply_fun v.valuation at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [mem_setOf_eq, valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    change 1 < v.intValuation n
    rw [← hk, mul_comm]
    exact lt_mul_of_le_of_one_lt' this hv (by simp) (by simp)
  simp_rw [valuation_of_algebraMap]
  change {v : HeightOneSpectrum R | v.intValuationDef d < 1}.Finite
  simp_rw [intValuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

def FiniteAdeleRing' : Type _ := {x : K_hat R K // x.IsFiniteAdele}

def subalgebra : Subalgebra K (K_hat R K) where
  carrier := {x : K_hat R K | x.IsFiniteAdele}
  mul_mem' := mul
  one_mem' := one
  add_mem' := add
  zero_mem' := zero
  algebraMap_mem' := algebraMap'

instance : CommRing (FiniteAdeleRing' R K) :=
  Subalgebra.toCommRing (subalgebra R K)

instance : Algebra K (FiniteAdeleRing' R K) :=
  Subalgebra.algebra (subalgebra R K)

instance : Coe (FiniteAdeleRing' R K) (K_hat R K) where
  coe := fun x ↦ x.1

@[ext]
lemma ext {a₁ a₂ : FiniteAdeleRing' R K} (h : (a₁ : K_hat R K) = a₂) : a₁ = a₂ :=
  Subtype.ext h

/-- The finite adele ring is an algebra over the finite integral adeles. -/
instance : Algebra (R_hat R K) (FiniteAdeleRing' R K) where
  smul rhat fadele := ⟨fun v ↦ rhat v * fadele.1 v, Finite.subset fadele.2 <| fun v hv ↦ by
    simp only [mem_adicCompletionIntegers, mem_compl_iff, mem_setOf_eq, map_mul] at hv ⊢
    exact mt (mul_le_one₀ (rhat v).2) hv
    ⟩
  toFun r := ⟨r, by simp_all⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ _ := mul_comm _ _
  smul_def' r x := rfl
