/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Probability.Notation
public import Statlib.EValues.NumeraireExistence
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
public import Statlib.ForMathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Reverse information projection and duality

The reverse information projection of a measure `P` on a set of measures `S` is the measure
`ripr P S = P.withDensity (numeraire P S)⁻¹`. It belongs to the effective set of `S`, the set of
measures under which every e-variable for `S` has expectation at most `1`, and it minimizes the
Kullback-Leibler divergence `klIntegral P μ` over that set. The minimal value is the maximal
expected logarithm of an e-variable: this is the duality between the maximization of the
logarithmic utility over the e-variables and the minimization of the Kullback-Leibler divergence
over the effective set.

## Main definitions

* `klIntegral μ ν`: a version of the Kullback-Leibler divergence between two measures, which
  differs from Mathlib's `klDiv` in that it has only the integral term. The two agree for measures
  of equal mass (`klIntegral_eq_klDiv`).
* `ripr P S`: the reverse information projection of the measure `P` on the set `S`.
* `effectiveSet S`: the measures under which the expectation of every e-variable for `S` is at
  most 1.

## Main statements

* `ripr_mem_effectiveSet`: the reverse information projection is in the effective set.
* `maxUtility_eq_klIntegral_ripr`: `maxUtility P S logUtility = klIntegral P (ripr P S)`.
* `maxUtility_eq_iInf_klIntegral_effectiveSet`:
  `maxUtility P S logUtility = ⨅ μ ∈ effectiveSet S, klIntegral P μ`. This is the duality between
  maximal logarithmic utility and minimal Kullback-Leibler divergence.

## References

* M. Larsson, A. Ramdas, J. Ruf, *The numeraire e-variable and reverse information projection*
  (2025).
-/

@[expose] public section

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

/-- The reverse information projection of `P` on `S`: the measure with density
`(numeraire P S)⁻¹` with respect to `P`. -/
noncomputable
def ripr (P : Measure 𝓧) (S : Set (Measure 𝓧)) : Measure 𝓧 :=
  P.withDensity fun ω ↦ (numeraire P S ω)⁻¹

lemma ripr_univ (P : Measure 𝓧) : ripr P S .univ = ∫⁻ x, (numeraire P S x)⁻¹ ∂P := by
  rw [ripr, withDensity_apply _ .univ, setLIntegral_univ]

lemma ripr_univ_le_measure_fsupport (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S .univ ≤ P (numeraire P S).fsupport := by
  rw [ripr_univ]
  simpa [numeraire] using
    lintegral_div_logNumeraire_le_measure_fsupport P (isEVarClass_isEVar S hS) (isEVar_one S)

lemma ripr_univ_le_measure_univ (P : Measure 𝓧) :
    ripr P S .univ ≤ P .univ := by
  rw [ripr_univ]
  by_cases h𝓔 : IsEVarClass {X | IsEVar X S}
  · simpa [numeraire] using lintegral_div_logNumeraire_le_measure_univ P h𝓔 (isEVar_one S)
  · have h_one : numeraire P S = 1 := by
      unfold numeraire logNumeraire
      split_ifs with h
      · exact absurd h.1 h𝓔
      · rfl
    simp [h_one]

/-- The reverse information projection is a sub-probability measure
(its total mass is at most 1). -/
lemma ripr_univ_le_one (P : Measure 𝓧) [IsProbabilityMeasure P] :
    ripr P S .univ ≤ 1 := by simpa using ripr_univ_le_measure_univ P

instance isFiniteMeasure_ripr (P : Measure 𝓧) [IsFiniteMeasure P] : IsFiniteMeasure (ripr P S) where
  measure_univ_lt_top := by
    rw [lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top (by simp) (ripr_univ_le_measure_univ P)

lemma absolutelyContinuous_ripr_of_ae_ne_top (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P ≪ ripr P S := by
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  simp only [ne_eq, ENNReal.inv_eq_zero, h_top]

/-- If the numeraire is almost everywhere finite, it is the density of `P` with respect to the
reverse information projection. -/
lemma rnDeriv_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P.rnDeriv (ripr P S) =ᵐ[P] numeraire P S := by
  refine (Measure.rnDeriv_withDensity_right _ _ (by fun_prop) ?_ ?_).trans ?_
  · simpa
  · simp only [ne_eq, ENNReal.inv_eq_top]
    exact (isNumeraire_numeraire P hS).ae_ne_zero
  simp only [inv_inv]
  filter_upwards [Measure.rnDeriv_self P] with x hx using by simp [hx]

lemma llr_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ Real.log (numeraire P S x).toReal := by
  unfold llr
  filter_upwards [rnDeriv_ripr hS h_top] with x hx using by simp [hx]

lemma llr_ripr' [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ (ENNReal.log (numeraire P S x)).toReal := by
  have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
  filter_upwards [h_ne_zero, h_top, llr_ripr hS h_top] with x hx1 hx2
  unfold ENNReal.log
  simp [hx1, hx2]

open Classical in
/-- A version of the Kullback-Leibler divergence between two measures, with only the integral term:
`∫ x, llr μ ν x ∂μ` if `μ ≪ ν` and the log-likelihood ratio is integrable, `⊤` otherwise. It
takes values in `EReal` because it may be negative for measures of different masses. For measures
of equal mass, it is Mathlib's `klDiv` (`klIntegral_eq_klDiv`). -/
noncomputable def klIntegral (μ ν : Measure 𝓧) : EReal :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then (∫ x, llr μ ν x ∂μ : ℝ) else ⊤

lemma klIntegral_of_ac_of_integrable {μ ν : Measure 𝓧} (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    klIntegral μ ν = ∫ x, llr μ ν x ∂μ := by
  simp [klIntegral, h_ac, h_int]

lemma klIntegral_of_not_ac {μ ν : Measure 𝓧} (h : ¬ μ ≪ ν) : klIntegral μ ν = ⊤ := by
  simp [klIntegral, h]

lemma klIntegral_of_not_integrable {μ ν : Measure 𝓧} (h : ¬ Integrable (llr μ ν) μ) :
    klIntegral μ ν = ⊤ := by
  simp [klIntegral, h]

/-- For measures of equal mass, `klIntegral` is the Kullback-Leibler divergence `klDiv`. -/
lemma klIntegral_eq_klDiv {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_eq : μ .univ = ν .univ) :
    klIntegral μ ν = klDiv μ ν := by
  by_cases h_ac : μ ≪ ν
  swap; · simp [klIntegral_of_not_ac h_ac, klDiv_of_not_ac h_ac]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klIntegral_of_not_integrable h_int, klDiv_of_not_integrable h_int]
  have h_nonneg := integral_llr_add_sub_measure_univ_nonneg h_ac h_int
  simp only [measureReal_def, h_eq, add_sub_cancel_right] at h_nonneg
  rw [klIntegral_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac h_int,
    measureReal_def, measureReal_def, h_eq, add_sub_cancel_right, EReal.coe_ennreal_ofReal,
    max_eq_left h_nonneg]

lemma eintegral_log_numeraire_eq_integral [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤)
    (h_int : ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤) :
    ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P = ∫ x, Real.log (numeraire P S x).toReal ∂P := by
  rw [eintegral_eq_integral_toReal (by fun_prop) (isNumeraire_numeraire P hS).eintegral_log_ne_bot
    h_int]
  congr 1
  refine integral_congr_ae ?_
  have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
  filter_upwards [h_ne_zero, h_top] with x hx1 hx2
  unfold ENNReal.log
  simp [hx1, hx2]

lemma integrable_llr_ripr_iff [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    Integrable (llr P (ripr P S)) P ↔ ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤ := by
  rw [integrable_congr (llr_ripr' hS h_top),
    integrable_toReal_iff_eintegral_ne_bot_and_ne_top (by fun_prop)]
  · simp [(isNumeraire_numeraire P hS).eintegral_log_ne_bot]
  · simp only [ne_eq, ENNReal.log_eq_bot_iff]
    exact (isNumeraire_numeraire P hS).ae_ne_zero
  · simpa

/-- The maximal logarithmic utility is the Kullback-Leibler divergence between `P` and its reverse
information projection. -/
lemma maxUtility_eq_klIntegral_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    maxUtility P S logUtility = klIntegral P (ripr P S) := by
  rw [maxUtility_eq_eintegral_numeraire _ hS]
  by_cases h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤
  · have h_ac : P ≪ ripr P S := absolutelyContinuous_ripr_of_ae_ne_top h_top
    by_cases h_int : Integrable (llr P (ripr P S)) P
    · rw [klIntegral_of_ac_of_integrable h_ac h_int, integral_congr_ae (llr_ripr hS h_top)]
      rw [integrable_congr (llr_ripr' hS h_top)] at h_int
      have h_int' := (integrable_toReal_iff_eintegral_ne_bot_and_ne_top (by fun_prop) ?_ ?_).mp
        h_int
      · rw [eintegral_log_numeraire_eq_integral hS h_top h_int'.2]
      · simp only [ne_eq, ENNReal.log_eq_bot_iff]
        exact (isNumeraire_numeraire P hS).ae_ne_zero
      · simpa
    · rw [klIntegral_of_not_integrable h_int]
      rw [integrable_llr_ripr_iff hS h_top] at h_int
      simpa using h_int
  -- if the numeraire is infinite on a set `A` of positive measure, both sides are `⊤`
  have hA : P {x | numeraire P S x = ∞} ≠ 0 := by simpa [ae_iff] using h_top
  have hA_meas : MeasurableSet {x | numeraire P S x = ∞} :=
    (measurableSet_singleton ∞).preimage (measurable_numeraire P S)
  -- the reverse information projection vanishes on `A`, so `P` is not absolutely continuous
  have h_not_ac : ¬ P ≪ ripr P S := by
    refine fun h_ac ↦ hA (h_ac ?_)
    rw [ripr, withDensity_apply _ hA_meas, setLIntegral_congr_fun hA_meas (g := fun _ ↦ 0)
      fun x hx ↦ by simp [show numeraire P S x = ∞ from hx]]
    simp
  -- the positive part of the logarithm of the numeraire is infinite on `A`
  have h_pos : ∫⁻ x, (ENNReal.log (numeraire P S x)).toENNReal ∂P = ∞ := by
    refine lintegral_eq_top_of_measure_eq_top_ne_zero (by fun_prop) fun h ↦ hA ?_
    refine measure_mono_null (fun x hx ↦ ?_) h
    simp [show numeraire P S x = ∞ from hx]
  have h_neg := lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot
    (isNumeraire_numeraire P hS).eintegral_log_ne_bot
  rw [klIntegral_of_not_ac h_not_ac, eintegral, h_pos, EReal.coe_ennreal_top,
    EReal.top_sub (by simpa using h_neg)]

/-- The effective set of a set of measures `S`: the measures under which the expectation of every
e-variable for `S` is at most 1. -/
def effectiveSet (S : Set (Measure 𝓧)) : Set (Measure 𝓧) :=
  {μ | ∀ X, IsEVar X S → ∫⁻ ω, X ω ∂μ ≤ 1}

lemma mem_effectiveSet_iff {μ : Measure 𝓧} :
    μ ∈ effectiveSet S ↔ ∀ X, IsEVar X S → ∫⁻ ω, X ω ∂μ ≤ 1 := Iff.rfl

lemma measure_univ_le_one_of_mem_effectiveSet {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S) :
    μ .univ ≤ 1 := by
  simpa using mem_effectiveSet_iff.mp hμ (fun _ ↦ 1) (isEVar_fun_one S)

lemma isFiniteMeasure_of_mem_effectiveSet {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S) :
    IsFiniteMeasure μ :=
  ⟨(measure_univ_le_one_of_mem_effectiveSet hμ).trans_lt (by simp)⟩

/-- The reverse information projection belongs to the effective set. -/
lemma ripr_mem_effectiveSet (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S ∈ effectiveSet S := by
  refine mem_effectiveSet_iff.mpr fun X hX ↦ ?_
  unfold ripr
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hX.measurable]
  have h_le := (isNumeraire_numeraire P hS).lintegral_div_le_one hX
  convert h_le with ω
  simp [ENNReal.div_eq_inv_mul]

lemma lintegral_mul_le_of_mem_effectiveSet {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫⁻ ω, X ω * (μ.rnDeriv P) ω ∂P ≤ 1 := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hμ
  simp_rw [mul_comm (X _)]
  calc ∫⁻ ω, (∂μ/∂P) ω * X ω ∂P
  _ ≤ ∫⁻ ω, X ω ∂μ := lintegral_rnDeriv_mul_le μ P hX.measurable
  _ ≤ 1 := mem_effectiveSet_iff.mp hμ X hX

lemma eintegral_log_mul_nonpos_of_mem_effectiveSet [IsProbabilityMeasure P]
    {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫ᵉ ω, ENNReal.log (X ω * (μ.rnDeriv P) ω) ∂P ≤ 0 := by
  calc ∫ᵉ ω, ENNReal.log (X ω * (μ.rnDeriv P) ω) ∂P
  _ ≤ ENNReal.log (∫⁻ ω, X ω * (μ.rnDeriv P) ω ∂P) := by
    refine Utility.eintegral_le_map logUtility ?_
    have := hX.measurable
    fun_prop
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_mul_le_of_mem_effectiveSet hμ hX

lemma eintegral_log_isEVar_le_eintegral_rnDeriv [IsProbabilityMeasure P]
    {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S) [IsFiniteMeasure μ] (h_ac : P ≪ μ)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫ᵉ ω, ENNReal.log (X ω) ∂P ≤ ∫ᵉ ω, ENNReal.log ((μ.rnDeriv P)⁻¹ ω) ∂P := by
  have hX_meas := hX.measurable
  by_cases hX_bot : ∫ᵉ ω, ENNReal.log (X ω) ∂P = ⊥
  · simp [hX_bot]
  by_cases h_top : ∫ᵉ ω, ENNReal.log ((μ.rnDeriv P)⁻¹ ω) ∂P = ⊤
  · simp only [Pi.inv_apply] at h_top
    simp [h_top]
  have h_int' : EIntegrable (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) P :=
    eintegrable_ennreal_log_rnDeriv h_ac
  have h_nonpos := eintegral_log_mul_nonpos_of_mem_effectiveSet hμ hX (P := P)
  simp_rw [ENNReal.log_mul_add] at h_nonpos
  have h_eq_sub : ∫ᵉ ω, ENNReal.log (X ω) + ENNReal.log ((∂μ/∂P) ω) ∂P =
      ∫ᵉ ω, ENNReal.log (X ω) - ENNReal.log ((∂μ/∂P)⁻¹ ω) ∂P := by
    congr with ω
    simp only [Pi.inv_apply, ENNReal.log_inv]
    rw [sub_eq_add_neg, neg_neg]
  rwa [h_eq_sub, eintegral_sub (by fun_prop) (by fun_prop) h_int' (.inr h_top) (.inl hX_bot),
    EReal.sub_nonpos] at h_nonpos

lemma klIntegral_eq_eintegral_log_inv_rnDeriv {μ : Measure 𝓧} [IsFiniteMeasure P]
    [IsFiniteMeasure μ] (h_ac : P ≪ μ) (h_int : Integrable (llr P μ) P) :
    klIntegral P μ = ∫ᵉ x, ENNReal.log ((μ.rnDeriv P)⁻¹ x) ∂P := by
  rw [klIntegral_of_ac_of_integrable h_ac h_int, integral_congr_ae (llr_ae_eq_log_inv_rnDeriv h_ac),
    ← eintegral_eq_integral]
  swap; · rw [integrable_congr (llr_ae_eq_log_inv_rnDeriv h_ac)] at h_int; simpa using h_int
  refine eintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top μ P, Measure.rnDeriv_pos' h_ac] with x hx1 hx2
  simp [ENNReal.log, hx1, hx2.ne']

/-- Weak duality: the maximal logarithmic utility is at most the Kullback-Leibler divergence
between `P` and any measure of the effective set. -/
lemma maxUtility_le_klIntegral_of_mem_effectiveSet [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S) :
    maxUtility P S logUtility ≤ klIntegral P μ := by
  by_cases h_ac : P ≪ μ
  swap; · simp [klIntegral_of_not_ac h_ac]
  by_cases h_int : Integrable (llr P μ) P
  swap; · simp [klIntegral_of_not_integrable h_int]
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hμ
  rw [klIntegral_eq_eintegral_log_inv_rnDeriv h_ac h_int, maxUtility_eq_eintegral_numeraire _ hS]
  exact eintegral_log_isEVar_le_eintegral_rnDeriv hμ h_ac (isEVar_numeraire P S)

/-- **Duality** between the maximal logarithmic utility over the e-variables and the minimal
Kullback-Leibler divergence over the effective set. -/
lemma maxUtility_eq_iInf_klIntegral_effectiveSet [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    maxUtility P S logUtility = ⨅ μ ∈ effectiveSet S, klIntegral P μ :=
  le_antisymm (le_iInf₂ fun _ ↦ maxUtility_le_klIntegral_of_mem_effectiveSet hS)
    ((iInf₂_le (ripr P S) (ripr_mem_effectiveSet P hS)).trans_eq
      (maxUtility_eq_klIntegral_ripr hS).symm)

end ProbabilityTheory
