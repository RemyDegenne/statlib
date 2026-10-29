/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Change of measure inequalities

The mass that `μ` puts on a set `s` and on the set where the log-likelihood ratio `llr μ ν` is
at most `c` is at most `exp c` times the mass that `ν` puts on `s`. More generally, the same holds
for the integrals of a function with values in `[0, 1]`. These inequalities are the basis of lower
bounds for hypothesis testing in terms of the log-likelihood ratio.

## Main statements

* `lintegral_sub_le_lintegral_mul_exp`: for `μ ≪ ν` and `f` with values in `[0, 1]`,
  `∫⁻ f ∂μ - μ {x | c < llr μ ν x} ≤ (∫⁻ f ∂ν) * exp c`.
* `integral_sub_le_integral_mul_exp`: the same inequality for real functions, for a finite
  measure `ν`.
* `measure_sub_le_measure_mul_exp`, `measureReal_sub_le_measureReal_mul_exp`:
  `μ s - μ {x | c < llr μ ν x} ≤ ν s * exp c`, for any set `s` and `c : ℝ`.
* `one_sub_le_add_measureReal_mul_exp`: for a probability measure `μ` and any set `s`, the masses
  `ν s` and `ν' sᶜ` cannot both be small unless `μ` puts mass on large values of `llr μ ν` or
  `llr μ ν'`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ν' : Measure α}

/-- **Change of measure inequality** for functions with values in `[0, 1]`:
`∫⁻ f ∂μ - μ {x | c < llr μ ν x} ≤ (∫⁻ f ∂ν) * exp c`.
See `measure_sub_le_measure_mul_exp` for the case of an indicator function. -/
lemma lintegral_sub_le_lintegral_mul_exp [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    {f : α → ℝ≥0∞} (hf_le : ∀ᵐ x ∂μ, f x ≤ 1) (c : ℝ) :
    ∫⁻ x, f x ∂μ - μ {x | c < llr μ ν x} ≤ (∫⁻ x, f x ∂ν) * ENNReal.ofReal (exp c) := by
  set t := {x | llr μ ν x ≤ c}
  have ht : MeasurableSet t := measurableSet_le (measurable_llr _ _) measurable_const
  have ht_compl : tᶜ = {x | c < llr μ ν x} := by ext; simp [t]
  -- on `t`, `∂ν/∂μ = exp (-llr μ ν) ≥ exp (-c)`
  have h_ae : ∀ᵐ x ∂μ.restrict t, f x ≤ ENNReal.ofReal (exp c) * (ν.rnDeriv μ x * f x) := by
    rw [ae_restrict_iff' ht]
    filter_upwards [exp_neg_llr hμν, ν.rnDeriv_ne_top μ] with x hx hx_top hxt
    have h1 : 1 ≤ ENNReal.ofReal (exp c) * ν.rnDeriv μ x := by
      rw [← ENNReal.ofReal_toReal hx_top, ← hx, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add,
        ENNReal.one_le_ofReal]
      exact one_le_exp (by simp only [t, Set.mem_ofPred_eq] at hxt; linarith)
    calc f x = 1 * f x := (one_mul _).symm
    _ ≤ ENNReal.ofReal (exp c) * ν.rnDeriv μ x * f x := by gcongr
    _ = ENNReal.ofReal (exp c) * (ν.rnDeriv μ x * f x) := mul_assoc _ _ _
  calc ∫⁻ x, f x ∂μ - μ {x | c < llr μ ν x}
  _ ≤ ∫⁻ x in t, f x ∂μ := by
    rw [tsub_le_iff_right, ← lintegral_add_compl f ht, ← ht_compl]
    gcongr
    calc ∫⁻ x in tᶜ, f x ∂μ ≤ ∫⁻ _ in tᶜ, 1 ∂μ := lintegral_mono_ae (ae_restrict_of_ae hf_le)
    _ = μ tᶜ := by simp
  _ ≤ ∫⁻ x in t, ENNReal.ofReal (exp c) * (ν.rnDeriv μ x * f x) ∂μ := lintegral_mono_ae h_ae
  _ = ENNReal.ofReal (exp c) * ∫⁻ x in t, ν.rnDeriv μ x * f x ∂μ :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  _ ≤ ENNReal.ofReal (exp c) * ∫⁻ x, ν.rnDeriv μ x * f x ∂μ := by
    gcongr
    exact Measure.restrict_le_self
  _ = ENNReal.ofReal (exp c) * ∫⁻ x, f x ∂(μ.withDensity (ν.rnDeriv μ)) := by
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (ν.measurable_rnDeriv μ)
      (ν.rnDeriv_lt_top μ)]
    rfl
  _ ≤ ENNReal.ofReal (exp c) * ∫⁻ x, f x ∂ν := by
    gcongr
    exact Measure.withDensity_rnDeriv_le ν μ
  _ = (∫⁻ x, f x ∂ν) * ENNReal.ofReal (exp c) := mul_comm _ _

/-- **Change of measure inequality**: `μ s - μ {x | c < llr μ ν x} ≤ ν s * exp c`. -/
lemma measure_sub_le_measure_mul_exp [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α)
    (c : ℝ) :
    μ s - μ {x | c < llr μ ν x} ≤ ν s * ENNReal.ofReal (exp c) := by
  have ht := measurableSet_toMeasurable ν s
  calc μ s - μ {x | c < llr μ ν x}
  _ ≤ ∫⁻ x, (toMeasurable ν s).indicator 1 x ∂μ - μ {x | c < llr μ ν x} := by
    rw [lintegral_indicator_one ht]
    gcongr
    exact subset_toMeasurable ν s
  _ ≤ (∫⁻ x, (toMeasurable ν s).indicator 1 x ∂ν) * ENNReal.ofReal (exp c) :=
    lintegral_sub_le_lintegral_mul_exp hμν
      (ae_of_all _ fun x ↦ Set.indicator_le (fun _ _ ↦ le_rfl) x) c
  _ = ν s * ENNReal.ofReal (exp c) := by rw [lintegral_indicator_one ht, measure_toMeasurable]

/-- **Change of measure inequality**: `μ s - μ {x | c < llr μ ν x} ≤ ν s * exp c`. -/
lemma measureReal_sub_le_measureReal_mul_exp [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (s : Set α) (c : ℝ) (hμc : μ {x | c < llr μ ν x} ≠ ∞) :
    μ.real s - μ.real {x | c < llr μ ν x} ≤ ν.real s * exp c := by
  calc μ.real s - μ.real {x | c < llr μ ν x}
  _ ≤ (μ s - μ {x | c < llr μ ν x}).toReal := ENNReal.le_toReal_sub hμc
  _ ≤ (ν s * ENNReal.ofReal (exp c)).toReal :=
    ENNReal.toReal_mono (by finiteness) (measure_sub_le_measure_mul_exp hμν s c)
  _ = ν.real s * exp c := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le, measureReal_def]

/-- **Change of measure inequality** for real functions with values in `[0, 1]`:
`∫ f ∂μ - μ {x | c < llr μ ν x} ≤ (∫ f ∂ν) * exp c`. -/
lemma integral_sub_le_integral_mul_exp [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {f : α → ℝ} (hf : AEStronglyMeasurable f ν) (hf_nonneg : ∀ᵐ x ∂ν, 0 ≤ f x)
    (hf_le : ∀ᵐ x ∂ν, f x ≤ 1) (c : ℝ) (hμc : μ {x | c < llr μ ν x} ≠ ∞) :
    ∫ x, f x ∂μ - μ.real {x | c < llr μ ν x} ≤ (∫ x, f x ∂ν) * exp c := by
  have h_nonneg (ρ : Measure α) (hρ : ρ ≪ ν) : 0 ≤ ∫ x, f x ∂ρ :=
    integral_nonneg_of_ae (hρ.ae_le hf_nonneg)
  have h_int (ρ : Measure α) (hρ : ρ ≪ ν) (hρf : Integrable f ρ) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂ρ = ENNReal.ofReal (∫ x, f x ∂ρ) :=
    (ofReal_integral_eq_lintegral_ofReal hρf (hρ.ae_le hf_nonneg)).symm
  have hν_int : Integrable f ν := by
    refine Integrable.of_bound (C := 1) hf ?_
    filter_upwards [hf_nonneg, hf_le] with x hx0 hx1
    rwa [Real.norm_of_nonneg hx0]
  by_cases hμ_int : Integrable f μ
  swap
  · -- `f` is not `μ`-integrable (`μ` may be infinite): the left-hand side is nonpositive
    rw [integral_undef hμ_int, zero_sub]
    exact (neg_nonpos.mpr measureReal_nonneg).trans
      (mul_nonneg (h_nonneg ν .rfl) (exp_pos _).le)
  have h := lintegral_sub_le_lintegral_mul_exp hμν
    (hμν.ae_le (hf_le.mono fun x hx ↦ ENNReal.ofReal_le_one.mpr hx)) c
  rw [h_int μ hμν hμ_int, h_int ν .rfl hν_int] at h
  calc ∫ x, f x ∂μ - μ.real {x | c < llr μ ν x}
  _ ≤ (ENNReal.ofReal (∫ x, f x ∂μ) - μ {x | c < llr μ ν x}).toReal := by
    have h_sub := ENNReal.le_toReal_sub (a := ENNReal.ofReal (∫ x, f x ∂μ)) hμc
    rwa [ENNReal.toReal_ofReal (h_nonneg μ hμν)] at h_sub
  _ ≤ (ENNReal.ofReal (∫ x, f x ∂ν) * ENNReal.ofReal (exp c)).toReal :=
    ENNReal.toReal_mono (by finiteness) h
  _ = (∫ x, f x ∂ν) * exp c := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h_nonneg ν .rfl),
      ENNReal.toReal_ofReal (exp_pos _).le]

/-- For a probability measure `μ` and any set `s`, the masses `ν s` and `ν' sᶜ` cannot both be
small unless `μ` puts mass on large values of `llr μ ν` or `llr μ ν'`. -/
lemma one_sub_le_add_measureReal_mul_exp [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    [IsProbabilityMeasure μ] (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - μ.real {x | c < llr μ ν x} - μ.real {x | c' < llr μ ν' x}
      ≤ ν.real s * exp c + ν'.real sᶜ * exp c' := by
  have h := measureReal_sub_le_measureReal_mul_exp hμν s c (measure_ne_top _ _)
  have h' := measureReal_sub_le_measureReal_mul_exp hμν' sᶜ c' (measure_ne_top _ _)
  calc 1 - μ.real {x | c < llr μ ν x} - μ.real {x | c' < llr μ ν' x}
  _ ≤ μ.real s + μ.real sᶜ - μ.real {x | c < llr μ ν x} - μ.real {x | c' < llr μ ν' x} := by
    gcongr
    calc (1 : ℝ) = (μ .univ).toReal := by simp
    _ ≤ (μ s + μ sᶜ).toReal :=
      ENNReal.toReal_mono (by finiteness) (measure_univ_le_add_compl s)
    _ = μ.real s + μ.real sᶜ := ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  _ = (μ.real s - μ.real {x | c < llr μ ν x}) + (μ.real sᶜ - μ.real {x | c' < llr μ ν' x}) := by
    abel
  _ ≤ ν.real s * exp c + ν'.real sᶜ * exp c' := by gcongr

/-- For a probability measure `μ` and any set `s`, the masses `ν s` and `ν' sᶜ` cannot both be
small unless `μ` puts mass on large values of `llr μ ν` or `llr μ ν'`. -/
lemma one_sub_le_add_measureReal_mul_exp_max [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    [IsProbabilityMeasure μ] (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - μ.real {x | c < llr μ ν x} - μ.real {x | c' < llr μ ν' x}
      ≤ (ν.real s + ν'.real sᶜ) * exp (max c c') := by
  refine (one_sub_le_add_measureReal_mul_exp hμν hμν' s c c').trans ?_
  rw [add_mul]
  gcongr
  · exact le_max_left _ _
  · exact le_max_right _ _

end ProbabilityTheory
