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
at most `c` is at most `exp c` times the mass that `ν` puts on `s`. These inequalities are the
basis of lower bounds for hypothesis testing in terms of the log-likelihood ratio.

## Main statements

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

/-- **Change of measure inequality**: `μ s - μ {x | c < llr μ ν x} ≤ ν s * exp c`. -/
lemma measure_sub_le_measure_mul_exp [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α)
    (c : ℝ) :
    μ s - μ {x | c < llr μ ν x} ≤ ν s * ENNReal.ofReal (exp c) := by
  set t := {x | llr μ ν x ≤ c}
  have ht : MeasurableSet t := measurableSet_le (measurable_llr _ _) measurable_const
  -- on `t`, `∂ν/∂μ = exp (-llr μ ν) ≥ exp (-c)`
  have h_ae : ∀ᵐ x ∂μ.restrict (s ∩ t), 1 ≤ ENNReal.ofReal (exp c) * ν.rnDeriv μ x := by
    refine ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right ?_
    rw [ae_restrict_iff' ht]
    filter_upwards [exp_neg_llr hμν, ν.rnDeriv_ne_top μ] with x hx hx_top hxt
    rw [← ENNReal.ofReal_toReal hx_top, ← hx, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add,
      ENNReal.one_le_ofReal]
    exact one_le_exp (by simp only [t, Set.mem_ofPred_eq] at hxt; linarith)
  calc μ s - μ {x | c < llr μ ν x}
  _ ≤ μ (s ∩ t) := by
    rw [tsub_le_iff_right]
    refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le (s ∩ t) _)
    by_cases h : llr μ ν x ≤ c
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (not_le.mp h)
  _ = ∫⁻ _ in s ∩ t, 1 ∂μ := (setLIntegral_one _).symm
  _ ≤ ∫⁻ x in s ∩ t, ENNReal.ofReal (exp c) * ν.rnDeriv μ x ∂μ := lintegral_mono_ae h_ae
  _ = ENNReal.ofReal (exp c) * ∫⁻ x in s ∩ t, ν.rnDeriv μ x ∂μ :=
    lintegral_const_mul _ (ν.measurable_rnDeriv μ)
  _ ≤ ENNReal.ofReal (exp c) * ν (s ∩ t) := by grw [Measure.setLIntegral_rnDeriv_le]
  _ ≤ ν s * ENNReal.ofReal (exp c) := by
    rw [mul_comm]
    grw [Set.inter_subset_left]

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
