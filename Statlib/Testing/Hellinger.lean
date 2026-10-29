/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Hellinger.Renyi

/-!
# Testing lower bounds from Rényi divergences of order less than `1`

For probability measures `μ`, `ν`, an event `s` and `a ∈ (0, 1)`,
`μ(s) ^ a + ν(sᶜ) ^ (1 - a) ≥ exp (-(1 - a) * Rₐ(μ, ν))`. In particular, the two errors of a test
cannot both be small if the Rényi divergence is small. For `a = 1/2`, this gives a bound in terms of
the squared Hellinger distance: `√μ(s) + √ν(sᶜ) ≥ exp (-R_{1/2}(μ, ν) / 2) = 1 - H²(μ, ν)`.

## Main statements

* `exp_neg_mul_renyiDiv_le_add_rpow`: `exp (-(1 - a) * Rₐ(μ, ν)) ≤ μ(s) ^ a + ν(sᶜ) ^ (1 - a)`.
* `one_sub_sqHellinger_le_sqrt_add_sqrt`: `1 - H²(μ, ν) ≤ √μ(s) + √ν(sᶜ)`.
-/

@[expose] public section

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- **Testing lower bound** from the Rényi divergence: for probability measures `μ`, `ν`, an event
`s` and `a ∈ [0, 1]`, `exp (-(1 - a) * Rₐ(μ, ν)) ≤ μ(s) ^ a + ν(sᶜ) ^ (1 - a)`. The cases `a = 0`
and `a = 1` are trivial: the left-hand side is at most `1` and the right-hand side at least `1`. -/
theorem exp_neg_mul_renyiDiv_le_add_rpow [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set α) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h : renyiDiv a μ ν ≠ ∞) :
    exp (-(1 - a) * (renyiDiv a μ ν).toReal) ≤ μ.real s ^ a + ν.real sᶜ ^ (1 - a) := by
  rcases ha0.eq_or_lt with rfl | ha0
  · have : exp (-(renyiDiv 0 μ ν).toReal) ≤ 1 := exp_le_one_iff.mpr (by simp)
    simp only [sub_zero, neg_mul, one_mul, rpow_zero, rpow_one]
    linarith [measureReal_nonneg (μ := ν) (s := sᶜ)]
  rcases ha1.eq_or_lt with rfl | ha1
  · simp
  have ha1' : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
  -- it suffices to prove the bound for the measurable set `F = toMeasurable μ s ⊇ s`
  set F := toMeasurable μ s
  have hF : MeasurableSet F := measurableSet_toMeasurable μ s
  have h_le : μ.real F ^ a + ν.real Fᶜ ^ (1 - a) ≤ μ.real s ^ a + ν.real sᶜ ^ (1 - a) := by
    have hFE : μ.real F = μ.real s := by simp [F, measureReal_def, measure_toMeasurable]
    have h_compl : ν.real Fᶜ ^ (1 - a) ≤ ν.real sᶜ ^ (1 - a) :=
      rpow_le_rpow measureReal_nonneg
        (measureReal_mono (Set.compl_subset_compl.mpr (subset_toMeasurable μ s))) ha1'
    rw [hFE]
    linarith
  refine le_trans ?_ h_le
  have h_ms : ¬ μ ⟂ₘ ν := (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).not.mp h
  have h_int := integrable_rpow_rnDeriv_of_lt_one (μ := μ) (ν := ν) ha0.le ha1
  have h_pos := (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha0.ne' h_int).mpr h_ms
  have h_exp : exp (-(1 - a) * (renyiDiv a μ ν).toReal) = ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
    rw [toReal_renyiDiv_of_lt_one ha0 ha1 h_ms]
    simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero]
    rw [← mul_assoc, show -(1 - a) * (a - 1)⁻¹ = 1 by
      rw [neg_sub, mul_inv_cancel₀ (sub_ne_zero.mpr ha1.ne)], one_mul, exp_log h_pos]
  have h1 : μ.real F ^ a * ν.real F ^ (1 - a) ≤ μ.real F ^ a :=
    mul_le_of_le_one_right (by positivity) (rpow_le_one measureReal_nonneg measureReal_le_one ha1')
  have h2 : μ.real Fᶜ ^ a * ν.real Fᶜ ^ (1 - a) ≤ ν.real Fᶜ ^ (1 - a) :=
    mul_le_of_le_one_left (by positivity) (rpow_le_one measureReal_nonneg measureReal_le_one ha0.le)
  rw [h_exp, ← integral_add_compl hF h_int]
  exact add_le_add
    ((setIntegral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one ha0.le ha1.le F).trans h1)
    ((setIntegral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one ha0.le ha1.le Fᶜ).trans h2)

/-- **Testing lower bound** from the squared Hellinger distance: for probability measures `μ`,
`ν` and an event `s`, `1 - H²(μ, ν) ≤ √μ(s) + √ν(sᶜ)`. If `μ` and `ν` are not mutually singular,
`1 - H²(μ, ν) = exp (-R_{1/2}(μ, ν) / 2)` (`exp_neg_toReal_renyiDiv_inv_two_div_two`), and this is
the case `a = 1/2` of `exp_neg_mul_renyiDiv_le_add_rpow`. -/
theorem one_sub_sqHellinger_le_sqrt_add_sqrt (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : Set α) :
    1 - (sqHellinger μ ν).toReal ≤ √(μ.real s) + √(ν.real sᶜ) := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [toReal_sqHellinger_eq_one_iff.mpr h_ms, sub_self]
    positivity
  have h_ne_top : renyiDiv 2⁻¹ μ ν ≠ ∞ := by
    rwa [Ne, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)]
  have h := exp_neg_mul_renyiDiv_le_add_rpow s (by norm_num) (by norm_num) h_ne_top
  rw [← exp_neg_toReal_renyiDiv_inv_two_div_two h_ms, sqrt_eq_rpow, sqrt_eq_rpow]
  convert h using 2
  · ring
  · norm_num
  · norm_num

end ProbabilityTheory
