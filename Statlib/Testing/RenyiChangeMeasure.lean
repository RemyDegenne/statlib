/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Basic
public import Statlib.Testing.ChangeMeasure

/-!
# Change of measure inequalities involving Rényi divergences

The change of measure inequalities of `Statlib.Testing.ChangeMeasure` involve the probability that
the log-likelihood ratio `llr μ ν` exceeds a threshold. We bound that probability using a Rényi
divergence of order `1 + a > 1`, through a Chernoff bound for `llr μ ν`, whose cumulant generating
function under `μ` is `a * renyiDiv (1 + a) μ ν` (`cgf_llr'`).

## Main statements

* `measureReal_llr_gt_renyiDiv_le_exp`: for probability measures and `0 < a`,
  `μ {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x} ≤ exp (-a * c)`.
* `measureReal_sub_le_measureReal_mul_exp_renyiDiv`,
  `one_sub_two_mul_exp_le_add_measureReal_mul_exp_max_renyiDiv`: change of measure inequalities in
  which the log-likelihood ratio is controlled through a Rényi divergence.
* `exp_neg_max_renyiDiv_le_add_measureReal`: a lower bound on `ν s + ν' sᶜ`, the sum of the errors
  of a test between `ν` and `ν'`, in terms of Rényi divergences from a third measure `μ`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ν' : Measure α} {a : ℝ}

/-- **Chernoff bound** for the log-likelihood ratio, in terms of a Rényi divergence. -/
lemma measureReal_llr_gt_renyiDiv_le_exp [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ∞) :
    μ.real {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x} ≤ exp (-a * c) := by
  have hμν : μ ≪ ν := absolutelyContinuous_of_renyiDiv_ne_top (by linarith) h
  rw [renyiDiv_ne_top_iff_of_one_lt (by linarith)] at h
  calc μ.real {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x}
  _ ≤ μ.real {x | (renyiDiv (1 + a) μ ν).toReal + c ≤ llr μ ν x} :=
        measureReal_mono fun _ (hx : _ < _) ↦ hx.le
  _ ≤ exp (-a * ((renyiDiv (1 + a) μ ν).toReal + c) + cgf (llr μ ν) μ a) := by
        refine measure_ge_le_exp_cgf _ ha.le ?_
        rw [integrable_congr (exp_mul_llr_of_ac hμν), integrable_rpow_rnDeriv_iff hμν ha]
        exact h.1
  _ = exp (-a * c) := by
        rw [cgf_llr' ha h.1 h.2]
        congr 1
        ring

lemma measureReal_sub_le_measureReal_mul_exp_renyiDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : Set α) (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ∞) :
    μ.real s - exp (-a * c) ≤ ν.real s * exp ((renyiDiv (1 + a) μ ν).toReal + c) := by
  have hμν : μ ≪ ν := absolutelyContinuous_of_renyiDiv_ne_top (by linarith) h
  refine le_trans ?_ (measureReal_sub_le_measureReal_mul_exp hμν s _ (measure_ne_top _ _))
  gcongr
  exact measureReal_llr_gt_renyiDiv_le_exp ha c h

lemma one_sub_two_mul_exp_le_add_measureReal_mul_exp_max_renyiDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (s : Set α) (ha : 0 < a) (c : ℝ)
    (hν : renyiDiv (1 + a) μ ν ≠ ∞) (hν' : renyiDiv (1 + a) μ ν' ≠ ∞) :
    1 - 2 * exp (-a * c)
      ≤ (ν.real s + ν'.real sᶜ)
        * exp (max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal + c) := by
  have hμν : μ ≪ ν := absolutelyContinuous_of_renyiDiv_ne_top (by linarith) hν
  have hμν' : μ ≪ ν' := absolutelyContinuous_of_renyiDiv_ne_top (by linarith) hν'
  calc 1 - 2 * exp (-a * c)
  _ = 1 - exp (-a * c) - exp (-a * c) := by ring
  _ ≤ 1 - μ.real {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x}
      - μ.real {x | (renyiDiv (1 + a) μ ν').toReal + c < llr μ ν' x} := by
        gcongr
        · exact measureReal_llr_gt_renyiDiv_le_exp ha c hν
        · exact measureReal_llr_gt_renyiDiv_le_exp ha c hν'
  _ ≤ (ν.real s + ν'.real sᶜ)
      * exp (max ((renyiDiv (1 + a) μ ν).toReal + c) ((renyiDiv (1 + a) μ ν').toReal + c)) :=
        one_sub_le_add_measureReal_mul_exp_max hμν hμν' s _ _
  _ = (ν.real s + ν'.real sᶜ)
        * exp (max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal + c) := by
        rw [max_add_add_right]

/-- Lower bound on the sum of the errors `ν s + ν' sᶜ` of a test between `ν` and `ν'`, in terms of
Rényi divergences from a third measure `μ`. -/
lemma exp_neg_max_renyiDiv_le_add_measureReal [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (s : Set α)
    (ha : 0 < a) (hν : renyiDiv (1 + a) μ ν ≠ ∞) (hν' : renyiDiv (1 + a) μ ν' ≠ ∞) :
    2⁻¹ * exp (-max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal - log 4 / a)
      ≤ ν.real s + ν'.real sᶜ := by
  have h := one_sub_two_mul_exp_le_add_measureReal_mul_exp_max_renyiDiv s ha (log 4 / a) hν hν'
  -- with `c = log 4 / a`, the left-hand side `1 - 2 * exp (-a * c)` is `1 / 2`
  have : 1 - 2 * exp (-a * (log 4 / a)) = 2⁻¹ := by
    rw [neg_mul, mul_div_cancel₀ _ ha.ne', exp_neg, exp_log (by positivity)]
    norm_num
  rw [this] at h
  rwa [neg_sub_left, exp_neg, mul_inv_le_iff₀ (exp_pos _), add_comm (log 4 / a)]

end ProbabilityTheory
