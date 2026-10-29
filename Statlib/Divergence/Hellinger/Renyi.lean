/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Basic

/-!
# Squared Hellinger distance and Rényi divergence of order `1/2`

For probability measures, the squared Hellinger distance `sqHellinger μ ν` is related to the
Bhattacharyya coefficient `∫ √(∂μ/∂ν) ∂ν` by `1 - H²(μ, ν) = ∫ √(∂μ/∂ν) ∂ν`
(`one_sub_toReal_sqHellinger`), and the Rényi divergence of order `1/2` is
`R_{1/2}(μ, ν) = -2 log (1 - H²(μ, ν))`.

## Main statements

* `toReal_renyiDiv_inv_two`, `renyiDiv_inv_two_of_not_mutuallySingular`: for probability
  measures, `R_{1/2}(μ, ν) = -2 log (1 - H²(μ, ν))`.
* `exp_neg_toReal_renyiDiv_inv_two_div_two`: for probability measures which are not mutually
  singular, `exp (-R_{1/2}(μ, ν) / 2) = 1 - H²(μ, ν)`.
* `two_mul_sqHellinger_le_renyiDiv_inv_two`: for probability measures,
  `2 * H²(μ, ν) ≤ R_{1/2}(μ, ν)`.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014).
-/

@[expose] public section

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- For probability measures, `R_{1/2}(μ, ν) = ∞` iff `H²(μ, ν) = 1`, that is iff the measures are
mutually singular. -/
lemma renyiDiv_inv_two_eq_top_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    renyiDiv 2⁻¹ μ ν = ∞ ↔ sqHellinger μ ν = 1 := by
  rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num),
    sqHellinger_eq_one_iff]

/-- The Rényi divergence of order `1/2` between probability measures which are not mutually
singular is `-2 log (1 - H²(μ, ν))`. -/
lemma renyiDiv_inv_two_of_not_mutuallySingular [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ms : ¬ μ ⟂ₘ ν) :
    renyiDiv 2⁻¹ μ ν = ENNReal.ofReal (-2 * Real.log (1 - (sqHellinger μ ν).toReal)) := by
  rw [renyiDiv_eq_log_integral_of_lt_one (by norm_num) (by norm_num) h_ms,
    one_sub_toReal_sqHellinger]
  simp_rw [Real.sqrt_eq_rpow, one_div]
  norm_num

/-- **Rényi divergence of order `1/2` and squared Hellinger distance**: for probability measures,
`R_{1/2}(μ, ν) = -2 log (1 - H²(μ, ν))`. If the measures are mutually singular, both sides are
`0` since `R_{1/2}(μ, ν) = ∞` and `Real.log 0 = 0`. -/
lemma toReal_renyiDiv_inv_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (renyiDiv 2⁻¹ μ ν).toReal = -2 * Real.log (1 - (sqHellinger μ ν).toReal) := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms,
      toReal_sqHellinger_eq_one_iff.mpr h_ms]
    simp
  rw [renyiDiv_inv_two_of_not_mutuallySingular h_ms, ENNReal.toReal_ofReal]
  have h_lt := toReal_sqHellinger_lt_one h_ms
  have h_log : Real.log (1 - (sqHellinger μ ν).toReal) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith [ENNReal.toReal_nonneg (a := sqHellinger μ ν)])
  linarith

/-- For probability measures which are not mutually singular,
`exp (- R_{1/2}(μ, ν) / 2) = 1 - H²(μ, ν)`. -/
lemma exp_neg_toReal_renyiDiv_inv_two_div_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ms : ¬ μ ⟂ₘ ν) :
    Real.exp (-(renyiDiv 2⁻¹ μ ν).toReal / 2) = 1 - (sqHellinger μ ν).toReal := by
  rw [toReal_renyiDiv_inv_two]
  have h_pos : 0 < 1 - (sqHellinger μ ν).toReal := by
    linarith [toReal_sqHellinger_lt_one h_ms]
  rw [show -(-2 * Real.log (1 - (sqHellinger μ ν).toReal)) / 2
    = Real.log (1 - (sqHellinger μ ν).toReal) by ring, Real.exp_log h_pos]

/-- For probability measures, `2 * H²(μ, ν) ≤ R_{1/2}(μ, ν)`. -/
lemma two_mul_sqHellinger_le_renyiDiv_inv_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2 * sqHellinger μ ν ≤ renyiDiv 2⁻¹ μ ν := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms]
    exact le_top
  have h_eq : 2 * sqHellinger μ ν = ENNReal.ofReal (2 * (sqHellinger μ ν).toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (sqHellinger_ne_top μ ν),
      ENNReal.ofReal_ofNat]
  rw [h_eq, renyiDiv_inv_two_of_not_mutuallySingular h_ms]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_lt := toReal_sqHellinger_lt_one h_ms
  have h_log := Real.log_le_sub_one_of_pos (x := 1 - (sqHellinger μ ν).toReal) (by linarith)
  linarith

end ProbabilityTheory
