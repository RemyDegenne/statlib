/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.ForMathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Statlib.Divergence.Chernoff.Properties
public import Statlib.Divergence.TotalVariation

/-!
# Bayes binary risk, Rényi and Chernoff divergences

We bound the Bayes risk of simple binary hypothesis testing by the Rényi divergences between the
two hypotheses: for `a ∈ (0, 1)` and probability measures `μ`, `ν`,
`B_π(μ, ν) ≤ π({false}) ^ a * π({true}) ^ (1 - a) * exp (-(1 - a) * Rₐ(μ, ν))`.
Optimizing over `a`, we get a bound in terms of the Chernoff divergence:
`B_π(μ, ν) ≤ max (π({false}), π({true})) * exp (-C₁(μ, ν))`.

The proof uses `min x y ≤ x ^ a * y ^ (1 - a)` inside the integral formula
`B_π(μ, ν) = ∫ min (π({false}) * ∂μ/∂ν, π({true})) ∂ν`, and the expression of
`∫ (∂μ/∂ν) ^ a ∂ν` in terms of the Rényi divergence (`lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv`).

## Main statements

* `bayesBinaryRisk_le_mul_lintegral_rpow_rnDeriv`: for `a ∈ [0, 1]`,
  `B_π(μ, ν) ≤ π({false}) ^ a * π({true}) ^ (1 - a) * ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν`.
* `bayesBinaryRisk_eq_mul_lintegral_min_withDensity_rpow`: an identity of Zhou and Li, an exact
  expression of the Bayes binary risk as an integral with respect to a tilted measure.
* `bayesBinaryRisk_le_mul_exp_renyiDiv`: the bound on the Bayes binary risk, for finite measures.
  `bayesBinaryRisk_le_mul_exp_renyiDiv_of_isProbabilityMeasure` is its version for probability
  measures.
* `bayesBinaryRisk_le_max_mul_exp_chernoffDiv`: for finite measures,
  `B_π(μ, ν) ≤ max (π({false}) * μ(univ), π({true}) * ν(univ)) * exp (-C₁(μ, ν))`.
* `bayesBinaryRisk_le_exp_chernoffDiv`: for probability measures,
  `B_π(μ, ν) ≤ exp (-C₁(μ, ν))` when `π({false}), π({true}) ≤ 1`.
* `ofReal_one_sub_tvDist_div_two_le_exp_chernoffDiv`: `1 - tvDist μ ν / 2 ≤ exp (-C₁(μ, ν))`.

The Rényi divergence of statlib is the one of the normalized measures, hence the factors
`μ(univ) ^ a * ν(univ) ^ (1 - a)` for finite measures. The exponential is `EReal.exp`, so that
the bounds are also correct (and equal to `0`) when the divergence is infinite.

## References

* Z. Zhou, P. Li, *Non-asymptotic Chernoff lower bound and its application to community detection
  in stochastic block model*, arXiv:1812.11269 (2018).
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {a : ℝ}

/-- For `a ∈ [0, 1]`, the Bayes binary risk is bounded by
`π({false}) ^ a * π({true}) ^ (1 - a) * ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν`. -/
lemma bayesBinaryRisk_le_mul_lintegral_rpow_rnDeriv (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    bayesBinaryRisk μ ν π ≤ π {false} ^ a * π {true} ^ (1 - a) * ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν := by
  rw [bayesBinaryRisk_eq_lintegral_min_rnDeriv, ← lintegral_const_mul _
    ((μ.measurable_rnDeriv ν).pow_const a)]
  refine lintegral_mono fun x ↦ ?_
  calc min (π {false} * (∂μ/∂ν) x) (π {true})
      ≤ (π {false} * (∂μ/∂ν) x) ^ a * π {true} ^ (1 - a) :=
        ENNReal.min_le_rpow_mul_rpow _ _ ha0 ha1
    _ = π {false} ^ a * π {true} ^ (1 - a) * (∂μ/∂ν) x ^ a := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha0]; ring

/-- An identity of Zhou and Li: for `a ∈ (0, 1)`, the Bayes binary risk is
`π({false}) ^ a * π({true}) ^ (1 - a) * ∫ min ((π({false}) * ∂μ/∂ν / π({true})) ^ (1 - a),
(π({true}) / (π({false}) * ∂μ/∂ν)) ^ a)` with respect to the tilted measure
`ν.withDensity ((∂μ/∂ν) ^ a)`. For probability measures, that tilted measure has total mass
`exp (-(1 - a) * Rₐ(μ, ν))` (see `lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv`), and
`renyiMeasure a μ ν` is its normalization (see `renyiMeasure_eq_withDensity`). -/
theorem bayesBinaryRisk_eq_mul_lintegral_min_withDensity_rpow (μ ν : Measure 𝒳)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π]
    (ha0 : 0 < a) (ha1 : a < 1) :
    bayesBinaryRisk μ ν π = π {false} ^ a * π {true} ^ (1 - a)
      * ∫⁻ x, min ((π {false} * (∂μ/∂ν) x / π {true}) ^ (1 - a))
          ((π {true} / (π {false} * (∂μ/∂ν) x)) ^ a) ∂(ν.withDensity fun x ↦ (∂μ/∂ν) x ^ a) := by
  have ha1' : 0 < 1 - a := by linarith
  by_cases hπ0 : π {false} = 0
  · rw [bayesBinaryRisk_of_measure_false_eq_zero μ ν hπ0, hπ0, ENNReal.zero_rpow_of_pos ha0,
      zero_mul, zero_mul]
  by_cases hπ1 : π {true} = 0
  · rw [bayesBinaryRisk_of_measure_true_eq_zero μ ν hπ1, hπ1, ENNReal.zero_rpow_of_pos ha1',
      mul_zero, zero_mul]
  have hπ0_top : π {false} ≠ ∞ := measure_ne_top _ _
  have hπ1_top : π {true} ≠ ∞ := measure_ne_top _ _
  have h_meas : Measurable fun x ↦ min ((π {false} * (∂μ/∂ν) x / π {true}) ^ (1 - a))
      ((π {true} / (π {false} * (∂μ/∂ν) x)) ^ a) := by
    have h := μ.measurable_rnDeriv ν
    exact ((h.const_mul _).div_const _ |>.pow_const _).min
      ((measurable_const.div (h.const_mul _)).pow_const _)
  rw [lintegral_withDensity_eq_lintegral_mul _ ((μ.measurable_rnDeriv ν).pow_const a) h_meas,
    ← lintegral_const_mul _ (((μ.measurable_rnDeriv ν).pow_const a).mul h_meas),
    bayesBinaryRisk_eq_lintegral_min_rnDeriv]
  refine lintegral_congr_ae ?_
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  simp only [Pi.mul_apply]
  by_cases hx0 : (∂μ/∂ν) x = 0
  · simp [hx0, ENNReal.zero_rpow_of_pos ha0]
  rw [ENNReal.min_eq_rpow_mul_rpow_mul_min (mul_ne_zero hπ0 hx0)
    (ENNReal.mul_ne_top hπ0_top hx.ne) hπ1 hπ1_top a,
    ENNReal.mul_rpow_of_nonneg _ _ ha0.le]
  ring

/-- For `a ∈ (0, 1)` and finite measures, the Bayes binary risk is bounded by
`π({false}) ^ a * π({true}) ^ (1 - a) * μ(univ) ^ a * ν(univ) ^ (1 - a)
* exp (-(1 - a) * Rₐ(μ, ν))`. -/
theorem bayesBinaryRisk_le_mul_exp_renyiDiv (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] (ha0 : 0 < a) (ha1 : a < 1) :
    bayesBinaryRisk μ ν π
      ≤ π {false} ^ a * π {true} ^ (1 - a) * μ .univ ^ a * ν .univ ^ (1 - a)
        * EReal.exp (-(((1 - a : ℝ) : EReal) * renyiDiv a μ ν)) := by
  refine (bayesBinaryRisk_le_mul_lintegral_rpow_rnDeriv μ ν π ha0.le ha1.le).trans_eq ?_
  rw [lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv ha0 ha1]
  ring

/-- For `a ∈ (0, 1)` and probability measures, the Bayes binary risk is bounded by
`π({false}) ^ a * π({true}) ^ (1 - a) * exp (-(1 - a) * Rₐ(μ, ν))`. -/
theorem bayesBinaryRisk_le_mul_exp_renyiDiv_of_isProbabilityMeasure (μ ν : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (π : Measure Bool) [IsFiniteMeasure π]
    (ha0 : 0 < a) (ha1 : a < 1) :
    bayesBinaryRisk μ ν π
      ≤ π {false} ^ a * π {true} ^ (1 - a)
        * EReal.exp (-(((1 - a : ℝ) : EReal) * renyiDiv a μ ν)) := by
  simpa using bayesBinaryRisk_le_mul_exp_renyiDiv μ ν π ha0 ha1

/-- For finite measures `μ`, `ν`, the Bayes binary risk is bounded by
`max (π({false}) * μ(univ), π({true}) * ν(univ)) * exp (-C₁(μ, ν))`, where `C₁` is the Chernoff
divergence. -/
theorem bayesBinaryRisk_le_max_mul_exp_chernoffDiv (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≤ max (π {false} * μ .univ) (π {true} * ν .univ)
      * EReal.exp (-(chernoffDiv 1 μ ν : EReal)) := by
  set M := max (π {false} * μ .univ) (π {true} * ν .univ) with hM_def
  rcases eq_or_ne M 0 with hM0 | hM0
  · have hB := (bayesBinaryRisk_le_min μ ν π).trans (min_le_max.trans_eq hM0)
    rw [nonpos_iff_eq_zero.mp hB]
    exact zero_le
  have hM_top : M ≠ ∞ := max_ne_top (by finiteness) (by finiteness)
  -- bound for each order `a ∈ (0, 1)`
  have h_open : ∀ a ∈ Ioo (0 : ℝ) 1, bayesBinaryRisk μ ν π / M
      ≤ EReal.exp (-((ENNReal.ofReal (1 - a) * renyiDiv a μ ν : ℝ≥0∞) : EReal)) := by
    intro a ha
    have ha1 : 0 ≤ 1 - a := by linarith [ha.2]
    rw [ENNReal.div_le_iff' hM0 hM_top, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
      max_eq_left ha1]
    refine (bayesBinaryRisk_le_mul_exp_renyiDiv μ ν π ha.1 ha.2).trans (mul_le_mul_left ?_ _)
    calc π {false} ^ a * π {true} ^ (1 - a) * μ .univ ^ a * ν .univ ^ (1 - a)
        = (π {false} * μ .univ) ^ a * (π {true} * ν .univ) ^ (1 - a) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha.1.le, ENNReal.mul_rpow_of_nonneg _ _ ha1]
          ring
      _ ≤ M ^ a * M ^ (1 - a) := mul_le_mul' (ENNReal.rpow_le_rpow (le_max_left _ _) ha.1.le)
          (ENNReal.rpow_le_rpow (le_max_right _ _) ha1)
      _ = M := by rw [← ENNReal.rpow_add_of_nonneg _ _ ha.1.le ha1]; simp
  -- optimize over the order
  rw [← ENNReal.div_le_iff' hM0 hM_top, chernoffDiv_one_eq_iSup_mul_renyiDiv,
    ← iSup_Ioo_mul_renyiDiv_eq_iSup_Icc]
  exact EReal.le_exp_neg_biSup (nonempty_Ioo.mpr zero_lt_one) h_open

/-- For probability measures `μ`, `ν` and a prior with `π({false}), π({true}) ≤ 1`, the Bayes binary
risk is bounded by `exp (-C₁(μ, ν))`, where `C₁` is the Chernoff divergence. -/
theorem bayesBinaryRisk_le_exp_chernoffDiv (μ ν : Measure 𝒳) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (π : Measure Bool) (hπ0 : π {false} ≤ 1) (hπ1 : π {true} ≤ 1) :
    bayesBinaryRisk μ ν π ≤ EReal.exp (-(chernoffDiv 1 μ ν : EReal)) := by
  have : IsFiniteMeasure π := by
    rw [Measure.eq_boolMeasure π]
    exact Measure.isFiniteMeasure_boolMeasure (ne_top_of_le_ne_top ENNReal.one_ne_top hπ0)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hπ1)
  refine (bayesBinaryRisk_le_max_mul_exp_chernoffDiv μ ν π).trans
    (mul_le_of_le_one_left zero_le ?_)
  simpa using max_le hπ0 hπ1

/-- For probability measures, `1 - TV(μ, ν) ≤ exp (-C₁(μ, ν))`, where `TV(μ, ν) = tvDist μ ν / 2`
and `C₁` is the Chernoff divergence. -/
theorem ofReal_one_sub_tvDist_div_two_le_exp_chernoffDiv (μ ν : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (1 - tvDist μ ν / 2) ≤ EReal.exp (-(chernoffDiv 1 μ ν : EReal)) := by
  rw [← bayesBinaryRisk_one_one_eq_ofReal_one_sub_tvDist_div_two]
  exact bayesBinaryRisk_le_exp_chernoffDiv μ ν _ (by simp) (by simp)

end ProbabilityTheory
