/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Pow.Real
public import Statlib.ForMathlib.MeasureTheory.Integral.MeanInequalities
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RNDerivProd
public import Statlib.ForMathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Integrals of powers of Radon-Nikodym derivatives

We study the integral `∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν`, which appears in the Hellinger and Rényi
divergences.

## Main statements

* `integral_rpow_rnDeriv_symm`: `∫ (∂μ/∂ν) ^ a ∂ν = ∫ (∂ν/∂μ) ^ (1 - a) ∂μ`.
* `lintegral_rpow_rnDeriv_add_mul_rpow_rnDeriv_add`: for `a ∈ [0, 1)`, the integral of
  `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)` with respect to `μ + ν` is `∫⁻ (∂μ/∂ν) ^ a ∂ν`.
* `integral_rpow_rnDeriv_eq_toReal_lintegral`: for `0 ≤ a`, `∫ (∂μ/∂ν) ^ a ∂ν` is the `toReal` of
  `∫⁻ (∂μ/∂ν) ^ a ∂ν`, and `integrable_rpow_rnDeriv_iff_lintegral_ne_top`: `(∂μ/∂ν) ^ a` is
  `ν`-integrable iff `∫⁻ (∂μ/∂ν) ^ a ∂ν ≠ ∞`.
* `integrable_rpow_rnDeriv_of_le`: for a finite measure `ν` and `0 ≤ a ≤ b`, integrability of
  `(∂μ/∂ν) ^ b` implies that of `(∂μ/∂ν) ^ a`; `integrable_rpow_rnDeriv_of_lt_one`: for finite
  measures and `a ∈ [0, 1)`, `(∂μ/∂ν) ^ a` is `ν`-integrable.
* `integrable_llr_of_integrable_rpow_rnDeriv`: if `(∂μ/∂ν) ^ b` is `ν`-integrable for some `b > 1`,
  then the log-likelihood ratio is `μ`-integrable.
* `lintegral_rpow_rnDeriv_eq_zero_iff_mutuallySingular` (for `0 < a`),
  `integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular` (for `a ≠ 0`): the integral vanishes iff
  `μ ⟂ₘ ν`.
* `integral_rpow_rnDeriv_le_rpow_mul_rpow`: log-convexity of `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν`.
* `setIntegral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one`: **Hölder's inequality**
  `∫_E (∂μ/∂ν) ^ a ∂ν ≤ μ(E) ^ a * ν(E) ^ (1 - a)` for `a ∈ [0, 1]`, finite measures and any set
  `E`; `integral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one` is the case `E = univ`.
* `continuousOn_integral_rpow_rnDeriv`: if `(∂μ/∂ν) ^ c` is integrable, then
  `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν` is continuous on `(0, c]`.
* `integral_rpow_rnDeriv_smul_left`, `integral_rpow_rnDeriv_smul_right`: behaviour under scaling of
  the measures.
* `integral_rpow_rnDeriv_prod`: the integral for product measures is the product of the integrals.
* `tendsto_mul_log_integral_rpow_rnDeriv`: for probability measures with `μ ≪ ν` and `llr μ ν`
  integrable, `(a - 1)⁻¹ * log (∫ (∂μ/∂ν) ^ a ∂ν)` tends to `∫ llr μ ν ∂μ` as `a → 1⁻`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real Filter Set

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a b : ℝ}

/-! ### Symmetry -/

/-- Symmetry of the Hellinger integral: `∫ (∂μ/∂ν)^a ∂ν = ∫ (∂ν/∂μ)^(1 - a) ∂μ`. -/
lemma integral_rpow_rnDeriv_symm (ha_pos : 0 < a) (ha : a ≠ 1) [SigmaFinite μ] [SigmaFinite ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = ∫ x, (ν.rnDeriv μ x).toReal ^ (1 - a) ∂μ := by
  let p := μ.rnDeriv (μ + ν)
  let q := ν.rnDeriv (μ + ν)
  calc ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_eq_div (ξ := μ + ν)
          (Measure.AbsolutelyContinuous.rfl.add_right ν)
          (Measure.AbsolutelyContinuous.rfl.add_right' μ)] with x hx
        simp only [hx, Pi.div_apply, p, q]
  _ = ∫ x, (q x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := by
        rw [← integral_rnDeriv_smul (_ : ν ≪ μ + ν)]
        · simp [q]
        · rw [add_comm]
          exact Measure.AbsolutelyContinuous.rfl.add_right μ
  _ = ∫ x, (p x).toReal * ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := by
        refine integral_congr_ae ?_
        filter_upwards [μ.rnDeriv_lt_top (μ + ν), ν.rnDeriv_lt_top (μ + ν)]
          with x hp_top hq_top
        by_cases hp : p x = 0
        · simp [hp, ha_pos.ne']
        by_cases hq : q x = 0
        · simp only [hq, ENNReal.toReal_zero, Pi.div_apply, zero_mul, ENNReal.zero_div,
            zero_eq_mul]
          refine Or.inr ?_
          rw [zero_rpow]
          rwa [ne_eq, sub_eq_zero, Eq.comm]
        simp only [Pi.div_apply, div_eq_mul_inv, ENNReal.toReal_mul,
          mul_rpow ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.toReal_inv,
          inv_rpow ENNReal.toReal_nonneg, ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
        rw [mul_comm, mul_assoc, mul_comm _ ((p x).toReal ^ (a - 1)), ← mul_assoc (p x).toReal]
        congr
        · have : a = 1 + (a - 1) := by abel
          conv_lhs => rw [this]
          rw [rpow_add, rpow_one]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le.lt_of_ne' hp, hp_top⟩
        · rw [mul_comm, rpow_sub, rpow_one, rpow_neg ENNReal.toReal_nonneg, div_eq_mul_inv]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le.lt_of_ne' hq, hq_top⟩
  _ = ∫ x, ((q/p) x).toReal ^ (1 - a) ∂μ := by
        rw [← integral_rnDeriv_smul (_ : μ ≪ μ + ν)]
        · simp [p]
        · exact Measure.AbsolutelyContinuous.rfl.add_right ν
  _ = ∫ x, (ν.rnDeriv μ x).toReal ^ (1 - a) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_eq_div (ξ := μ + ν)
          (Measure.AbsolutelyContinuous.rfl.add_right' μ)
          (Measure.AbsolutelyContinuous.rfl.add_right ν)] with x hx
        simp only [hx, Pi.div_apply, p, q]

/-- For `μ ≪ ν`, `∫ (∂μ/∂ν) ^ a ∂ν = ∫ (∂μ/∂ν) ^ (a - 1) ∂μ`. -/
lemma integral_rpow_rnDeriv_eq_integral_rpow_sub_one (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    [SigmaFinite μ] [SigmaFinite ν] (h_ac : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = ∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ := by
  rw [integral_rpow_rnDeriv_symm ha_pos ha_ne]
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

/-- For `a ∈ [0, 1)`, the integral of `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)` with respect to
the dominating measure `μ + ν` is `∫⁻ (∂μ/∂ν) ^ a ∂ν`. -/
lemma lintegral_rpow_rnDeriv_add_mul_rpow_rnDeriv_add [SigmaFinite μ] [SigmaFinite ν]
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∫⁻ x, (μ.rnDeriv (μ + ν) x) ^ a * (ν.rnDeriv (μ + ν) x) ^ (1 - a) ∂(μ + ν)
      = ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  calc ∫⁻ x, (μ.rnDeriv (μ + ν) x) ^ a * (ν.rnDeriv (μ + ν) x) ^ (1 - a) ∂(μ + ν)
  _ = ∫⁻ x, ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ^ a ∂(μ + ν) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν (μ + ν)] with x hq_top
    rcases eq_or_ne (ν.rnDeriv (μ + ν) x) 0 with hq | hq
    · simp [hq, ENNReal.zero_rpow_of_pos (sub_pos.mpr ha1)]
    rw [ENNReal.div_rpow_of_nonneg _ _ ha0, ENNReal.rpow_sub _ _ hq hq_top.ne,
      ENNReal.rpow_one, ← mul_div_assoc, mul_comm, mul_div_assoc]
  _ = ∫⁻ x, (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ^ a ∂ν :=
    lintegral_rnDeriv_mul hν (by fun_prop)
  _ = ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_eq_div hμ hν] with x hx
    rw [← hx]

/-! ### Integrability -/

/-- For `0 ≤ a`, the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` is the `toReal` of the Lebesgue integral
`∫⁻ (∂μ/∂ν) ^ a ∂ν` (both sides are `0` when the latter is infinite). -/
lemma integral_rpow_rnDeriv_eq_toReal_lintegral [SigmaFinite μ] (ha : 0 ≤ a) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = (∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν).toReal := by
  rw [← integral_toReal (by fun_prop)]
  · simp_rw [ENNReal.toReal_rpow]
  · filter_upwards [μ.rnDeriv_lt_top ν] with x hx
    exact (ENNReal.rpow_ne_top_of_nonneg ha hx.ne).lt_top

/-- For `0 ≤ a`, the function `(∂μ/∂ν) ^ a` is integrable if and only if its integral is
finite. -/
lemma integrable_rpow_rnDeriv_iff_lintegral_ne_top [SigmaFinite μ] (ha : 0 ≤ a) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν ↔ ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν ≠ ∞ := by
  simp_rw [ENNReal.toReal_rpow]
  refine integrable_toReal_iff (by fun_prop) ?_
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  exact ENNReal.rpow_ne_top_of_nonneg ha hx.ne

/-- For `μ ≪ ν` and `0 < a`, `(∂μ/∂ν) ^ a` is `μ`-integrable if and only if `(∂μ/∂ν) ^ (1 + a)` is
`ν`-integrable. -/
lemma integrable_rpow_rnDeriv_iff [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν) (ha : 0 < a) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) μ
      ↔ Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ (1 + a)) ν := by
  rw [← integrable_rnDeriv_smul_iff hμν]
  refine integrable_congr ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [smul_eq_mul]
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [h_zero, ENNReal.toReal_zero, zero_mul]
    rw [zero_rpow]
    linarith
  · rw [rpow_add (ENNReal.toReal_pos h_zero hx), rpow_one]

/-- For a finite measure `ν` and `0 ≤ a ≤ b`, if `(∂μ/∂ν) ^ b` is `ν`-integrable, then so is
`(∂μ/∂ν) ^ a`. -/
lemma integrable_rpow_rnDeriv_of_le [IsFiniteMeasure ν] (ha : 0 ≤ a) (hab : a ≤ b)
    (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ b) ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν := by
  refine ((integrable_const 1).add h_int).mono'
    ((μ.measurable_rnDeriv ν).ennreal_toReal.pow_const a).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_one_add_rpow ENNReal.toReal_nonneg ha hab

/-- For finite measures and `a ∈ [0, 1)`, `(∂μ/∂ν) ^ a` is `ν`-integrable. -/
lemma integrable_rpow_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν :=
  integrable_rpow_rnDeriv_of_le ha_nonneg ha.le
    (by simpa using Measure.integrable_toReal_rnDeriv (μ := μ) (ν := ν))

/-- If `(∂μ/∂ν) ^ b` is integrable for some `b > 1`, then the log-likelihood ratio is
`μ`-integrable. -/
lemma integrable_llr_of_integrable_rpow_rnDeriv [SigmaFinite μ] [IsFiniteMeasure ν]
    (hb : 1 < b) (h_ac : μ ≪ ν) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ b) ν) :
    Integrable (llr μ ν) μ := by
  rw [← integrable_rnDeriv_mul_log_iff h_ac]
  refine Integrable.mono' ((integrable_const 1).add (h_int.div_const (b - 1))) ?_ ?_
  · exact ((μ.measurable_rnDeriv ν).ennreal_toReal.mul
      (μ.measurable_rnDeriv ν).ennreal_toReal.log).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact Real.abs_mul_log_le_one_add_rpow ENNReal.toReal_nonneg hb

/-! ### Positivity -/

/-- The Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` is nonnegative. -/
lemma integral_rpow_rnDeriv_nonneg : 0 ≤ ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν :=
  integral_nonneg fun _ ↦ by positivity

/-- For `0 < a`, the Hellinger integral `∫⁻ (∂μ/∂ν) ^ a ∂ν` vanishes if and only if `μ` and `ν`
are mutually singular. -/
lemma lintegral_rpow_rnDeriv_eq_zero_iff_mutuallySingular [μ.HaveLebesgueDecomposition ν]
    (ha : 0 < a) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν = 0 ↔ μ ⟂ₘ ν := by
  rw [lintegral_eq_zero_iff (by fun_prop), ← Measure.rnDeriv_eq_zero]
  refine eventually_congr (Eventually.of_forall fun x ↦ ?_)
  simp [ENNReal.rpow_eq_zero_iff, ha, not_lt.mpr ha.le]

/-- For a nonnegative function `f` vanishing exactly at `0` and `∞`, `∫ f (∂μ/∂ν) ∂ν` vanishes if
and only if `μ` and `ν` are mutually singular. -/
lemma integral_fun_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ]
    [μ.HaveLebesgueDecomposition ν] {f : ℝ≥0∞ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_zero : ∀ x, f x = 0 ↔ x = 0 ∨ x = ⊤)
    (h_int : Integrable (f ∘ μ.rnDeriv ν) ν) :
    ∫ x, f (μ.rnDeriv ν x) ∂ν = 0 ↔ μ ⟂ₘ ν := by
  rw [← Measure.rnDeriv_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ ↦ hf_nonneg _) h_int]
  apply Filter.eventually_congr
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [Pi.zero_apply, hf_zero, hx, or_false]

/-- For `a ≠ 0` and `(∂μ/∂ν) ^ a` integrable, the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` vanishes if
and only if `μ` and `ν` are mutually singular. -/
lemma integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ]
    [μ.HaveLebesgueDecomposition ν] (ha_zero : a ≠ 0)
    (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = 0 ↔ μ ⟂ₘ ν := by
  have h_nonneg : ∀ (x : ℝ≥0∞), 0 ≤ x.toReal ^ a := by
    intro x
    simp only [ENNReal.toReal_nonneg, rpow_nonneg]
  refine integral_fun_rnDeriv_eq_zero_iff_mutuallySingular h_nonneg (fun x ↦ ?_) h_int
  rw [rpow_eq_zero ENNReal.toReal_nonneg ha_zero, ENNReal.toReal_eq_zero_iff]

/-- For `a ≠ 0` and `(∂μ/∂ν) ^ a` integrable, the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` is positive
if and only if `μ` and `ν` are not mutually singular. -/
lemma integral_rpow_rnDeriv_pos_iff_not_mutuallySingular [SigmaFinite μ]
    [μ.HaveLebesgueDecomposition ν] (ha_zero : a ≠ 0)
    (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    0 < ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν ↔ ¬ μ ⟂ₘ ν := by
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero h_int]
  push Not
  exact ⟨fun h ↦ h.ne', fun h ↦ integral_rpow_rnDeriv_nonneg.lt_of_ne' h⟩

/-! ### Log-convexity and continuity in the exponent -/

/-- Real version of the log-convexity of `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν`. -/
lemma integral_rpow_rnDeriv_le_rpow_mul_rpow [SigmaFinite μ] {c θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc : c = θ * a + (1 - θ) * b)
    (ha_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν)
    (hb_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ b) ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ c ∂ν
      ≤ (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) ^ θ
        * (∫ x, (μ.rnDeriv ν x).toReal ^ b ∂ν) ^ (1 - θ) := by
  have hc_nonneg : 0 ≤ c := hc ▸ add_nonneg (mul_nonneg hθ0 ha) (mul_nonneg (by linarith) hb)
  have ha_top := (integrable_rpow_rnDeriv_iff_lintegral_ne_top ha).mp ha_int
  have hb_top := (integrable_rpow_rnDeriv_iff_lintegral_ne_top hb).mp hb_int
  rw [integral_rpow_rnDeriv_eq_toReal_lintegral hc_nonneg,
    integral_rpow_rnDeriv_eq_toReal_lintegral ha, integral_rpow_rnDeriv_eq_toReal_lintegral hb,
    ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  have h := ENNReal.lintegral_rpow_le_rpow_mul_rpow (μ := ν)
    (μ.measurable_rnDeriv ν).aemeasurable ha hb hθ0 hθ1
  rw [← hc] at h
  refine ENNReal.toReal_mono ?_ h
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0 ha_top)
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) hb_top)

/-- If `(∂μ/∂ν) ^ c` is integrable, then `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν` is continuous on `(0, c]`. -/
lemma continuousOn_integral_rpow_rnDeriv [IsFiniteMeasure ν] {c : ℝ}
    (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ c) ν) :
    ContinuousOn (fun a ↦ ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) (Ioc 0 c) := by
  refine continuousOn_of_dominated (bound := fun x ↦ 1 + (μ.rnDeriv ν x).toReal ^ c) ?_ ?_ ?_ ?_
  · exact fun a _ ↦ ((μ.measurable_rnDeriv ν).ennreal_toReal.pow_const _).aestronglyMeasurable
  · intro a ha
    refine Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_add_rpow ENNReal.toReal_nonneg ha.1.le ha.2
  · exact (integrable_const _).add h_int
  · exact Eventually.of_forall fun x a ha ↦
      (Real.continuousAt_const_rpow' ha.1.ne').continuousWithinAt

/-! ### Hölder's inequality -/

/-- **Hölder's inequality** for the Radon-Nikodym derivative: for `a ∈ [0, 1]`, finite measures
and any set `E`, `∫_E (∂μ/∂ν) ^ a ∂ν ≤ μ(E) ^ a * ν(E) ^ (1 - a)`. -/
lemma setIntegral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (E : Set α) :
    ∫ x in E, (μ.rnDeriv ν x).toReal ^ a ∂ν ≤ μ.real E ^ a * ν.real E ^ (1 - a) := by
  have h_le : ∫⁻ x in E, μ.rnDeriv ν x ^ a ∂ν ≤ μ E ^ a * ν E ^ (1 - a) :=
    calc ∫⁻ x in E, μ.rnDeriv ν x ^ a ∂ν = ∫⁻ x in E, μ.rnDeriv ν x ^ a * 1 ^ (1 - a) ∂ν := by simp
    _ ≤ (∫⁻ x in E, μ.rnDeriv ν x ∂ν) ^ a * (∫⁻ _ in E, 1 ∂ν) ^ (1 - a) :=
      ENNReal.lintegral_mul_norm_pow_le (μ.measurable_rnDeriv ν).aemeasurable aemeasurable_const
        ha0 (sub_nonneg.mpr ha1) (by ring)
    _ ≤ μ E ^ a * ν E ^ (1 - a) := by
      rw [setLIntegral_one]
      gcongr
      exact Measure.setLIntegral_rnDeriv_le E
  have h_eq :
      ∫ x in E, (μ.rnDeriv ν x).toReal ^ a ∂ν = (∫⁻ x in E, μ.rnDeriv ν x ^ a ∂ν).toReal := by
    simp_rw [ENNReal.toReal_rpow]
    refine integral_toReal ((μ.measurable_rnDeriv ν).pow_const a).aemeasurable ?_
    filter_upwards [ae_restrict_of_ae (μ.rnDeriv_lt_top ν)] with x hx
    exact ENNReal.rpow_lt_top_of_nonneg ha0 hx.ne
  rw [h_eq, measureReal_def, measureReal_def, ENNReal.toReal_rpow, ENNReal.toReal_rpow,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness) h_le

/-- **Hölder's inequality** for the Radon-Nikodym derivative: for `a ∈ [0, 1]` and finite
measures, `∫ (∂μ/∂ν) ^ a ∂ν ≤ μ(α) ^ a * ν(α) ^ (1 - a)`. -/
lemma integral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν ≤ (μ .univ).toReal ^ a * (ν .univ).toReal ^ (1 - a) := by
  simpa [measureReal_def] using setIntegral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one ha0 ha1 .univ

/-- For `a ∈ (0, 1)` and finite measures that are not mutually singular,
`log (∫ (∂μ/∂ν) ^ a ∂ν) ≤ a * log μ(α) + (1 - a) * log ν(α)`. -/
lemma log_integral_rpow_rnDeriv_le_of_lt_one (ha_pos : 0 < a) (ha_lt : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ms : ¬ μ ⟂ₘ ν) :
    Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
      ≤ a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal := by
  have hμ : μ ≠ 0 := fun h ↦ h_ms (by rw [h]; exact .zero_left)
  have hν : ν ≠ 0 := fun h ↦ h_ms (by rw [h]; exact .zero_right)
  have hm : 0 < (μ .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
  have hn : 0 < (ν .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)
  rw [← Real.log_rpow hm, ← Real.log_rpow hn,
    ← Real.log_mul (rpow_pos_of_pos hm _).ne' (rpow_pos_of_pos hn _).ne']
  refine Real.log_le_log ?_ (integral_rpow_rnDeriv_le_rpow_mul_rpow_of_le_one ha_pos.le ha_lt.le)
  exact (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne'
    (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)).mpr h_ms

/-! ### Scaling and products -/

/-- Scaling `μ` by `c` multiplies the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` by `c ^ a`. -/
lemma integral_rpow_rnDeriv_smul_left [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0) :
    ∫ x, ((c • μ).rnDeriv ν x).toReal ^ a ∂ν = c ^ a * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_left' μ ν c] with x hx
  rw [← mul_rpow NNReal.zero_le_coe ENNReal.toReal_nonneg, hx, Pi.smul_apply, ENNReal.toReal_smul]
  rfl

/-- Scaling `ν` by `c` multiplies the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` by `c ^ (1 - a)`. -/
lemma integral_rpow_rnDeriv_smul_right [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0)
    (ha : c = 0 → a ≠ 1) :
    ∫ x, (μ.rnDeriv (c • ν) x).toReal ^ a ∂(c • ν)
      = c ^ (1 - a) * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  by_cases hc : c = 0
  · simp [hc, zero_rpow <| sub_ne_zero_of_ne (ha hc).symm]
  rw [integral_smul_nnreal_measure, ← integral_const_mul, NNReal.smul_def, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_right' μ ν hc] with x hx
  rw [hx, Pi.smul_apply, ENNReal.toReal_smul, smul_eq_mul, NNReal.smul_def, smul_eq_mul,
    mul_rpow NNReal.zero_le_coe ENNReal.toReal_nonneg, NNReal.coe_inv, inv_rpow NNReal.zero_le_coe,
    ← mul_assoc, mul_eq_mul_right_iff]
  left
  rw [rpow_sub, rpow_one, div_eq_mul_inv]
  exact NNReal.coe_pos.mpr <| pos_iff_ne_zero.mpr hc

/-- Version of `integral_rpow_rnDeriv_smul_left` for a scalar `c : ℝ≥0∞`. -/
lemma integral_rpow_rnDeriv_smul_left' [SigmaFinite μ] [SigmaFinite ν] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫ x, ((c • μ).rnDeriv ν x).toReal ^ a ∂ν
      = c.toReal ^ a * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  lift c to ℝ≥0 using hc
  rw [← ENNReal.smul_def, ENNReal.coe_toReal]
  exact integral_rpow_rnDeriv_smul_left c

/-- Version of `integral_rpow_rnDeriv_smul_right` for a scalar `c : ℝ≥0∞`. -/
lemma integral_rpow_rnDeriv_smul_right' [SigmaFinite μ] [SigmaFinite ν] {c : ℝ≥0∞} (hc : c ≠ ∞)
    (ha : c = 0 → a ≠ 1) :
    ∫ x, (μ.rnDeriv (c • ν) x).toReal ^ a ∂(c • ν)
      = c.toReal ^ (1 - a) * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  lift c to ℝ≥0 using hc
  rw [← ENNReal.smul_def, ENNReal.coe_toReal]
  exact integral_rpow_rnDeriv_smul_right c fun h ↦ ha (by simp [h])

/-- `∫ (∂μ/∂ν)^a ∂ν` is `μ(univ)^a * ν(univ)^(1 - a)` times its value for the normalized
measures. -/
lemma integral_rpow_rnDeriv_eq_mul_integral_rpow_rnDeriv_inv_smul (ha_ne : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] [NeZero ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
      = (μ .univ).toReal ^ a * (ν .univ).toReal ^ (1 - a)
        * ∫ x, (((μ .univ)⁻¹ • μ).rnDeriv ((ν .univ)⁻¹ • ν) x).toReal ^ a ∂((ν .univ)⁻¹ • ν) := by
  have hm : 0 < (μ .univ).toReal := ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  have hn : 0 < (ν .univ).toReal := ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  rw [integral_rpow_rnDeriv_smul_right' (ENNReal.inv_ne_top.mpr (NeZero.ne _)) (fun _ ↦ ha_ne),
    integral_rpow_rnDeriv_smul_left' (ENNReal.inv_ne_top.mpr (NeZero.ne _)),
    ENNReal.toReal_inv, ENNReal.toReal_inv, inv_rpow hn.le, inv_rpow hm.le]
  have h1 : (μ .univ).toReal ^ a ≠ 0 := (rpow_pos_of_pos hm a).ne'
  have h2 : (ν .univ).toReal ^ (1 - a) ≠ 0 := (rpow_pos_of_pos hn _).ne'
  field_simp

/-- The Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` of product measures is the product of the Hellinger
integrals. -/
lemma integral_rpow_rnDeriv_prod {β : Type*} {mβ : MeasurableSpace β} (μ₁ ν₁ : Measure α)
    (μ₂ ν₂ : Measure β)
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂] :
    ∫ p, ((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) p).toReal ^ a ∂(ν₁.prod ν₂)
      = (∫ x, (μ₁.rnDeriv ν₁ x).toReal ^ a ∂ν₁) * ∫ y, (μ₂.rnDeriv ν₂ y).toReal ^ a ∂ν₂ := by
  rw [← integral_prod_mul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_prod μ₁ ν₁ μ₂ ν₂] with p hp
  rw [hp, ENNReal.toReal_mul, mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

/-! ### Behaviour as `a → 1⁻` -/

/-- For `μ ≪ ν` with `llr μ ν` integrable, the slope
`(a - 1)⁻¹ * (∫ (∂μ/∂ν) ^ a ∂ν - μ univ)` tends to `∫ llr μ ν ∂μ` as `a → 1⁻`: this is the left
derivative at `1` of `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν`. -/
lemma tendsto_integral_rpow_rnDeriv_sub_div [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν - (μ .univ).toReal)) (𝓝[<] 1)
      (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  rw [← integral_rnDeriv_mul_log hμν]
  have h_ev : ∀ᶠ a in 𝓝[<] (1:ℝ), a ∈ Set.Ico 2⁻¹ 1 := Ico_mem_nhdsLT (by norm_num)
  -- the slope of the integral is the integral of the slopes `((∂μ/∂ν) ^ a - ∂μ/∂ν) / (a - 1)`
  have h_eq : (fun a ↦ (a - 1)⁻¹ * (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν - (μ .univ).toReal))
      =ᶠ[𝓝[<] (1:ℝ)]
        fun a ↦ ∫ x, ((μ.rnDeriv ν x).toReal ^ a - (μ.rnDeriv ν x).toReal) / (a - 1) ∂ν := by
    filter_upwards [h_ev] with a ha
    rw [integral_div, integral_sub (integrable_rpow_rnDeriv_of_lt_one (by linarith [ha.1]) ha.2)
      Measure.integrable_toReal_rnDeriv, Measure.integral_toReal_rnDeriv hμν, measureReal_def,
      div_eq_inv_mul]
  refine Tendsto.congr' h_eq.symm ?_
  -- for `a ∈ [1/2, 1)`, the slopes lie between `-1/2` and `∂μ/∂ν * log (∂μ/∂ν)`
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ 2⁻¹ + |(μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a ↦ (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [h_ev] with a ha
    refine Eventually.of_forall fun x ↦ ?_
    have h1 := Real.neg_inv_two_le_rpow_sub_self_div_sub_one (t := (μ.rnDeriv ν x).toReal)
      ENNReal.toReal_nonneg ha.1 ha.2.ne
    have h2 := Real.rpow_sub_self_div_sub_one_le_mul_log (t := (μ.rnDeriv ν x).toReal)
      ENNReal.toReal_nonneg ha.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [abs_nonneg ((μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal),
      le_abs_self ((μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal)]
  · exact (integrable_const _).add ((integrable_rnDeriv_mul_log_iff hμν).mpr h_int).abs
  · exact Eventually.of_forall fun x ↦ (Real.tendsto_rpow_sub_self_div_sub_one _).mono_left
      (nhdsWithin_mono _ fun y hy ↦ ne_of_lt (Set.mem_Iio.mp hy))

/-- For finite measures with `μ ≠ 0`, `μ ≪ ν` and `llr μ ν` integrable, the slope at `1` of
`a ↦ log (∫ (∂μ/∂ν) ^ a ∂ν) - a * log (μ univ) - (1 - a) * log (ν univ)` tends to
`(μ univ)⁻¹ * ∫ llr μ ν ∂μ - log (μ univ / ν univ)` as `a → 1⁻`. -/
lemma tendsto_mul_log_integral_rpow_rnDeriv' [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
        - (a - 1)⁻¹ * (a * log (μ .univ).toReal + (1 - a) * log (ν .univ).toReal))
      (𝓝[<] 1)
      (𝓝 ((μ .univ).toReal⁻¹ * ∫ x, llr μ ν x ∂μ
        - log ((μ .univ).toReal / (ν .univ).toReal))) := by
  have hm : (μ .univ).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨NeZero.ne _, measure_ne_top _ _⟩
  have hn : (ν .univ).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    refine ⟨fun h ↦ ?_, measure_ne_top _ _⟩
    have hν : ν = 0 := Measure.measure_univ_eq_zero.mp h
    rw [hν, Measure.absolutelyContinuous_zero_iff] at hμν
    exact NeZero.ne μ hμν
  set φ : ℝ → ℝ := fun a ↦ ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν with hφ
  have hφ1 : φ 1 = (μ .univ).toReal := by
    simp [φ, Measure.integral_toReal_rnDeriv hμν, measureReal_def]
  have hφ' : HasDerivWithinAt φ (∫ x, llr μ ν x ∂μ) (Set.Iio 1) 1 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Iio (1 : ℝ)) (x := 1) (by simp)]
    refine (tendsto_integral_rpow_rnDeriv_sub_div hμν h_int).congr fun a ↦ ?_
    rw [slope_def_field, div_eq_inv_mul, hφ1]
  have hlog : HasDerivWithinAt (fun a ↦ log (φ a))
      ((μ .univ).toReal⁻¹ * ∫ x, llr μ ν x ∂μ) (Set.Iio 1) 1 := by
    have := (Real.hasDerivAt_log (by rw [hφ1]; exact hm)).comp_hasDerivWithinAt 1 hφ'
    rwa [hφ1] at this
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Iio (1 : ℝ)) (x := 1) (by simp)] at hlog
  rw [Real.log_div hm hn]
  refine (hlog.sub_const (log (μ .univ).toReal - log (ν .univ).toReal)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : a < 1)
  rw [slope_def_field, hφ1]
  have : a - 1 ≠ 0 := sub_ne_zero.mpr ha.ne
  field_simp
  ring

/-- For probability measures with `μ ≪ ν` and `llr μ ν` integrable,
`(a - 1)⁻¹ * log (∫ (∂μ/∂ν) ^ a ∂ν)` tends to `∫ llr μ ν ∂μ` as `a → 1⁻`. -/
lemma tendsto_mul_log_integral_rpow_rnDeriv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)) (𝓝[<] 1)
      (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  simpa using tendsto_mul_log_integral_rpow_rnDeriv' hμν h_int

end MeasureTheory
