/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Statlib.ForMathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Integrals of powers of Radon-Nikodym derivatives

We study the integral `∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν`, which appears in the Hellinger and Rényi
divergences.

## Main statements

* `integral_rpow_rnDeriv_symm`: `∫ (∂μ/∂ν) ^ a ∂ν = ∫ (∂ν/∂μ) ^ (1 - a) ∂μ`.
* `lintegral_rpow_rnDeriv_add_mul_rpow_rnDeriv_add`: for `a ∈ [0, 1)`, the integral of
  `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)` with respect to `μ + ν` is `∫⁻ (∂μ/∂ν) ^ a ∂ν`.
* `integrable_rpow_rnDeriv_of_lt_one`: for finite measures and `a ∈ [0, 1)`, `(∂μ/∂ν) ^ a` is
  `ν`-integrable.
* `integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular`: for `a ≠ 0`, the integral vanishes iff
  `μ ⟂ₘ ν`.
* `integral_rpow_rnDeriv_smul_left`, `integral_rpow_rnDeriv_smul_right`: behaviour under scaling of
  the measures.
* `tendsto_mul_log_integral_rpow_rnDeriv`: for probability measures with `μ ≪ ν` and `llr μ ν`
  integrable, `(a - 1)⁻¹ * log (∫ (∂μ/∂ν) ^ a ∂ν)` tends to `∫ llr μ ν ∂μ` as `a → 1⁻`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real Filter Set

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

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

lemma integrable_rpow_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν := by
  rw [← integrable_neg_iff]
  have h_cvx : ConvexOn ℝ (Ici 0) (fun y : ℝ ↦ -y ^ a) := (concaveOn_rpow ha_nonneg ha.le).neg
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top (f := fun y ↦ -y ^ a) μ ν h_cvx ?_
  -- the right derivative `-a * x ^ (a - 1)` tends to `0`
  have h_eq : (fun x ↦ derivWithin (fun y : ℝ ↦ -y ^ a) (Ioi x) x)
      =ᶠ[atTop] fun x ↦ -(a * x ^ (a - 1)) := by
    filter_upwards [eventually_ne_atTop 0] with x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl hx)).neg.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi x)
  have h_lim : Tendsto (fun x : ℝ ↦ -(a * x ^ (a - 1))) atTop (𝓝 0) := by
    have : (fun (x : ℝ) ↦ x ^ (a - 1)) = (fun x ↦ x ^ (-(1 - a))) := by ext x; simp
    simpa [this] using ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - a)).const_mul a).neg
  rw [(h_cvx.subset Ioi_subset_Ici_self (convex_Ioi 0)).derivAtTop_eq_of_tendsto_rightDeriv
    ((tendsto_congr' h_eq).mpr h_lim)]
  simp

lemma integral_rpow_rnDeriv_nonneg : 0 ≤ ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  apply integral_nonneg
  intro x
  simp only [Pi.zero_apply, ENNReal.toReal_nonneg, rpow_nonneg]

lemma integral_fun_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    {f : ℝ≥0∞ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_zero : ∀ x, f x = 0 ↔ x = 0 ∨ x = ⊤)
    (h_int : Integrable (f ∘ μ.rnDeriv ν) ν) :
    ∫ x, f (μ.rnDeriv ν x) ∂ν = 0 ↔ μ ⟂ₘ ν := by
  rw [← Measure.rnDeriv_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ ↦ hf_nonneg _) h_int]
  apply Filter.eventually_congr
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [Pi.zero_apply, hf_zero, hx, or_false]

lemma integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = 0 ↔ μ ⟂ₘ ν := by
  have h_nonneg : ∀ (x : ℝ≥0∞), 0 ≤ x.toReal ^ a := by
    intro x
    simp only [ENNReal.toReal_nonneg, rpow_nonneg]
  refine integral_fun_rnDeriv_eq_zero_iff_mutuallySingular h_nonneg (fun x ↦ ?_) h_int
  rw [rpow_eq_zero ENNReal.toReal_nonneg ha_zero, ENNReal.toReal_eq_zero_iff]

lemma integral_rpow_rnDeriv_pos_iff_not_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    0 < ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν ↔ ¬ μ ⟂ₘ ν := by
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero h_int]
  push Not
  exact ⟨fun h ↦ h.ne', fun h ↦ integral_rpow_rnDeriv_nonneg.lt_of_ne' h⟩

lemma integral_rpow_rnDeriv_smul_left [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0) :
    ∫ x, ((c • μ).rnDeriv ν x).toReal ^ a ∂ν = c ^ a * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_left' μ ν c] with x hx
  rw [← mul_rpow NNReal.zero_le_coe ENNReal.toReal_nonneg, hx, Pi.smul_apply, ENNReal.toReal_smul]
  rfl

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

lemma integral_rpow_rnDeriv_eq_integral_rpow_sub_one (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    [SigmaFinite μ] [SigmaFinite ν] (h_ac : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν = ∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ := by
  rw [integral_rpow_rnDeriv_symm ha_pos ha_ne]
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

lemma integral_rpow_rnDeriv_smul_left' [SigmaFinite μ] [SigmaFinite ν] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫ x, ((c • μ).rnDeriv ν x).toReal ^ a ∂ν
      = c.toReal ^ a * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  lift c to ℝ≥0 using hc
  rw [← ENNReal.smul_def, ENNReal.coe_toReal]
  exact integral_rpow_rnDeriv_smul_left c

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

/-- Slope of `a ↦ x ^ a` between `a` and `1` is bounded by `2 + x * |log x|`, for `a ∈ [1/2, 1)`. -/
lemma abs_mul_rpow_sub_le {x : ℝ} (hx : 0 ≤ x) (ha : 2⁻¹ ≤ a) (ha1 : a < 1) :
    |(a - 1)⁻¹ * (x ^ a - x)| ≤ 2 + x * |log x| := by
  rcases hx.eq_or_lt with rfl | hx_pos
  · rw [zero_rpow (by linarith), sub_zero, mul_zero, abs_zero, zero_mul, add_zero]
    norm_num
  obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope (fun t ↦ x ^ t) (fun t ↦ x ^ t * log x) ha1
    (continuous_iff_continuousAt.2 fun t ↦ Real.continuousAt_const_rpow hx_pos.ne').continuousOn
    (fun t _ ↦ (Real.hasStrictDerivAt_const_rpow hx_pos t).hasDerivAt)
  have h_eq : (a - 1)⁻¹ * (x ^ a - x) = x ^ c * log x := by
    rw [hc_eq, rpow_one]
    have : a - 1 ≠ 0 := sub_ne_zero.mpr ha1.ne
    have : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.ne'
    field_simp
    ring
  rw [h_eq, abs_mul, abs_of_nonneg (rpow_nonneg hx c)]
  have h0 : 0 ≤ x * |log x| := by positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · calc x ^ c * |log x| ≤ x * |log x| := by
          gcongr
          calc x ^ c ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1 hc.2.le
          _ = x := rpow_one x
      _ ≤ 2 + x * |log x| := by linarith
  · have h1 : x ^ c ≤ x ^ (2⁻¹ : ℝ) :=
      rpow_le_rpow_of_exponent_ge hx_pos hx1.le (by linarith [hc.1])
    have h2 : x ^ (2⁻¹ : ℝ) * |log x| < 2 := by
      have := abs_log_mul_self_lt (x ^ (2⁻¹ : ℝ)) (rpow_pos_of_pos hx_pos _)
        (rpow_le_one hx hx1.le (by norm_num))
      rw [log_rpow hx_pos, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹),
        abs_of_nonneg (rpow_nonneg hx _)] at this
      calc x ^ (2⁻¹ : ℝ) * |log x| = 2 * (2⁻¹ * |log x| * x ^ (2⁻¹ : ℝ)) := by ring
        _ < 2 * 1 := by gcongr
        _ = 2 := by ring
    calc x ^ c * |log x| ≤ x ^ (2⁻¹ : ℝ) * |log x| := by gcongr
      _ ≤ 2 := h2.le
      _ ≤ 2 + x * |log x| := by linarith

lemma tendsto_integral_rpow_rnDeriv_sub_div [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν - (μ .univ).toReal)) (𝓝[<] 1)
      (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  have h_int' : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * |log (μ.rnDeriv ν x).toReal|) ν := by
    have := (integrable_rnDeriv_smul_iff hμν).mpr h_int.abs
    simpa [llr_def, smul_eq_mul] using this
  have hL : ∫ x, llr μ ν x ∂μ = ∫ x, (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← integral_rnDeriv_smul hμν]
    simp [llr_def]
  rw [hL]
  have h_ev : ∀ᶠ a in 𝓝[<] (1:ℝ), a ∈ Set.Ico 2⁻¹ 1 := Ico_mem_nhdsLT (by norm_num)
  have h_eq : (fun a ↦ (a - 1)⁻¹ * (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν - (μ .univ).toReal))
      =ᶠ[𝓝[<] (1:ℝ)]
        fun a ↦ ∫ x, (a - 1)⁻¹ * ((μ.rnDeriv ν x).toReal ^ a - (μ.rnDeriv ν x).toReal) ∂ν := by
    filter_upwards [h_ev] with a ha
    rw [integral_const_mul,
      integral_sub (integrable_rpow_rnDeriv_of_lt_one (by linarith [ha.1]) ha.2)
      Measure.integrable_toReal_rnDeriv, Measure.integral_toReal_rnDeriv hμν, measureReal_def]
  refine Tendsto.congr' h_eq.symm ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ 2 + (μ.rnDeriv ν x).toReal * |log (μ.rnDeriv ν x).toReal|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a ↦ (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [h_ev] with a ha
    exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_mul_rpow_sub_le ENNReal.toReal_nonneg ha.1 ha.2
  · exact (integrable_const _).add h_int'
  · refine Eventually.of_forall fun x ↦ ?_
    rcases (ENNReal.toReal_nonneg (a := μ.rnDeriv ν x)).eq_or_lt with h0 | h_pos
    · rw [← h0]
      simp only [Real.log_zero, mul_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h_ev] with a ha
      rw [zero_rpow (by linarith [ha.1]), sub_zero, mul_zero]
    · have h := (Real.hasStrictDerivAt_const_rpow h_pos 1).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at h
      have h' := tendsto_nhdsWithin_mono_left
        (fun a (ha : a ∈ Set.Iio (1:ℝ)) ↦ Set.mem_compl_singleton_iff.2 (ne_of_lt ha)) h
      simp only [rpow_one] at h'
      refine h'.congr fun a ↦ ?_
      rw [slope_def_field, rpow_one, div_eq_inv_mul]

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

lemma tendsto_mul_log_integral_rpow_rnDeriv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)) (𝓝[<] 1)
      (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  simpa using tendsto_mul_log_integral_rpow_rnDeriv' hμν h_int

end MeasureTheory
