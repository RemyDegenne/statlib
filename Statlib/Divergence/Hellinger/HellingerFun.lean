/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Notation
public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.IntegralRPowRNDeriv

/-!
# The real function of the Hellinger divergence

## Main definitions

* `hellingerFun a`: the real function `x ↦ (a - 1)⁻¹ * (x ^ a - 1 - a * (x - 1))`, with special
  cases at `a = 0` (indicator of `{0}`) and `a = 1` (`x * log x + 1 - x`, the function of the
  Kullback-Leibler divergence).

## Main statements

* `convexOn_hellingerFun`: `hellingerFun a` is convex on `[0, ∞)` for `0 ≤ a`.
* `derivAtTop_hellingerFun_of_one_le`, `derivAtTop_hellingerFun_of_lt_one`: the derivative at
  infinity is `⊤` for `1 ≤ a` and `a / (1 - a)` for `a < 1`.
* `integrable_hellingerFun_iff_integrable_rpow`: integrability of `hellingerFun a (∂μ/∂ν)` is
  equivalent to integrability of `(∂μ/∂ν) ^ a`.

## Implementation details

How to define a `DivFunction` from a real function `f`:
- prove that the function is convex on `(0, ∞)` and that `f 1 = 0`
- if applicable, prove that `f` is continuous at zero
- find the limit of `f` at +∞
- useful lemma: `f` is nonnegative
- useful lemma: `0 ≤ ∫ x, f (μ.rnDeriv ν x) ∂ν`. Simplify the integral to get other inequalities.

Then use `DivFunction.ofReal`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace InformationTheory Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

section HellingerFun

/-- Hellinger function, defined as `x ↦ (a - 1)⁻¹ * (x ^ a - 1)` for `a ∈ (0, 1) ∪ (1, + ∞)`.
At `0` the function is obtained by contiuity and is the indicator function of `{0}`. At `1` it is
defined as `x ↦ x * log x`, because in this way we obtain that the Hellinger divergence at `1`
conincides with the KL divergence, which is natural for continuity reasons. -/
noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ :=
  if a = 0 then fun x ↦ if x = 0 then 1 else 0
  else if a = 1 then fun x ↦ x * log x + 1 - x
  else fun x ↦ (a - 1)⁻¹ * (x ^ a - 1 - a * (x - 1))

@[simp]
lemma hellingerFun_zero : hellingerFun 0 = fun x ↦ if x = 0 then 1 else 0 := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_zero_eq_indicator : hellingerFun 0 = Set.indicator {0} 1 := by
  ext x
  by_cases h : x = 0 <;> simp [hellingerFun_zero, h]

@[simp]
lemma hellingerFun_one : hellingerFun 1 = fun x ↦ x * log x + 1 - x := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_of_ne_zero_of_ne_one (ha_zero : a ≠ 0) (ha_one : a ≠ 1) :
    hellingerFun a = fun x ↦ (a - 1)⁻¹ * (x ^ a - 1 - a * (x - 1)) := by
  ext x
  simp [hellingerFun, ha_zero, ha_one]

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) := by
  by_cases ha_eq : a = 1
  · rw [ha_eq, hellingerFun_one]
    fun_prop
  rw [hellingerFun, ite_eq_right ha_pos.ne', ite_eq_right ha_eq]
  refine continuous_const.mul ?_
  refine ((continuous_rpow_const ha_pos.le).sub continuous_const).sub ?_
  fun_prop

@[simp]
lemma hellingerFun_apply_one_eq_zero : hellingerFun a 1 = 0 := by
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  simp [hellingerFun, ha_one, ha_zero]

@[simp]
lemma hellingerFun_apply_zero : hellingerFun a 0 = 1 := by
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  simp only [hellingerFun, ha_zero, ↓reduceIte, ha_one, ne_eq, not_false_eq_true, zero_rpow,
    zero_sub, mul_neg, mul_one, sub_neg_eq_add]
  rw [add_comm, ← sub_eq_add_neg, inv_mul_cancel₀]
  rwa [sub_ne_zero]

lemma convexOn_hellingerFun (ha_pos : 0 ≤ a) : ConvexOn ℝ (Set.Ici 0) (hellingerFun a) := by
  by_cases ha_zero : a = 0
  · refine convexOn_iff_slope_mono_adjacent.mpr ?_
    simp only [convex_Ici, Set.mem_Ici, true_and, hellingerFun_zero, ha_zero]
    intro x y z hx _ hxy hyz
    simp only [(lt_of_le_of_lt hx hxy).ne', ↓reduceIte, zero_sub,
      (gt_trans hyz <| lt_of_le_of_lt hx hxy).ne', sub_self, zero_div, div_nonpos_iff,
      Left.nonneg_neg_iff, tsub_le_iff_right, zero_add, Left.neg_nonpos_iff, sub_nonneg]
    exact Or.inr ⟨by positivity, by linarith⟩
  replace ha_pos := ha_pos.lt_of_ne fun h ↦ ha_zero h.symm
  rcases (lt_trichotomy a 1) with (ha | ha | ha)
  · have : hellingerFun a = - (fun x ↦ (1 - a)⁻¹ • (x ^ a - 1 - a * (x - 1))) := by
      ext x
      rw [Pi.neg_apply, hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha.ne, smul_eq_mul, ← neg_mul,
        neg_inv, neg_sub]
    rw [this]
    refine (((Real.concaveOn_rpow ha_pos.le ha.le).sub
      (convexOn_const _ (convex_Ici 0))).sub ?_).smul (by simp [ha.le]) |>.neg
    exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul ha_pos.le
  · simp only [hellingerFun, ha, one_ne_zero, ↓reduceIte]
    exact convexOn_klFun
  · simp_rw [hellingerFun, ← smul_eq_mul, ite_eq_right ha_pos.ne', ite_eq_right ha.ne']
    refine ((convexOn_rpow ha.le).sub (concaveOn_const _ (convex_Ici 0))).sub ?_ |>.smul
      (by simp [ha.le])
    exact ((concaveOn_id (convex_Ici 0)).sub (convexOn_const _ (convex_Ici 0))).smul ha_pos.le

lemma hasDerivAt_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (hellingerFun a)
      (if a = 0 then 0
      else if a = 1 then log x
      else (a - 1)⁻¹ * a * (x ^ (a - 1) - 1)) x := by
  split_ifs with h1 h2
  · rw [h1, hellingerFun_zero]
    refine HasDerivAt.congr_of_eventuallyEq (f := fun _ ↦ 0) (hasDerivAt_const _ _) ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [hy]
  · simp only [h2, hellingerFun_one]
    exact hasDerivAt_klFun hx
  · rw [hellingerFun_of_ne_zero_of_ne_one h1 h2, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    rw [mul_sub]
    refine HasDerivAt.sub ?_ ?_
    · exact (Real.hasDerivAt_rpow_const (Or.inl hx)).sub_const _
    · exact ((hasDerivAt_id x).sub_const _).const_mul _

lemma rightDeriv_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    derivWithin (hellingerFun a) (Ioi x) x =
      if a = 0 then 0
      else if a = 1 then log x
      else (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) :=
  (hasDerivAt_hellingerFun a hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]
lemma rightDeriv_hellingerFun_one :
    derivWithin (hellingerFun a) (Ioi 1) 1 = 0 := by
  simp [rightDeriv_hellingerFun]

lemma hellingerFun_nonneg (ha : 0 ≤ a) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hellingerFun a x := by
  rcases hx.eq_or_lt with rfl | hx; · simp
  have h_cvx := (convexOn_hellingerFun ha).subset (Set.Ioi_subset_Ici le_rfl) (convex_Ioi _)
  have h_one : (1 : ℝ) ∈ interior (Set.Ioi 0) := by simp
  simpa [hellingerFun_apply_one_eq_zero] using
    h_cvx.isMinOn_of_rightDeriv_eq_zero h_one rightDeriv_hellingerFun_one hx

lemma tendsto_rightDeriv_hellingerFun_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (fun x ↦ derivWithin (hellingerFun a) (Ioi x) x) atTop atTop := by
  have : (fun x ↦ derivWithin (hellingerFun a) (Ioi x) x)
      =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) := by
    filter_upwards [eventually_ne_atTop 0] with x hx
    rw [rightDeriv_hellingerFun _ hx]
    simp [(zero_lt_one.trans ha).ne', ha.ne']
  rw [tendsto_congr' this]
  simp_rw [mul_assoc, tendsto_const_mul_atTop_iff]
  have h1 : ¬ a < 0 := by linarith
  have h2 : ¬ a < 1 := by linarith
  simp only [inv_pos, sub_pos, ha, zero_lt_one.trans ha, true_and, h1, false_and, or_false,
    inv_neg'', sub_neg, h2]
  refine tendsto_atTop_add_const_right atTop (-1) ?_
  exact tendsto_rpow_atTop (by linarith)

lemma tendsto_rightDeriv_hellingerFun_atTop_of_lt_one (ha : a < 1) :
    Tendsto (fun x ↦ derivWithin (hellingerFun a) (Ioi x) x) atTop (𝓝 (a * (1 - a)⁻¹)) := by
  by_cases ha_zero : a = 0
  · simp only [ha_zero, sub_zero, inv_one, mul_one]
    have : (fun x ↦ derivWithin (hellingerFun 0) (Ioi x) x) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_hellingerFun _ hx]
      simp
    rw [tendsto_congr' this]
    exact tendsto_const_nhds
  · have : (fun x ↦ derivWithin (hellingerFun a) (Ioi x) x)
        =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_hellingerFun _ hx]
      simp [ha_zero, ha.ne]
    rw [tendsto_congr' this]
    have h_eq : (fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1))
        = (fun x ↦ a * (1 - x ^ (a - 1)) * (1 - a)⁻¹) := by
      ext x
      rw [mul_assoc, mul_comm, mul_assoc, mul_assoc]
      congr 1
      rw [← neg_sub 1 a, inv_neg, mul_neg, neg_sub, ← neg_mul, neg_sub]
    rw [h_eq]
    refine Tendsto.mul_const _ ?_
    simp_rw [mul_sub, mul_one]
    suffices Tendsto (fun k ↦ a - a * k ^ (a - 1)) atTop (𝓝 (a - a * 0)) by
      simpa using this
    refine Tendsto.const_sub _ ?_
    refine Tendsto.const_mul _ ?_
    have : (fun (x : ℝ) ↦ x ^ (a - 1)) = (fun x ↦ x ^ (-(1 - a))) := by ext x; simp
    rw [this]
    exact tendsto_rpow_neg_atTop (by linarith)

lemma derivAtTop_hellingerFun_of_one_lt (ha : 1 < a) : derivAtTop (hellingerFun a) = ⊤ :=
  ((convexOn_hellingerFun (zero_le_one.trans ha.le)).subset Ioi_subset_Ici_self
    (convex_Ioi 0)).derivAtTop_eq_top_of_tendsto_rightDeriv
    (tendsto_rightDeriv_hellingerFun_atTop_of_one_lt ha)

lemma derivAtTop_hellingerFun_of_one_le (ha : 1 ≤ a) : derivAtTop (hellingerFun a) = ⊤ := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [hellingerFun_one]
    exact convexOn_Ioi_klFun.derivAtTop_eq_top_of_tendsto_rightDeriv tendsto_rightDeriv_klFun_atTop
  · exact derivAtTop_hellingerFun_of_one_lt ha

/-- For `a < 1`, the derivative at infinity of `hellingerFun a` is `a / (1 - a)`. The function is
not convex for `a < 0`, so we compute the limit of `hellingerFun a x / x` directly. -/
lemma derivAtTop_hellingerFun_of_lt_one (ha : a < 1) :
    derivAtTop (hellingerFun a) = (a * (1 - a)⁻¹ : ℝ) := by
  refine derivAtTop_of_tendsto (EReal.tendsto_coe.mpr ?_)
  by_cases ha_zero : a = 0
  · simp only [ha_zero, zero_mul]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [hx.ne']
  -- for `x > 0`, `hellingerFun a x / x = (a - 1)⁻¹ * (x ^ (a - 1) + (a - 1) * x⁻¹ - a)`
  have h_eq : (fun x ↦ (a - 1)⁻¹ * (x ^ (a - 1) + (a - 1) * x⁻¹ - a))
      =ᶠ[atTop] fun x ↦ hellingerFun a x / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [hellingerFun_of_ne_zero_of_ne_one ha_zero ha.ne, rpow_sub_one hx.ne']
    field_simp
    ring
  have h_lim : Tendsto (fun x : ℝ ↦ (a - 1)⁻¹ * (x ^ (a - 1) + (a - 1) * x⁻¹ - a)) atTop
      (𝓝 ((a - 1)⁻¹ * (0 + (a - 1) * 0 - a))) := by
    refine ((Tendsto.add ?_ (tendsto_inv_atTop_zero.const_mul _)).sub_const _).const_mul _
    rw [show a - 1 = -(1 - a) by ring]
    exact tendsto_rpow_neg_atTop (by linarith)
  convert h_lim.congr' h_eq using 2
  rw [← neg_sub 1 a, inv_neg]
  ring

lemma integrable_hellingerFun_iff_integrable_rpow (ha_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, hellingerFun_zero_eq_indicator, rpow_zero, integrable_const, iff_true,
      ← Set.indicator_comp_right fun x ↦ ((∂μ/∂ν) x).toReal, Set.preimage, Set.mem_singleton_iff,
      Pi.one_comp]
    refine (integrable_indicator_iff ?_).mpr ?_
    · apply measurableSet_eq_fun <;> fun_prop
    · exact integrableOn_const (measure_ne_top ν _)
  rw [hellingerFun_of_ne_zero_of_ne_one ha_zero ha_one, integrable_const_mul_iff]
  swap; · simp [sub_eq_zero, ha_one]
  simp_rw [sub_eq_add_neg, add_assoc, ← sub_eq_add_neg]
  rw [integrable_add_iff_integrable_left']
  refine (integrable_const _).add (((Integrable.sub ?_ (integrable_const _)).const_mul _).neg)
  exact Measure.integrable_toReal_rnDeriv

lemma integrable_hellingerFun_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [integrable_hellingerFun_iff_integrable_rpow ha.ne]
  exact integrable_rpow_rnDeriv_of_lt_one ha_nonneg ha

lemma integral_hellingerFun_of_pos_of_ne_one_of_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
  calc ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
  _ = (a - 1)⁻¹ * ∫ x, ((μ.rnDeriv ν x).toReal ^ a - 1 - a * ((μ.rnDeriv ν x).toReal - 1)) ∂ν := by
    rw [← integral_const_mul]
    simp_rw [hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha_ne]
  _ = (a - 1)⁻¹ * ∫ x, ((μ.rnDeriv ν x).toReal ^ a + (a - 1) - a * (μ.rnDeriv ν x).toReal) ∂ν := by
    congr with x
    ring
  _ = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
      + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    rw [integral_sub, integral_add, integral_const, smul_eq_mul, mul_comm _ (a - 1),
      integral_const_mul, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀, one_mul,
      sub_eq_add_neg]
    · congr
      rw [mul_assoc, ← neg_mul, neg_inv, neg_sub, ← mul_assoc]
    · rwa [sub_ne_zero]
    · exact h_int
    · exact integrable_const _
    · exact h_int.add (integrable_const _)
    · exact Measure.integrable_toReal_rnDeriv.const_mul _

lemma integral_hellingerFun_of_pos_of_ne_one_of_integrable_of_ac
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν)
    (hμν : μ ≪ ν) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  rw [integral_hellingerFun_of_pos_of_ne_one_of_integrable ha_pos ha_ne h_int,
    Measure.integral_toReal_rnDeriv hμν, measureReal_def]

lemma integral_hellingerFun_of_pos_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν :=
  integral_hellingerFun_of_pos_of_ne_one_of_integrable ha_pos ha_lt.ne
    (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)

end HellingerFun

end ProbabilityTheory
