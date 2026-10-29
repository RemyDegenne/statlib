/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Secant slopes of `s ↦ t ^ s` at `1`

We study the secant slopes `(t ^ a - t) / (a - 1)` at `1` of the function `s ↦ t ^ s`, whose
derivative at `1` is `t * log t`. For `t > 0` that function is convex (`convexOn_rpow_left`), so its
slopes are monotone; for `t = 0` they are monotone on `[0, ∞)`.

## Main statements

* `Real.rpow_sub_self_div_sub_one_le`: the slopes are monotone in `a ≥ 0`.
* `Real.tendsto_rpow_sub_self_div_sub_one`: the slopes tend to `t * log t` as `a → 1`.
* `Real.neg_inv_two_le_rpow_sub_self_div_sub_one`, `Real.neg_inv_two_le_mul_log`: lower bounds by
  `-1/2`.
* `Real.mul_log_le_rpow_sub_self_div_sub_one`, `Real.rpow_sub_self_div_sub_one_le_mul_log`: the
  derivative `t * log t` lies between the slopes for `a < 1` and those for `a > 1`.
-/

@[expose] public section

open Filter Set

open scoped Topology

namespace Real

variable {a b : ℝ}

/-- The secant slopes `(t ^ a - t) / (a - 1)` of `s ↦ t ^ s` at `1` are monotone in `a ≥ 0`. -/
lemma rpow_sub_self_div_sub_one_le {t : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≤ b) :
    (t ^ a - t) / (a - 1) ≤ (t ^ b - t) / (b - 1) := by
  rcases ht.eq_or_lt with rfl | ht
  · rcases ha.eq_or_lt with rfl | ha
    · rcases hab.eq_or_lt with rfl | hb
      · exact le_rfl
      · simp [zero_rpow hb.ne']
    · simp [zero_rpow ha.ne', zero_rpow (ha.trans_le hab).ne']
  have h := (convexOn_rpow_left ht).secant_mono (mem_univ 1) (mem_univ a) (mem_univ b) ha1 hb1 hab
  simpa only [rpow_one] using h

/-- The secant slopes `(t ^ a - t) / (a - 1)` of `s ↦ t ^ s` tend to `t * log t` as `a → 1`. -/
lemma tendsto_rpow_sub_self_div_sub_one (t : ℝ) :
    Tendsto (fun a ↦ (t ^ a - t) / (a - 1)) (𝓝[≠] 1) (𝓝 (t * log t)) := by
  have h : HasDerivAt (fun a : ℝ ↦ t ^ a) (t * log t) 1 := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · simpa using (hasStrictDerivAt_const_rpow_of_neg (x := 1) ht).hasDerivAt
    · rw [zero_mul]
      refine (hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (f := fun _ ↦ 0) ?_
      filter_upwards [eventually_ne_nhds one_ne_zero] with a ha
      simp [zero_rpow ha]
    · simpa using (hasStrictDerivAt_const_rpow ht 1).hasDerivAt
  refine h.tendsto_slope.congr fun a ↦ ?_
  rw [slope_def_field, rpow_one]

/-- The secant slopes `(t ^ a - t) / (a - 1)` of `s ↦ t ^ s` at `1` are bounded below by `-1 / 2`
for `a ≥ 1 / 2`. -/
lemma neg_inv_two_le_rpow_sub_self_div_sub_one {t : ℝ} (ht : 0 ≤ t) (ha : 2⁻¹ ≤ a)
    (ha1 : a ≠ 1) :
    -2⁻¹ ≤ (t ^ a - t) / (a - 1) := by
  refine le_trans ?_ (rpow_sub_self_div_sub_one_le ht (by norm_num) (by norm_num) ha1 ha)
  have h_sqrt : t ^ (2⁻¹ : ℝ) = √t := by rw [sqrt_eq_rpow]; norm_num
  have hs := sq_sqrt ht
  rw [h_sqrt, show (2⁻¹ : ℝ) - 1 = -2⁻¹ by norm_num, div_neg, div_inv_eq_mul]
  nlinarith [sq_nonneg (√t - 2⁻¹)]

/-- For `a > 1`, the secant slope `(t ^ a - t) / (a - 1)` of `s ↦ t ^ s` at `1` is at least its
derivative `t * log t` at `1`. -/
lemma mul_log_le_rpow_sub_self_div_sub_one {t : ℝ} (ht : 0 ≤ t) (ha : 1 < a) :
    t * log t ≤ (t ^ a - t) / (a - 1) := by
  refine le_of_tendsto ((tendsto_rpow_sub_self_div_sub_one t).mono_left
    (nhdsWithin_mono _ fun x hx ↦ ne_of_lt (Set.mem_Iio.mp hx))) ?_
  filter_upwards [Ioo_mem_nhdsLT (show (2⁻¹ : ℝ) < 1 by norm_num)] with b hb
  exact rpow_sub_self_div_sub_one_le ht (by linarith [hb.1]) hb.2.ne ha.ne'
    (hb.2.le.trans ha.le)

/-- For `a < 1`, the secant slope `(t ^ a - t) / (a - 1)` of `s ↦ t ^ s` at `1` is at most its
derivative `t * log t` at `1`. -/
lemma rpow_sub_self_div_sub_one_le_mul_log {t : ℝ} (ht : 0 ≤ t) (ha : a < 1) :
    (t ^ a - t) / (a - 1) ≤ t * log t := by
  rcases ht.eq_or_lt with rfl | ht
  · rcases eq_or_ne a 0 with rfl | ha0
    · norm_num
    · simp [zero_rpow ha0]
  refine ge_of_tendsto ((tendsto_rpow_sub_self_div_sub_one t).mono_left
    (nhdsWithin_mono _ fun x hx ↦ ne_of_gt (Set.mem_Ioi.mp hx))) ?_
  filter_upwards [self_mem_nhdsWithin] with b (hb : 1 < b)
  simpa only [rpow_one] using (convexOn_rpow_left ht).secant_mono (mem_univ 1) (mem_univ a)
    (mem_univ b) ha.ne hb.ne' (ha.trans hb).le

/-- For `t ≥ 0`, `-1 / 2 ≤ t * log t` (the optimal lower bound is `-exp (-1)`). -/
lemma neg_inv_two_le_mul_log {t : ℝ} (ht : 0 ≤ t) : -2⁻¹ ≤ t * log t :=
  (neg_inv_two_le_rpow_sub_self_div_sub_one ht le_rfl (by norm_num)).trans
    (rpow_sub_self_div_sub_one_le_mul_log ht (by norm_num))

end Real
