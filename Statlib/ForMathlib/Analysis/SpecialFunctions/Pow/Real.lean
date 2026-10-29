/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary bounds on real powers

## Main statements

* `Real.rpow_le_one_add_rpow`: `t ^ a ≤ 1 + t ^ c` for `t ≥ 0` and `0 ≤ a ≤ c`.
* `Real.abs_mul_log_le_one_add_rpow`: `|t * log t| ≤ 1 + t ^ b / (b - 1)` for `t ≥ 0` and `b > 1`.
-/

@[expose] public section

namespace Real

variable {a b : ℝ}

/-- For `t ≥ 0` and `0 ≤ a ≤ c`, `t ^ a ≤ 1 + t ^ c`. -/
lemma rpow_le_one_add_rpow {t c : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hac : a ≤ c) :
    t ^ a ≤ 1 + t ^ c := by
  rcases le_total t 1 with ht1 | ht1
  · linarith [rpow_le_one ht ht1 ha, rpow_nonneg ht c]
  · linarith [rpow_le_rpow_of_exponent_le ht1 hac]

/-- For `t ≥ 0` and `b > 1`, `|t * log t| ≤ 1 + t ^ b / (b - 1)`. -/
lemma abs_mul_log_le_one_add_rpow {t : ℝ} (ht : 0 ≤ t) (hb : 1 < b) :
    |t * log t| ≤ 1 + t ^ b / (b - 1) := by
  have hb1 : 0 < b - 1 := by linarith
  have h_nonneg : 0 ≤ t ^ b / (b - 1) := by positivity
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases ht.eq_or_lt with rfl | ht0
    · simpa using h_nonneg.trans (le_add_of_nonneg_left zero_le_one)
    · have h := abs_log_mul_self_lt t ht0 ht1
      rw [mul_comm] at h
      linarith
  · have hlog : 0 ≤ log t := log_nonneg ht1.le
    rw [abs_of_nonneg (mul_nonneg ht hlog)]
    have h1 : log t ≤ t ^ (b - 1) / (b - 1) := log_le_rpow_div ht hb1
    have h2 : t * t ^ (b - 1) = t ^ b := by
      rw [← rpow_one_add' ht (by linarith)]
      congr 1
      ring
    calc t * log t ≤ t * (t ^ (b - 1) / (b - 1)) := by gcongr
      _ = t ^ b / (b - 1) := by rw [← h2]; ring
      _ ≤ 1 + t ^ b / (b - 1) := by linarith

end Real
