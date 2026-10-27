/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Complements on the real logarithm

* `Real.mul_log_div`: `a * log (a / b) = a * (log a - log b)` for `b ≠ 0`, including `a = 0`.
  Copied from LMLPapers (`LeanMachineLearning/ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean`).
* `Real.sub_le_mul_log_div`: `a - b ≤ a * log (a / b)` for `0 ≤ a` and `0 < b`.
-/

@[expose] public section

namespace Real

/-- `a * log (a / b) = a * (log a - log b)` for `b ≠ 0`, also when `a = 0` thanks to
`log 0 = 0`. -/
lemma mul_log_div {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * (log a - log b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]

/-- `a - b ≤ a * log (a / b)` for `0 ≤ a` and `0 < b`, a consequence of `1 - x⁻¹ ≤ log x`. -/
lemma sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * log (a / b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb.le
  calc a - b
  _ = a * (1 - (a / b)⁻¹) := by field_simp
  _ ≤ a * log (a / b) := by gcongr; exact one_sub_inv_le_log_of_pos (div_pos ha hb)

end Real
