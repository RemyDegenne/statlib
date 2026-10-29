/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Log-convexity of the integrals of powers

## Main statements

* `ENNReal.lintegral_rpow_le_rpow_mul_rpow`: the function `a ↦ ∫⁻ x, f x ^ a ∂μ` is log-convex on
  `[0, ∞)`, a consequence of Hölder's inequality.
-/

@[expose] public section

open MeasureTheory

namespace ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Log-convexity of `a ↦ ∫⁻ x, f x ^ a ∂μ` on `[0, ∞)`, a consequence of Hölder's inequality. -/
lemma lintegral_rpow_le_rpow_mul_rpow {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫⁻ x, f x ^ (θ * a + (1 - θ) * b) ∂μ
      ≤ (∫⁻ x, f x ^ a ∂μ) ^ θ * (∫⁻ x, f x ^ b ∂μ) ^ (1 - θ) := by
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have h_eq : ∀ x, f x ^ (θ * a + (1 - θ) * b) = (f x ^ a) ^ θ * (f x ^ b) ^ (1 - θ) := by
    intro x
    rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hθ0 ha) (mul_nonneg hθ1' hb),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm θ a, mul_comm (1 - θ) b]
  simp_rw [h_eq]
  exact ENNReal.lintegral_mul_norm_pow_le (hf.pow_const a) (hf.pow_const b) hθ0 hθ1'
    (by ring)

end ENNReal
