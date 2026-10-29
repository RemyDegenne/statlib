/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# A one-sided Chebyshev bound

## Main statements

* `ProbabilityTheory.measure_sqrt_variance_mul_lt_sub_le`: the probability that `X` exceeds its
  mean by more than `√(Var[X] * β)` is at most `β⁻¹`. Mathlib has the two-sided bounds
  `meas_ge_le_variance_div_sq` and `meas_ge_le_evariance_div_sq`.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- **One-sided Chebyshev-type bound**: the probability that `X` exceeds its mean by more than
`√(Var[X] * β)` is at most `β⁻¹`. -/
lemma measure_sqrt_variance_mul_lt_sub_le [IsFiniteMeasure P] (hX : MemLp X 2 P) {β : ℝ}
    (hβ : 0 < β) :
    P {ω | √(variance X P * β) < X ω - P[X]} ≤ ENNReal.ofReal β⁻¹ := by
  rcases (variance_nonneg X P).eq_or_lt with h_var | h_var
  · -- if the variance is zero, `X` is a.e. equal to its mean
    have h_ae : X =ᵐ[P] fun _ ↦ P[X] := by
      rw [← evariance_eq_zero_iff hX.aestronglyMeasurable.aemeasurable, ← hX.ofReal_variance_eq,
        ← h_var, ENNReal.ofReal_zero]
    suffices P {ω | √(variance X P * β) < X ω - P[X]} = 0 by rw [this]; exact zero_le
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h_ae] with ω hω
    simp [hω, ← h_var]
  · have hc : 0 < √(variance X P * β) := sqrt_pos.mpr (mul_pos h_var hβ)
    calc P {ω | √(variance X P * β) < X ω - P[X]}
    _ ≤ P {ω | √(variance X P * β) ≤ |X ω - P[X]|} :=
      measure_mono fun ω (hω : _ < _) ↦ hω.le.trans (le_abs_self _)
    _ ≤ ENNReal.ofReal (variance X P / √(variance X P * β) ^ 2) := meas_ge_le_variance_div_sq hX hc
    _ = ENNReal.ofReal β⁻¹ := by
      rw [sq_sqrt (mul_pos h_var hβ).le, div_mul_eq_div_div, div_self h_var.ne', one_div]

end ProbabilityTheory
