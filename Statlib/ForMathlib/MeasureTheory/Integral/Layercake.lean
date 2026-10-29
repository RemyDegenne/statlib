/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Tail-sum formula for random variables with values in `ℕ`

A discrete version of the layer cake formula: for a random variable `σ` with values in `ℕ`,
`∑ n, P {n ≤ σ} = ∫ (σ + 1) ∂P`.

## Main statements

* `sum_Iic_eq_tsum_indicator`: a sum up to a random time `τ` is the series of the terms restricted
  to the events `{n ≤ τ}`.
* `MeasureTheory.tsum_measure_le_eq_lintegral`: **tail-sum formula**,
  `∑ n, P {n ≤ σ} = ∫⁻ (σ + 1) ∂P` for a random variable `σ` with values in `ℕ`.
* `MeasureTheory.hasSum_measureReal_le`: **tail-sum formula**, `∑ n, P {n ≤ σ} = ∫ (σ + 1) ∂P` for
  an integrable random variable `σ` with values in `ℕ`.
-/

@[expose] public section

open scoped ENNReal

/-- A sum up to a random time `τ` is the series of the terms restricted to the events
`{n ≤ τ}`. -/
lemma sum_Iic_eq_tsum_indicator {Ω M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (X : ℕ → Ω → M) (τ : Ω → ℕ) (ω : Ω) :
    ∑ n ∈ Finset.Iic (τ ω), X n ω = ∑' n, {ω | n ≤ τ ω}.indicator (X n) ω := by
  rw [tsum_eq_sum (s := Finset.Iic (τ ω))]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Set.indicator_of_mem]
    simpa using hn
  · intro n hn
    rw [Set.indicator_of_notMem]
    simpa using hn

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- For an integrable random variable `σ` with values in `ℕ`, the expectation of `σ + 1` computed in
`ℝ` and in `ℝ≥0∞` agree. -/
lemma ofReal_integral_natCast_add_one_eq_lintegral [IsFiniteMeasure P] {σ : Ω → ℕ}
    (hσ_int : Integrable (fun ω ↦ (σ ω : ℝ)) P) :
    ENNReal.ofReal (∫ ω, (σ ω + 1 : ℝ) ∂P) = ∫⁻ ω, (σ ω + 1 : ℝ≥0∞) ∂P := by
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun ω ↦ (σ ω + 1 : ℝ))
    (hσ_int.add (integrable_const _)) (ae_of_all _ fun ω ↦ by positivity)]
  congr with ω
  rw [ENNReal.ofReal_add (by positivity) zero_le_one]
  simp

/-- **Tail-sum formula** for a random variable `σ` with values in `ℕ`:
`∑ n, P {n ≤ σ} = ∫⁻ (σ + 1) ∂P`. -/
lemma tsum_measure_le_eq_lintegral {σ : Ω → ℕ} (hσ : AEMeasurable σ P) :
    ∑' n, P {ω | n ≤ σ ω} = ∫⁻ ω, (σ ω + 1 : ℝ≥0∞) ∂P := by
  have h_meas (n : ℕ) : NullMeasurableSet {ω | n ≤ σ ω} P :=
    nullMeasurableSet_le aemeasurable_const hσ
  have h_pt (ω : Ω) : ∑' n, {ω | n ≤ σ ω}.indicator (1 : Ω → ℝ≥0∞) ω = σ ω + 1 := by
    rw [← sum_Iic_eq_tsum_indicator (fun _ ↦ 1)]
    simp
  rw [← funext h_pt, lintegral_tsum fun n ↦ measurable_one.aemeasurable.indicator₀ (h_meas n)]
  congr with n
  rw [lintegral_indicator_one₀ (h_meas n)]

/-- **Tail-sum formula** for an integrable random variable `σ` with values in `ℕ`:
`∑ n, P {n ≤ σ} = ∫ (σ + 1) ∂P`. -/
lemma hasSum_measureReal_le [IsFiniteMeasure P] {σ : Ω → ℕ}
    (hσ_int : Integrable (fun ω ↦ (σ ω : ℝ)) P) :
    HasSum (fun n ↦ P.real {ω | n ≤ σ ω}) (∫ ω, (σ ω + 1 : ℝ) ∂P) := by
  -- `σ = ⌊σ⌋₊` is a.e.-measurable since its cast to `ℝ` is integrable
  have hσ : AEMeasurable σ P := by
    simpa [Function.comp_def] using Nat.measurable_floor.comp_aemeasurable hσ_int.aemeasurable
  have h_lint : ∑' n, P {ω | n ≤ σ ω} = ENNReal.ofReal (∫ ω, (σ ω + 1 : ℝ) ∂P) := by
    rw [tsum_measure_le_eq_lintegral hσ, ofReal_integral_natCast_add_one_eq_lintegral hσ_int]
  have h := ENNReal.hasSum_toReal (f := fun n ↦ P {ω | n ≤ σ ω})
    (by rw [h_lint]; exact ENNReal.ofReal_ne_top)
  rwa [← ENNReal.tsum_toReal_eq (fun n ↦ measure_ne_top _ _), h_lint,
    ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ by positivity)] at h

end MeasureTheory
