/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Convex combinations of probability measures

## Main statements

* `MeasureTheory.isProbabilityMeasure_smul_add_one_sub_smul`: for probability measures `μ` and `ν`
  and `t : ℝ≥0` with `t ≤ 1`, `t • μ + (1 - t) • ν` is a probability measure. Mathlib has the
  corresponding instance for `toNNReal p • μ + toNNReal (σ p) • ν` with `p : unitInterval`.
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- A convex combination `t • μ + (1 - t) • ν` of probability measures is a probability measure. -/
lemma isProbabilityMeasure_smul_add_one_sub_smul {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {t : ℝ≥0} (ht : t ≤ 1) :
    IsProbabilityMeasure (t • μ + (1 - t) • ν) where
  measure_univ := by simp [add_tsub_cancel_of_le (ENNReal.coe_le_one_iff.mpr ht)]

end MeasureTheory
