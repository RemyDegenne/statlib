/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Differences of real-valued measures of sets

## Main statements

* `MeasureTheory.ofReal_measureReal_sub_measureReal`: for sets of finite measure,
  `ENNReal.ofReal (μ.real s - ν.real t) = μ s - ν t`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

/-- The difference of the measures of two sets of finite measure, as the image of the difference
of their real-valued measures. -/
lemma ofReal_measureReal_sub_measureReal (hs : μ s ≠ ∞ := by finiteness)
    (ht : ν t ≠ ∞ := by finiteness) :
    ENNReal.ofReal (μ.real s - ν.real t) = μ s - ν t := by
  rw [ENNReal.ofReal_sub _ measureReal_nonneg, ofReal_measureReal hs, ofReal_measureReal ht]

end MeasureTheory
