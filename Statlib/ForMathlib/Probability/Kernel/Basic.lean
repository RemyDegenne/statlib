/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# The kernel `boolKernel μ μ`

## Main statements

* `ProbabilityTheory.Kernel.boolKernel_self`: `boolKernel μ μ` is the constant kernel with value
  `μ`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The kernel `boolKernel μ μ` is the constant kernel with value `μ`. -/
@[simp]
lemma boolKernel_self (μ : Measure α) : boolKernel μ μ = const Bool μ := by
  ext b : 1
  cases b <;> rfl

end ProbabilityTheory.Kernel
