/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Posterior

/-!
# Bayes' formula for the posterior of a singleton

## Main statements

* `ProbabilityTheory.posterior_singleton_ae_eq`: for a countable parameter space,
  `(P†π) x {z} = π {z} * (dP_z/d(P ∘ₘ π))(x)` for `(P ∘ₘ π)`-almost every `x`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [StandardBorelSpace Θ]
  [Nonempty Θ]

/-- **Bayes' formula** for the posterior probability of a parameter, for a countable parameter
space. -/
lemma posterior_singleton_ae_eq [Countable Θ] (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ)
    [IsFiniteMeasure π] :
    ∀ᵐ x ∂(P ∘ₘ π), ∀ z, (P†π) x {z} = π {z} * (P z).rnDeriv (P ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable P π] with x hx z
  rw [hx, withDensity_apply _ (measurableSet_singleton z), lintegral_singleton, mul_comm]

end ProbabilityTheory
