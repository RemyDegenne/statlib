/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Kernel.Posterior
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool

/-!
# Bayes risk of estimation problems with parameter space `Bool`

* `ProbabilityTheory.bayesRisk_boolKernel_eq_lintegral_iInf`: when it admits an argmin estimator,
  the Bayes risk of an estimation problem with parameter space `Bool` and data generating kernel
  `Kernel.boolKernel μ ν` is an integral of an infimum over the actions.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳}

/-- The Bayes risk for a prior `π` of an estimation problem with parameter space `Bool` and
data generating kernel `boolKernel μ ν`, when it admits an argmin estimator. -/
lemma bayesRisk_boolKernel_eq_lintegral_iInf {𝒴 : Type*} [MeasurableSpace 𝒴]
    {ℓ : Bool → 𝒴 → ℝ≥0∞} (hℓ : Measurable (Function.uncurry ℓ))
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (h : HasArgminEstimator ℓ (Kernel.boolKernel μ ν) π) :
    bayesRisk ℓ (Kernel.boolKernel μ ν) π
      = ∫⁻ x, ⨅ y, π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x * ℓ true y
        + π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x * ℓ false y
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [h.bayesRisk_eq hℓ]
  refine lintegral_congr_ae ?_
  filter_upwards [posterior_boolKernel_apply_false μ ν π, posterior_boolKernel_apply_true μ ν π]
    with x h_false h_true
  congr with y
  rw [lintegral_bool, h_false, h_true]
  ring

end ProbabilityTheory
