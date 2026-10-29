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
# Bayes risk of problems which admit an argmin estimator

## Main statements

* `ProbabilityTheory.HasArgminEstimator.bayesRisk_eq_lintegral_rnDeriv`: if the estimation problem
  admits an argmin estimator and `P θ ≪ P ∘ₘ π` for `π`-almost every `θ`, then the Bayes risk is
  `∫⁻ x, ⨅ y, ∫⁻ θ, (dP_θ/d(P ∘ₘ π))(x) * ℓ θ y ∂π ∂(P ∘ₘ π)`.
  `ProbabilityTheory.HasArgminEstimator.bayesRisk_eq_lintegral_rnDeriv_of_countable` is the same
  statement for a countable parameter space, without the absolute continuity assumption.
* `ProbabilityTheory.bayesRisk_boolKernel_eq_lintegral_iInf`: when it admits an argmin estimator,
  the Bayes risk of an estimation problem with parameter space `Bool` and data generating kernel
  `Kernel.boolKernel μ ν` is an integral of an infimum over the actions.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Function

open scoped ENNReal

namespace ProbabilityTheory

section Posterior

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞} [StandardBorelSpace Θ] [Nonempty Θ]
  {P : Kernel Θ 𝓧} [IsFiniteKernel P] {π : Measure Θ} [IsFiniteMeasure π]

/-- If the estimation problem admits an argmin estimator and `P θ ≪ P ∘ₘ π` for `π`-almost every
`θ`, then the Bayes risk is
`∫⁻ x, ⨅ y, ∫⁻ θ, (dP_θ/d(P ∘ₘ π))(x) * ℓ θ y ∂π ∂(P ∘ₘ π)`, in which the jointly measurable version
`P.rnDeriv (Kernel.const Θ (P ∘ₘ π))` of the Radon-Nikodym derivatives is used. -/
lemma HasArgminEstimator.bayesRisk_eq_lintegral_rnDeriv
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (hl : Measurable (uncurry ℓ)) (h : HasArgminEstimator ℓ P π)
    (h_ac : ∀ᵐ θ ∂π, P θ ≪ P ∘ₘ π) :
    bayesRisk ℓ P π
      = ∫⁻ x, ⨅ y, ∫⁻ θ, P.rnDeriv (Kernel.const Θ (P ∘ₘ π)) θ x * ℓ θ y ∂π ∂(P ∘ₘ π) := by
  rw [h.bayesRisk_eq hl]
  refine lintegral_congr_ae ?_
  filter_upwards [posterior_eq_withDensity h_ac] with x hx
  congr with y
  rw [hx, lintegral_withDensity_eq_lintegral_mul _ _ (by fun_prop)]
  · rfl
  · exact (Kernel.measurable_rnDeriv _ _).comp (measurable_id.prodMk measurable_const)

/-- If the parameter space is countable and the estimation problem admits an argmin estimator,
then the Bayes risk is `∫⁻ x, ⨅ y, ∫⁻ θ, (dP_θ/d(P ∘ₘ π))(x) * ℓ θ y ∂π ∂(P ∘ₘ π)`. -/
lemma HasArgminEstimator.bayesRisk_eq_lintegral_rnDeriv_of_countable [Countable Θ]
    (hl : Measurable (uncurry ℓ)) (h : HasArgminEstimator ℓ P π) :
    bayesRisk ℓ P π
      = ∫⁻ x, ⨅ y, ∫⁻ θ, (P θ).rnDeriv (P ∘ₘ π) x * ℓ θ y ∂π ∂(P ∘ₘ π) := by
  rw [h.bayesRisk_eq hl]
  refine lintegral_congr_ae ?_
  filter_upwards [posterior_eq_withDensity_of_countable P π] with x hx
  congr with y
  rw [hx, lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) (by fun_prop)]
  rfl

end Posterior

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The Bayes risk for a prior `π` of an estimation problem with parameter space `Bool` and
data generating kernel `boolKernel μ ν`, when it admits an argmin estimator. -/
lemma bayesRisk_boolKernel_eq_lintegral_iInf {𝓨 : Type*} [MeasurableSpace 𝓨]
    {ℓ : Bool → 𝓨 → ℝ≥0∞} (hℓ : Measurable (uncurry ℓ))
    (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
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
