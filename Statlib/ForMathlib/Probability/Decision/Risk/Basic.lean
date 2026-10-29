/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.Risk.Basic

/-!
# Additional properties of the average and Bayes risks

## Main statements

* `bayesRisk_smul_prior`: the Bayes risk is positively homogeneous in the prior.
* `bayesRisk_le_bayesRisk_fst`, `bayesRisk_le_bayesRisk_snd`: forgetting a component of the
  observation increases the Bayes risk.
* `mul_bayesRisk_add_mul_bayesRisk_le`: **concavity of the Bayes risk** in the data generating
  kernel.
* `avgRisk_eq_lintegral_compProd`: the average risk is the integral of the expected loss of the
  estimator against the joint law `π ⊗ₘ P` of the parameter and the data.
* `avgRisk_le_one`, `bayesRisk_le_one`: the risks of a loss bounded by `1` are at most `1`.
* `bayesRisk_const_eq_bayesRisk_discard`: observing data with a law that does not depend on the
  parameter is as good as observing nothing.
-/

@[expose] public section

open MeasureTheory Function

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞}

/-! ### Scaling the prior -/

@[simp]
lemma avgRisk_smul_prior (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
    (c : ℝ≥0∞) :
    avgRisk ℓ P κ (c • π) = c * avgRisk ℓ P κ π := by
  simp [avgRisk, lintegral_smul_measure]

/-- The Bayes risk is positively homogeneous in the prior: scaling the prior by a finite factor
scales the Bayes risk by the same factor. -/
lemma bayesRisk_smul_prior [Nonempty 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    bayesRisk ℓ P (c • π) = c * bayesRisk ℓ P π := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  simp_rw [bayesRisk, avgRisk_smul_prior, ENNReal.mul_iInf_of_ne hc0 hc]

/-! ### Processing the observation -/

/-- Forgetting the second component of the observation increases the Bayes risk. -/
lemma bayesRisk_le_bayesRisk_fst (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ (𝓧 × 𝓧')) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ P.fst π := by
  rw [Kernel.fst_eq]
  exact bayesRisk_le_bayesRisk_map _ _ _ measurable_fst

/-- Forgetting the first component of the observation increases the Bayes risk. -/
lemma bayesRisk_le_bayesRisk_snd (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ (𝓧 × 𝓧')) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ P.snd π := by
  rw [Kernel.snd_eq]
  exact bayesRisk_le_bayesRisk_map _ _ _ measurable_snd

/-- The Bayes risk of a constant kernel with value a probability measure is the Bayes risk without
observations. -/
lemma bayesRisk_const_eq_bayesRisk_discard (ℓ : Θ → 𝓨 → ℝ≥0∞) (ξ : Measure 𝓧)
    [IsProbabilityMeasure ξ] (π : Measure Θ) :
    bayesRisk ℓ (Kernel.const Θ ξ) π = bayesRisk ℓ (Kernel.discard Θ) π := by
  -- in both problems, the laws of the estimates are exactly the probability measures on `𝓨`
  refine le_antisymm (le_iInf₂ fun κ hκ ↦ ?_) (le_iInf₂ fun κ hκ ↦ ?_)
  · refine iInf₂_le_of_le (Kernel.const 𝓧 (κ PUnit.unit)) inferInstance (le_of_eq ?_)
    simp [avgRisk, Kernel.discard_eq_const, Measure.dirac_bind κ.measurable]
  · refine iInf₂_le_of_le (Kernel.const _ (κ ∘ₘ ξ)) inferInstance (le_of_eq ?_)
    simp [avgRisk, Kernel.discard_eq_const]

/-! ### Concavity in the data generating kernel -/

/-- If `P θ = a • P₁ θ + b • P₂ θ` for `π`-almost every `θ`, then
`a * avgRisk ℓ P₁ κ π + b * avgRisk ℓ P₂ κ π ≤ avgRisk ℓ P κ π`. -/
lemma mul_avgRisk_add_mul_avgRisk_le (ℓ : Θ → 𝓨 → ℝ≥0∞) {P₁ P₂ P : Kernel Θ 𝓧} {a b : ℝ≥0∞}
    {π : Measure Θ} (hP : ∀ᵐ θ ∂π, P θ = a • P₁ θ + b • P₂ θ) (κ : Kernel 𝓧 𝓨) :
    a * avgRisk ℓ P₁ κ π + b * avgRisk ℓ P₂ κ π ≤ avgRisk ℓ P κ π := by
  calc a * avgRisk ℓ P₁ κ π + b * avgRisk ℓ P₂ κ π
  _ ≤ ∫⁻ θ, a * ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P₁) θ) + b * ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P₂) θ) ∂π :=
    (add_le_add (lintegral_const_mul_le _ _) (lintegral_const_mul_le _ _)).trans
      (le_lintegral_add _ _)
  _ = avgRisk ℓ P κ π := by
    refine lintegral_congr_ae ?_
    filter_upwards [hP] with θ hθ
    simp_rw [Kernel.comp_apply, hθ, Measure.comp_add, Measure.comp_smul, lintegral_add_measure,
      lintegral_smul_measure, smul_eq_mul]

/-- **Concavity of the Bayes risk** in the data generating kernel: if `P θ = a • P₁ θ + b • P₂ θ`
for `π`-almost every `θ`, then `a * bayesRisk ℓ P₁ π + b * bayesRisk ℓ P₂ π ≤ bayesRisk ℓ P π`. -/
lemma mul_bayesRisk_add_mul_bayesRisk_le (ℓ : Θ → 𝓨 → ℝ≥0∞) {P₁ P₂ P : Kernel Θ 𝓧}
    {a b : ℝ≥0∞} {π : Measure Θ} (hP : ∀ᵐ θ ∂π, P θ = a • P₁ θ + b • P₂ θ) :
    a * bayesRisk ℓ P₁ π + b * bayesRisk ℓ P₂ π ≤ bayesRisk ℓ P π := by
  refine le_iInf₂ fun κ hκ ↦ le_trans ?_ (mul_avgRisk_add_mul_avgRisk_le ℓ hP κ)
  gcongr <;> exact bayesRisk_le_avgRisk _ _ _ _

/-! ### The average risk as an integral against the joint law -/

/-- The expected loss `∫⁻ y, ℓ θ y ∂(κ x)` of an estimator `κ` is a measurable function of the
parameter-data pair `(θ, x)`. -/
lemma measurable_lintegral_loss (hℓ : Measurable (uncurry ℓ)) (κ : Kernel 𝓧 𝓨)
    [IsSFiniteKernel κ] :
    Measurable fun z : Θ × 𝓧 ↦ ∫⁻ y, ℓ z.1 y ∂(κ z.2) := by
  have h := (hℓ.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
    (κ := κ.comap Prod.snd measurable_snd)
  simpa [Kernel.comap_apply] using h

/-- The average risk is the integral of the expected loss of the estimator with respect to the
joint law `π ⊗ₘ P` of the parameter and the data. -/
lemma avgRisk_eq_lintegral_compProd (hℓ : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ P κ π = ∫⁻ z, ∫⁻ y, ℓ z.1 y ∂(κ z.2) ∂(π ⊗ₘ P) := by
  rw [avgRisk, Measure.lintegral_compProd (measurable_lintegral_loss hℓ κ)]
  congr with θ
  rw [Kernel.lintegral_comp _ _ _ (show Measurable (ℓ θ) from hℓ.comp measurable_prodMk_left)]

/-! ### Losses bounded by `1` -/

/-- For a loss bounded by `1`, a prior and kernels that are either zero or of mass `1` (for example
a probability prior and Markov kernels), the average risk is at most `1`. -/
lemma avgRisk_le_one (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) (P : Kernel Θ 𝓧) [IsZeroOrMarkovKernel P]
    (κ : Kernel 𝓧 𝓨) [IsZeroOrMarkovKernel κ] (π : Measure Θ) [IsZeroOrProbabilityMeasure π] :
    avgRisk ℓ P κ π ≤ 1 := by
  refine (avgRisk_le_mul' P κ π (C := 1) (by simpa using hℓ1)).trans ?_
  calc ((1 : ℝ≥0) : ℝ≥0∞) * κ.bound * P.bound * π Set.univ ≤ 1 * 1 * 1 * 1 := by
        gcongr
        exacts [le_of_eq ENNReal.coe_one, κ.bound_le_one, P.bound_le_one, prob_le_one]
  _ = 1 := by simp

/-- For a loss bounded by `1`, a prior and a kernel that are either zero or of mass `1` (for
example a probability prior and a Markov kernel), the Bayes risk is at most `1`. -/
lemma bayesRisk_le_one [Nonempty 𝓨] (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) (P : Kernel Θ 𝓧)
    [IsZeroOrMarkovKernel P] (π : Measure Θ) [IsZeroOrProbabilityMeasure π] :
    bayesRisk ℓ P π ≤ 1 := by
  refine (bayesRisk_le_mul' P π (C := 1) (by simpa using hℓ1)).trans ?_
  calc ((1 : ℝ≥0) : ℝ≥0∞) * P.bound * π Set.univ ≤ 1 * 1 * 1 := by
        gcongr
        exacts [le_of_eq ENNReal.coe_one, P.bound_le_one, prob_le_one]
  _ = 1 := by simp

end ProbabilityTheory
