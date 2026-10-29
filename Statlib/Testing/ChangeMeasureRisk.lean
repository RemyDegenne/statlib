/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.ForMathlib.Probability.Decision.Risk.Basic
public import Statlib.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import Statlib.Testing.ChangeMeasure

/-!
# Change of measure for risks

We deduce from the change of measure inequality for functions with values in `[0, 1]`
(`lintegral_sub_le_lintegral_mul_exp`) change of measure inequalities for Bayes risks of
estimation problems with a loss bounded by `1`.

## Main statements

* `bayesRisk_sub_le_bayesRisk_mul_exp`: for a loss bounded by `1` and `ζ ⊗ₘ Q ≪ π ⊗ₘ P`,
  `R_ζ^Q - (ζ ⊗ₘ Q) {llr (ζ ⊗ₘ Q) (π ⊗ₘ P) > c} ≤ R_π^P * exp c`.
* `iInf_lintegral_sub_le_bayesRisk_mul_exp`: the same inequality with `Q` the constant kernel with
  value a probability measure `ξ`. The Bayes risk of a constant kernel does not depend on its value,
  and is `⨅ y, ∫⁻ θ, ℓ θ y ∂ζ`.
* `iInf_lintegral_sub_iInf_le_bayesRisk_mul_exp`: the previous inequality, optimized over `ξ`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

section Risk

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞}

/-- **Change of measure for the Bayes risk**. For a loss bounded by `1` and `ζ ⊗ₘ Q ≪ π ⊗ₘ P`,
`R_ζ^Q - (ζ ⊗ₘ Q) {llr (ζ ⊗ₘ Q) (π ⊗ₘ P) > c} ≤ R_π^P * exp c`. -/
lemma bayesRisk_sub_le_bayesRisk_mul_exp (hl : Measurable (Function.uncurry ℓ))
    (hl_le : ∀ θ y, ℓ θ y ≤ 1) {P Q : Kernel Θ 𝓧} [IsFiniteKernel P] [IsFiniteKernel Q]
    {π ζ : Measure Θ} [SigmaFinite π] [SigmaFinite ζ] (h_ac : ζ ⊗ₘ Q ≪ π ⊗ₘ P) (c : ℝ) :
    bayesRisk ℓ Q ζ - (ζ ⊗ₘ Q) {p | c < llr (ζ ⊗ₘ Q) (π ⊗ₘ P) p}
      ≤ bayesRisk ℓ P π * ENNReal.ofReal (Real.exp c) := by
  have h_exp_ne_zero : ENNReal.ofReal (Real.exp c) ≠ 0 := by simp [Real.exp_pos]
  rw [← ENNReal.div_le_iff h_exp_ne_zero ENNReal.ofReal_ne_top]
  refine le_iInf₂ fun κ hκ ↦ ?_
  rw [ENNReal.div_le_iff h_exp_ne_zero ENNReal.ofReal_ne_top]
  have h_le_one (p : Θ × 𝓧) : ∫⁻ y, ℓ p.1 y ∂(κ p.2) ≤ 1 :=
    (lintegral_mono fun y ↦ hl_le _ y).trans (by simp)
  calc bayesRisk ℓ Q ζ - (ζ ⊗ₘ Q) {p | c < llr (ζ ⊗ₘ Q) (π ⊗ₘ P) p}
  _ ≤ avgRisk ℓ Q κ ζ - (ζ ⊗ₘ Q) {p | c < llr (ζ ⊗ₘ Q) (π ⊗ₘ P) p} := by
    gcongr
    exact bayesRisk_le_avgRisk ℓ Q κ ζ
  _ ≤ avgRisk ℓ P κ π * ENNReal.ofReal (Real.exp c) := by
    rw [avgRisk_eq_lintegral_compProd hl, avgRisk_eq_lintegral_compProd hl]
    exact lintegral_sub_le_lintegral_mul_exp h_ac (ae_of_all _ h_le_one) c

/-- **Change of measure for the Bayes risk** of a constant kernel. For a loss bounded by `1` and a
probability measure `ξ` with `ζ × ξ ≪ π ⊗ₘ P`,
`(⨅ y, ∫⁻ θ, ℓ θ y ∂ζ) - (ζ × ξ) {llr (ζ × ξ) (π ⊗ₘ P) > c} ≤ R_π^P * exp c`.
The first term is the Bayes risk with respect to `ζ` of the constant kernel with value `ξ`. -/
lemma iInf_lintegral_sub_le_bayesRisk_mul_exp (hl : Measurable (Function.uncurry ℓ))
    (hl_le : ∀ θ y, ℓ θ y ≤ 1) {P : Kernel Θ 𝓧} [IsFiniteKernel P] {π ζ : Measure Θ}
    [SigmaFinite π] [SigmaFinite ζ] {ξ : Measure 𝓧} [IsProbabilityMeasure ξ]
    (h_ac : ζ.prod ξ ≪ π ⊗ₘ P) (c : ℝ) :
    (⨅ y, ∫⁻ θ, ℓ θ y ∂ζ) - ζ.prod ξ {p | c < llr (ζ.prod ξ) (π ⊗ₘ P) p}
      ≤ bayesRisk ℓ P π * ENNReal.ofReal (Real.exp c) := by
  have h := bayesRisk_sub_le_bayesRisk_mul_exp hl hl_le (P := P) (π := π)
    (Q := Kernel.const Θ ξ) (ζ := ζ) (by rwa [Measure.compProd_const]) c
  rwa [Measure.compProd_const, bayesRisk_const hl] at h

/-- **Change of measure for the Bayes risk**, optimized over constant kernels. For a loss bounded by
`1`, `(⨅ y, ∫⁻ θ, ℓ θ y ∂ζ) - ⨅ ξ, (ζ × ξ) {llr (ζ × ξ) (π ⊗ₘ P) > c} ≤ R_π^P * exp c`, where the
infimum is over the probability measures `ξ` with `ζ × ξ ≪ π ⊗ₘ P`. The first term is the Bayes
risk with respect to `ζ` of any constant kernel. -/
lemma iInf_lintegral_sub_iInf_le_bayesRisk_mul_exp (hl : Measurable (Function.uncurry ℓ))
    (hl_le : ∀ θ y, ℓ θ y ≤ 1) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π ζ : Measure Θ)
    [SigmaFinite π] [SigmaFinite ζ] (c : ℝ) :
    (⨅ y, ∫⁻ θ, ℓ θ y ∂ζ)
        - ⨅ (ξ : Measure 𝓧) (_ : IsProbabilityMeasure ξ) (_ : ζ.prod ξ ≪ π ⊗ₘ P),
          ζ.prod ξ {p | c < llr (ζ.prod ξ) (π ⊗ₘ P) p}
      ≤ bayesRisk ℓ P π * ENNReal.ofReal (Real.exp c) := by
  simp_rw [ENNReal.sub_iInf]
  exact iSup_le fun ξ ↦ iSup_le fun _ ↦ iSup_le fun h_ac ↦
    iInf_lintegral_sub_le_bayesRisk_mul_exp hl hl_le h_ac c

end Risk

end ProbabilityTheory
