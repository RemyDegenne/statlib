/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.ForMathlib.Probability.Moments.Variance
public import Statlib.Divergence.Renyi.Variational
public import Statlib.Testing.Binary
public import Statlib.Testing.ChangeMeasureRisk
public import Statlib.Testing.RenyiChangeMeasure

/-!
# Change of measure and the moments of the log-likelihood ratio

The change of measure inequality `measure_sub_le_measure_mul_exp` involves the probability that the
log-likelihood ratio `llr μ ν` exceeds a threshold. We choose thresholds adapted to the moments of
`llr μ ν`: its variance (through Chebyshev's inequality), its cumulant generating function (through
Rényi divergences) or its mean (the Kullback-Leibler divergence).

## Main statements

* `measureReal_sub_inv_le_measureReal_mul_exp_variance`: for probability measures and `β > 0`,
  `μ s - β⁻¹ ≤ ν s * exp (KL(μ, ν) + √(Var_μ[llr μ ν] * β))`.
* `one_sub_two_mul_inv_le_add_measureReal_mul_exp_variance`: for probability measures `μ, ν, ξ`
  and `β > 0`, the errors `μ s` and `ν sᶜ` of a test cannot both be small.
* `iInf_lintegral_sub_exp_le_bayesRisk_mul_exp_renyiDiv`: change of measure for Bayes risks, in
  which the probability of large values of the log-likelihood ratio is controlled through a Rényi
  divergence of order `1 + ε`.
* `min_sub_exp_le_bayesBinaryRisk_mul_exp_renyiDiv`: its specialization to the Bayes binary risk.
* `min_sub_le_bayesBinaryRisk_mul_exp_klDiv_add_renyiDiv`: change of measure for the Bayes binary
  risk, with the threshold centered at the mean `KL(π_γ × ξ, π ⊗ₘ P)` of the log-likelihood ratio,
  where `π_γ = (γ, 1 - γ)`, `ξ = renyiMeasure γ μ ν` is the tilted measure and `P = boolKernel μ ν`.
  That mean is `KL(π_γ, π) + (1 - γ) * R_γ(μ, ν)` (`klDiv_boolMeasure_prod_renyiMeasure`).
-/

@[expose] public section

open MeasureTheory InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α}

section Variance

open Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- The probability under `μ` that the log-likelihood ratio exceeds `KL(μ, ν) + √(Var[llr] * β)` is
at most `β⁻¹`. -/
lemma measureReal_llr_gt_klDiv_add_sqrt_le_inv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h : MemLp (llr μ ν) 2 μ) {β : ℝ} (hβ : 0 < β) :
    μ.real {x | (klDiv μ ν).toReal + √(variance (llr μ ν) μ * β) < llr μ ν x} ≤ β⁻¹ := by
  have h_kl : (klDiv μ ν).toReal = μ[llr μ ν] := toReal_klDiv_of_measure_eq hμν (by simp)
  have h_set : {x | (klDiv μ ν).toReal + √(variance (llr μ ν) μ * β) < llr μ ν x}
      = {x | √(variance (llr μ ν) μ * β) < llr μ ν x - μ[llr μ ν]} := by
    ext x
    simp only [h_kl, Set.mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  rw [h_set, measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (inv_nonneg.mpr hβ.le) ?_
  exact measure_sqrt_variance_mul_lt_sub_le h hβ

/-- **Change of measure inequality**, with a threshold given by the mean and the variance of the
log-likelihood ratio: `μ s - β⁻¹ ≤ ν s * exp (KL(μ, ν) + √(Var_μ[llr μ ν] * β))`. -/
lemma measureReal_sub_inv_le_measureReal_mul_exp_variance [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) (h : MemLp (llr μ ν) 2 μ) (s : Set α) {β : ℝ}
    (hβ : 0 < β) :
    μ.real s - β⁻¹ ≤ ν.real s * exp ((klDiv μ ν).toReal + √(variance (llr μ ν) μ * β)) := by
  refine le_trans ?_ (measureReal_sub_le_measureReal_mul_exp hμν s _ (measure_ne_top _ _))
  gcongr
  exact measureReal_llr_gt_klDiv_add_sqrt_le_inv hμν h hβ

/-- For probability measures `μ, ν, ξ` and any set `s`, the errors `μ s` and `ν sᶜ` of a test
cannot both be small: a lower bound in terms of the mean and the variance of the log-likelihood
ratios of `ξ` with respect to `μ` and `ν`. -/
lemma one_sub_two_mul_inv_le_add_measureReal_mul_exp_variance [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν)
    (hμ : MemLp (llr ξ μ) 2 ξ) (hν : MemLp (llr ξ ν) 2 ξ) (s : Set α) {β : ℝ} (hβ : 0 < β) :
    1 - 2 * β⁻¹
      ≤ μ.real s * exp ((klDiv ξ μ).toReal + √(variance (llr ξ μ) ξ * β))
        + ν.real sᶜ * exp ((klDiv ξ ν).toReal + √(variance (llr ξ ν) ξ * β)) := by
  refine le_trans ?_ (one_sub_le_add_measureReal_mul_exp hξμ hξν s _ _)
  have h1 := measureReal_llr_gt_klDiv_add_sqrt_le_inv hξμ hμ hβ
  have h2 := measureReal_llr_gt_klDiv_add_sqrt_le_inv hξν hν hβ
  linarith

end Variance

section Risk

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞}

/-- **Change of measure for the Bayes risk**, with the probability of large values of the
log-likelihood ratio controlled through a Rényi divergence of order `1 + ε`. For a loss bounded by
`1`, a probability measure `ξ` and `R = R_{1+ε}(ζ × ξ, π ⊗ₘ P)`,
`(⨅ y, ∫⁻ θ, ℓ θ y ∂ζ) - exp (-ε * c) ≤ R_π^P * exp (R + c)`. -/
lemma iInf_lintegral_sub_exp_le_bayesRisk_mul_exp_renyiDiv (hl : Measurable (Function.uncurry ℓ))
    (hl_le : ∀ θ y, ℓ θ y ≤ 1) {P : Kernel Θ 𝓧} [IsMarkovKernel P] {π ζ : Measure Θ}
    [IsProbabilityMeasure π] [IsProbabilityMeasure ζ] {ξ : Measure 𝓧} [IsProbabilityMeasure ξ]
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) (h : renyiDiv (1 + ε) (ζ.prod ξ) (π ⊗ₘ P) ≠ ∞) :
    (⨅ y, ∫⁻ θ, ℓ θ y ∂ζ) - ENNReal.ofReal (Real.exp (-ε * c))
      ≤ bayesRisk ℓ P π
        * ENNReal.ofReal (Real.exp ((renyiDiv (1 + ε) (ζ.prod ξ) (π ⊗ₘ P)).toReal + c)) := by
  refine le_trans ?_ (iInf_lintegral_sub_le_bayesRisk_mul_exp hl hl_le
    (absolutelyContinuous_of_renyiDiv_ne_top (by linarith) h) _)
  gcongr
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_llr_gt_renyiDiv_le_exp hε c h)

/-- **Change of measure for the Bayes binary risk**, with the probability of large values of the
log-likelihood ratio controlled through a Rényi divergence of order `1 + ε`: for a probability
measure `ξ` and `R = R_{1+ε}(ζ × ξ, π ⊗ₘ boolKernel μ ν)`,
`min ζ({false}) ζ({true}) - exp (-ε * c) ≤ B_π(μ, ν) * exp (R + c)`. -/
lemma min_sub_exp_le_bayesBinaryRisk_mul_exp_renyiDiv {μ ν : Measure 𝓧} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {π ζ : Measure Bool} [IsProbabilityMeasure π]
    [IsProbabilityMeasure ζ] {ξ : Measure 𝓧} [IsProbabilityMeasure ξ] {ε : ℝ} (hε : 0 < ε) (c : ℝ)
    (h : renyiDiv (1 + ε) (ζ.prod ξ) (π ⊗ₘ Kernel.boolKernel μ ν) ≠ ∞) :
    min (ζ {false}) (ζ {true}) - ENNReal.ofReal (Real.exp (-ε * c))
      ≤ bayesBinaryRisk μ ν π * ENNReal.ofReal
        (Real.exp ((renyiDiv (1 + ε) (ζ.prod ξ) (π ⊗ₘ Kernel.boolKernel μ ν)).toReal + c)) := by
  rw [← iInf_lintegral_zeroOneLoss_bool]
  exact iInf_lintegral_sub_exp_le_bayesRisk_mul_exp_renyiDiv measurable_zeroOneLoss
    zeroOneLoss_le_one hε c h

/-- **Change of measure for the Bayes binary risk**, with the threshold centered at the mean of the
log-likelihood ratio. Let `π_γ = (γ, 1 - γ)`, `ξ = renyiMeasure γ μ ν` be the tilted measure and
`P = boolKernel μ ν`. The mean of `llr (π_γ × ξ) (π ⊗ₘ P)` under `π_γ × ξ` is
`KL(π_γ × ξ, π ⊗ₘ P) = KL(π_γ, π) + (1 - γ) * R_γ(μ, ν)`, and
`min γ (1 - γ) - (π_γ × ξ) {llr > KL(π_γ × ξ, π ⊗ₘ P) + c}
  ≤ B_π(μ, ν) * exp (KL(π_γ, π) + (1 - γ) * R_γ(μ, ν) + c)`. -/
lemma min_sub_le_bayesBinaryRisk_mul_exp_klDiv_add_renyiDiv {μ ν : Measure 𝓧}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {π : Measure Bool} [IsFiniteMeasure π]
    (hπ_false : π {false} ≠ 0) (hπ_true : π {true} ≠ 0) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h_ms : ¬ μ ⟂ₘ ν) (c : ℝ) :
    min (ENNReal.ofReal γ) (ENNReal.ofReal (1 - γ))
        - (Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))).prod (renyiMeasure γ μ ν)
          {x | (klDiv ((Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))).prod
                (renyiMeasure γ μ ν)) (π ⊗ₘ Kernel.boolKernel μ ν)).toReal + c
            < llr ((Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))).prod (renyiMeasure γ μ ν))
              (π ⊗ₘ Kernel.boolKernel μ ν) x}
      ≤ bayesBinaryRisk μ ν π
        * ENNReal.ofReal (Real.exp
          ((klDiv (Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))) π
            + ENNReal.ofReal (1 - γ) * renyiDiv γ μ ν).toReal + c)) := by
  have := isProbabilityMeasure_renyiMeasure hγ0 hγ1 h_ms
  -- `π_γ × ξ ≪ π ⊗ₘ P` since `π` charges both points and `ξ ≪ μ`, `ξ ≪ ν`
  have h_ac : (Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))).prod (renyiMeasure γ μ ν)
      ≪ π ⊗ₘ Kernel.boolKernel μ ν := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd ?_ (ae_of_all _ fun b ↦ ?_)
    · refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
      suffices s = ∅ by simp [this]
      refine Set.eq_empty_of_forall_notMem fun b hb ↦ ?_
      cases b
      · exact hπ_false (measure_mono_null (Set.singleton_subset_iff.mpr hb) hs)
      · exact hπ_true (measure_mono_null (Set.singleton_subset_iff.mpr hb) hs)
    · cases b
      · exact renyiMeasure_absolutelyContinuous_left ν hγ0
      · exact renyiMeasure_absolutelyContinuous_right μ hγ1
  rw [← klDiv_boolMeasure_prod_renyiMeasure μ ν π hγ0 hγ1 h_ms]
  have h := iInf_lintegral_sub_le_bayesRisk_mul_exp measurable_zeroOneLoss
    zeroOneLoss_le_one h_ac
    ((klDiv ((Measure.boolMeasure (.ofReal γ) (.ofReal (1 - γ))).prod (renyiMeasure γ μ ν))
      (π ⊗ₘ Kernel.boolKernel μ ν)).toReal + c)
  rwa [iInf_lintegral_zeroOneLoss_bool, Measure.boolMeasure_apply_false,
    Measure.boolMeasure_apply_true] at h

end Risk

end ProbabilityTheory
