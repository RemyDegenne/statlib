/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.JensenShannon.Variational
public import Statlib.Divergence.MutualInformation.LeftRight
public import Statlib.Divergence.Renyi.Variational

/-!
# Mutual informations for a prior on `Bool`

Let `π` be a probability measure on `Bool` and `κ : Bool ⇝ 𝓧` be a Markov kernel, and write
`π₀ = π {false}`. The Kullback-Leibler mutual informations of `π` and `κ` are divergences
between `κ false` and `κ true`:
* the mutual information `I(π ⊗ₘ κ)` and the right Kullback-Leibler mutual information
  `I^R_KL(π, κ)` are the Jensen-Shannon divergence `JS_{π₀}(κ false, κ true)`;
* if `π₀ ≠ 0`, the left Kullback-Leibler mutual information `I^L_KL(π, κ)` is
  `(1 - π₀) * R_{π₀}(κ false, κ true)`, where `R` is the Rényi divergence.

## Main statements

* `mutualInfo_compProd_boolKernel`: with `πₐ = boolMeasure α (1 - α)`,
  `I(πₐ ⊗ₘ boolKernel μ ν) = JS_α(μ, ν)`.
* `mutualInfo_compProd_bool`: `I(π ⊗ₘ κ) = JS_{π₀}(κ false, κ true)`.
* `mutualInfoRight_klDivFun_bool`: `I^R_KL(π, κ) = JS_{π₀}(κ false, κ true)`.
* `mutualInfoLeft_klDivFun_bool`: for `π₀ ≠ 0`, `I^L_KL(π, κ) = π {true} * R_{π₀}(κ false, κ true)`.

## Implementation notes

The same identities for the prior `πₐ = boolMeasure α (1 - α)` and the kernel `boolKernel μ ν`,
with the left and right mutual informations unfolded, are `jensenShannon_eq_iInf_klDiv_compProd`
and `mul_renyiDiv_eq_iInf_klDiv_prod`.
-/

@[expose] public section

open MeasureTheory InformationTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

section JensenShannon

variable {α : ℝ≥0}

/-- The prior on `Bool` with mass `α` at `false` and `1 - α` at `true`. -/
local notation "πₐ" => Measure.boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞)

/-- The mutual information of `πₐ ⊗ₘ boolKernel μ ν` is the Jensen-Shannon divergence
`JS_α(μ, ν)`. -/
theorem mutualInfo_compProd_boolKernel (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    mutualInfo (πₐ ⊗ₘ Kernel.boolKernel μ ν) = jensenShannon α μ ν := by
  rw [mutualInfo_compProd, jensenShannon_eq_klDiv_compProd]

end JensenShannon

/-- The mutual information of `π ⊗ₘ κ` for a probability measure `π` on `Bool` and a Markov
kernel `κ : Bool ⇝ 𝓧` is the Jensen-Shannon divergence `JS_{π {false}}(κ false, κ true)`. -/
theorem mutualInfo_compProd_bool (π : Measure Bool) [IsProbabilityMeasure π]
    (κ : Kernel Bool 𝓧) [IsMarkovKernel κ] :
    mutualInfo (π ⊗ₘ κ) = jensenShannon (π {false}).toNNReal (κ false) (κ true) := by
  conv_lhs => rw [Measure.eq_boolMeasure_toNNReal π, Kernel.eq_boolKernel κ]
  exact mutualInfo_compProd_boolKernel _ _

/-- The right Kullback-Leibler mutual information of a probability measure `π` on `Bool` and a
Markov kernel `κ : Bool ⇝ 𝓧` is the Jensen-Shannon divergence
`JS_{π {false}}(κ false, κ true)`. -/
theorem mutualInfoRight_klDivFun_bool (π : Measure Bool) [IsProbabilityMeasure π]
    (κ : Kernel Bool 𝓧) [IsMarkovKernel κ] :
    mutualInfoRight klDivFun π κ = jensenShannon (π {false}).toNNReal (κ false) (κ true) := by
  rw [mutualInfoRight_klDivFun, mutualInfo_compProd_bool]

/-- The left Kullback-Leibler mutual information of a probability measure `π` on `Bool` with
`π {false} ≠ 0` and a Markov kernel `κ : Bool ⇝ 𝓧` is `(1 - π₀) * R_{π₀}(κ false, κ true)`,
where `π₀ = π {false}` and `R` is the Rényi divergence. -/
theorem mutualInfoLeft_klDivFun_bool (π : Measure Bool) [IsProbabilityMeasure π]
    (h0 : π {false} ≠ 0) (κ : Kernel Bool 𝓧) [IsMarkovKernel κ] :
    mutualInfoLeft klDivFun π κ = π {true} * renyiDiv (π {false}).toReal (κ false) (κ true) := by
  have h_true : π {true} = 1 - π {false} := Measure.prob_true_eq_one_sub π
  rcases eq_or_ne (π {false}) 1 with h1 | h1
  · -- `π` is the Dirac mass at `false`: both sides vanish
    have h_true0 : π {true} = 0 := by simp [h_true, h1]
    have h := klDiv_prod_compProd_boolKernel π (κ false) (κ true) (κ false)
    rw [← Kernel.eq_boolKernel κ] at h
    refine le_antisymm ((mutualInfoLeft_le _ π κ (κ false)).trans_eq ?_) (by simp [h_true0])
    simp [← klDiv_eq_fDiv, h, h_true0]
  have ha0 : 0 < (π {false}).toReal := ENNReal.toReal_pos h0 (measure_ne_top π _)
  have ha1 : (π {false}).toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top (lt_of_le_of_ne prob_le_one h1)
  have h_one_sub : ENNReal.ofReal (1 - (π {false}).toReal) = π {true} := by
    rw [h_true, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top π _)]
  have hπ : π = Measure.boolMeasure (ENNReal.ofReal (π {false}).toReal)
      (ENNReal.ofReal (1 - (π {false}).toReal)) := by
    rw [ENNReal.ofReal_toReal (measure_ne_top π _), h_one_sub]
    exact Measure.eq_boolMeasure π
  have h := mul_renyiDiv_eq_iInf_klDiv_prod (μ := κ false) (ν := κ true) ha0 ha1
  rw [← hπ, ← Kernel.eq_boolKernel κ, h_one_sub] at h
  rw [mutualInfoLeft_klDivFun_eq_iInf]
  exact h.symm

end ProbabilityTheory
