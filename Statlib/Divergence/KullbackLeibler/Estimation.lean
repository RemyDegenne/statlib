/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Statlib.Divergence.FDiv.Estimation
public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
public import Statlib.ForMathlib.Probability.Kernel.Basic
public import Statlib.Testing.Binary

/-!
# Lower bounds on the Bayes risk from the Kullback-Leibler divergence

We specialize the lower bound of `Statlib.Divergence.FDiv.Estimation` to the Kullback-Leibler
divergence: for a loss with values in `[0, 1]`, priors `π, ξ` and kernels `P, Q`,
`kl(R_π^Q, R_ξ^P) ≤ KL(π ⊗ₘ Q, ξ ⊗ₘ P)`, where `kl` is the binary Kullback-Leibler divergence
`klBerReal`. We then derive the corresponding bounds for simple binary hypothesis testing.

## Main statements

* `klDiv_bernoulliMeasure_bayesRisk_le`: the Kullback-Leibler divergence between the Bernoulli
  distributions with parameters `R_π^Q` and `R_ξ^P` is at most `KL(π ⊗ₘ Q, ξ ⊗ₘ P)`.
* `ofReal_klBerReal_bayesRisk_le_klDiv`: `kl(R_π^Q, R_ξ^P) ≤ KL(π ⊗ₘ Q, ξ ⊗ₘ P)`.
* `ofReal_klBerReal_bayesRisk_le_klDiv_add_klDiv`:
  `kl(R_π^Q, R_ξ^P) ≤ KL(π ⊗ₘ Q, π ⊗ₘ P) + KL(π, ξ)`.
* `ofReal_klBerReal_bayesBinaryRisk_le_klDiv`,
  `ofReal_klBerReal_bayesBinaryRisk_le_klDiv_add_klDiv`: the same bounds for simple binary
  hypothesis testing.
* `ofReal_klBerReal_bayesBinaryRisk_min_le_klDiv_compProd_prod_add`,
  `ofReal_klBerReal_min_bayesBinaryRisk_le_klDiv_prod_compProd_add`: comparison of a binary
  hypothesis testing problem with the trivial problem in which both hypotheses have the same law
  `ζ`. These are the main tools for the binary Fano inequality (a bound in terms of the
  Jensen-Shannon divergence) and for the lower bound on the Bayes binary risk in terms of the Rényi
  divergence, in `Statlib.Testing.Fano`.

## Implementation notes

The Bayes risks are real numbers in `[0, 1]` obtained with `ENNReal.toReal`. The binary
Kullback-Leibler divergence `klBerReal p q` is the right value only for `q ∈ (0, 1)`, but its
`ENNReal.ofReal` is always a lower bound of the Kullback-Leibler divergence between the Bernoulli
distributions (`ofReal_klBerReal_le_klDiv_bernoulliMeasure`), so no assumption is needed.
-/

@[expose] public section

open MeasureTheory Function InformationTheory unitInterval

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞}

section Estimation

variable (π ξ : Measure Θ) [IsProbabilityMeasure π] [IsProbabilityMeasure ξ]
  (P Q : Kernel Θ 𝓧) [IsMarkovKernel P] [IsMarkovKernel Q]

variable {π ξ P Q} in
/-- **Lower bound on the Kullback-Leibler divergence from the Bayes risks**, with Bernoulli
distributions: for a loss with values in `[0, 1]`, the Kullback-Leibler divergence between the
Bernoulli distributions with parameters the Bayes risks `R_π^Q` and `R_ξ^P` is at most
`KL(π ⊗ₘ Q, ξ ⊗ₘ P)`. -/
theorem klDiv_bernoulliMeasure_bayesRisk_le (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) {p q : I} (hp : ENNReal.ofReal p = bayesRisk ℓ Q π)
    (hq : ENNReal.ofReal q = bayesRisk ℓ P ξ) :
    klDiv Ber(true, false, p) Ber(true, false, q) ≤ klDiv (π ⊗ₘ Q) (ξ ⊗ₘ P) := by
  rw [klDiv_eq_fDiv, klDiv_eq_fDiv]
  exact fDiv_bernoulliMeasure_bayesRisk_le hℓ hℓ1 hp hq

/-- **Lower bound on the Kullback-Leibler divergence from the Bayes risks**: for a loss with values
in `[0, 1]`, `kl(R_π^Q, R_ξ^P) ≤ KL(π ⊗ₘ Q, ξ ⊗ₘ P)`, in which `kl` is the binary Kullback-Leibler
divergence. -/
theorem ofReal_klBerReal_bayesRisk_le_klDiv (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) :
    ENNReal.ofReal (klBerReal (bayesRisk ℓ Q π).toReal (bayesRisk ℓ P ξ).toReal)
      ≤ klDiv (π ⊗ₘ Q) (ξ ⊗ₘ P) := by
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · -- there is no estimator: both risks are `0` or both are `∞`
    have h_eq : bayesRisk ℓ Q π = bayesRisk ℓ P ξ := by
      rcases isEmpty_or_nonempty 𝓧 with h𝓧 | h𝓧 <;> simp
    simp [h_eq]
  have hQ : bayesRisk ℓ Q π ≤ 1 := bayesRisk_le_one hℓ1 Q π
  have hP : bayesRisk ℓ P ξ ≤ 1 := bayesRisk_le_one hℓ1 P ξ
  calc ENNReal.ofReal (klBerReal (bayesRisk ℓ Q π).toReal (bayesRisk ℓ P ξ).toReal)
  _ ≤ klDiv Ber(true, false, ⟨_, ENNReal.toReal_mem_unitInterval hQ⟩)
      Ber(true, false, ⟨_, ENNReal.toReal_mem_unitInterval hP⟩) :=
    ofReal_klBerReal_le_klDiv_bernoulliMeasure (by decide)
      ⟨_, ENNReal.toReal_mem_unitInterval hQ⟩ ⟨_, ENNReal.toReal_mem_unitInterval hP⟩
  _ ≤ klDiv (π ⊗ₘ Q) (ξ ⊗ₘ P) :=
    klDiv_bernoulliMeasure_bayesRisk_le hℓ hℓ1
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hQ))
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hP))

/-- **Lower bound on the Kullback-Leibler divergence from the Bayes risks**, with the same prior:
for a loss with values in `[0, 1]`, `kl(R_π^Q, R_ξ^P) ≤ KL(π ⊗ₘ Q, π ⊗ₘ P) + KL(π, ξ)`. -/
theorem ofReal_klBerReal_bayesRisk_le_klDiv_add_klDiv (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) :
    ENNReal.ofReal (klBerReal (bayesRisk ℓ Q π).toReal (bayesRisk ℓ P ξ).toReal)
      ≤ klDiv (π ⊗ₘ Q) (π ⊗ₘ P) + klDiv π ξ := by
  refine (ofReal_klBerReal_bayesRisk_le_klDiv π ξ P Q hℓ hℓ1).trans_eq ?_
  rw [klDiv_compProd_eq_add, add_comm]

end Estimation

section Binary

variable (μ ν μ' ν' : Measure 𝓧) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
  (π ξ : Measure Bool) [IsProbabilityMeasure π] [IsProbabilityMeasure ξ]

/-- **Lower bound on the Kullback-Leibler divergence from the Bayes binary risks**:
`kl(B_π(μ, ν), B_ξ(μ', ν')) ≤ KL(π ⊗ₘ boolKernel μ ν, ξ ⊗ₘ boolKernel μ' ν')`. -/
theorem ofReal_klBerReal_bayesBinaryRisk_le_klDiv :
    ENNReal.ofReal (klBerReal (bayesBinaryRisk μ ν π).toReal (bayesBinaryRisk μ' ν' ξ).toReal)
      ≤ klDiv (π ⊗ₘ Kernel.boolKernel μ ν) (ξ ⊗ₘ Kernel.boolKernel μ' ν') :=
  ofReal_klBerReal_bayesRisk_le_klDiv π ξ _ _ measurable_zeroOneLoss zeroOneLoss_le_one

/-- **Lower bound on the Kullback-Leibler divergence from the Bayes binary risks**, with the same
prior: `kl(B_π(μ, ν), B_ξ(μ', ν')) ≤ KL(π ⊗ₘ boolKernel μ ν, π ⊗ₘ boolKernel μ' ν') + KL(π, ξ)`. -/
theorem ofReal_klBerReal_bayesBinaryRisk_le_klDiv_add_klDiv :
    ENNReal.ofReal (klBerReal (bayesBinaryRisk μ ν π).toReal (bayesBinaryRisk μ' ν' ξ).toReal)
      ≤ klDiv (π ⊗ₘ Kernel.boolKernel μ ν) (π ⊗ₘ Kernel.boolKernel μ' ν') + klDiv π ξ := by
  refine (ofReal_klBerReal_bayesBinaryRisk_le_klDiv μ ν μ' ν' π ξ).trans_eq ?_
  rw [klDiv_compProd_eq_add, add_comm]

/-- Comparison of the binary hypothesis testing problem between `μ` and `ν` with the trivial problem
in which both hypotheses have law `ζ`:
`kl(B_π(μ, ν), min(ξ₀, ξ₁)) ≤ KL(π ⊗ₘ boolKernel μ ν, π × ζ) + KL(π, ξ)`.
This is the main tool in the proof of the binary Fano inequality. -/
theorem ofReal_klBerReal_bayesBinaryRisk_min_le_klDiv_compProd_prod_add (ζ : Measure 𝓧)
    [IsProbabilityMeasure ζ] :
    ENNReal.ofReal (klBerReal (bayesBinaryRisk μ ν π).toReal (min (ξ {false}) (ξ {true})).toReal)
      ≤ klDiv (π ⊗ₘ Kernel.boolKernel μ ν) (π.prod ζ) + klDiv π ξ := by
  have h := ofReal_klBerReal_bayesBinaryRisk_le_klDiv_add_klDiv μ ν ζ ζ π ξ
  rwa [bayesBinaryRisk_self, measure_univ, mul_one, Kernel.boolKernel_self,
    Measure.compProd_const] at h

/-- Comparison of the trivial binary hypothesis testing problem in which both hypotheses have law
`ζ` with the problem between `μ` and `ν`:
`kl(min(π₀, π₁), B_ξ(μ, ν)) ≤ KL(π × ζ, π ⊗ₘ boolKernel μ ν) + KL(π, ξ)`.
This is the main tool to bound the Bayes binary risk with the Rényi divergence. -/
theorem ofReal_klBerReal_min_bayesBinaryRisk_le_klDiv_prod_compProd_add (ζ : Measure 𝓧)
    [IsProbabilityMeasure ζ] :
    ENNReal.ofReal (klBerReal (min (π {false}) (π {true})).toReal (bayesBinaryRisk μ ν ξ).toReal)
      ≤ klDiv (π.prod ζ) (π ⊗ₘ Kernel.boolKernel μ ν) + klDiv π ξ := by
  have h := ofReal_klBerReal_bayesBinaryRisk_le_klDiv_add_klDiv ζ ζ μ ν π ξ
  rwa [bayesBinaryRisk_self, measure_univ, mul_one, Kernel.boolKernel_self,
    Measure.compProd_const] at h

end Binary

end ProbabilityTheory
