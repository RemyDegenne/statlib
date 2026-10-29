/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.KullbackLeibler.CondKL
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Statlib.ForMathlib.Probability.Kernel.Composition.Lemmas

/-!
# Mutual information

We define the mutual information `mutualInfo ρ = klDiv ρ (ρ.fst.prod ρ.snd)` of a measure `ρ` on a
product space and prove its basic properties.

## Main definitions

* `mutualInfo ρ`: the mutual information between the two components of a measure `ρ` on `α × β`,
  the Kullback-Leibler divergence between `ρ` and the product of its marginals.
* `condMutualInfo κ ν`: the conditional mutual information
  `KL(ν ⊗ κ, ν ⊗ (κ.fst ×ₖ κ.snd))` of a kernel `κ : γ ⇝ α × β` with respect to a measure `ν`.

## Main statements

* `mutualInfo_compProd`: `I(μ ⊗ κ) = KL(μ ⊗ κ, μ × (κ ∘ μ))`.
* `condMutualInfo_eq_condKL`: `I(κ | ν) = KL(κ, κ.fst ×ₖ κ.snd | ν)`.
* `condMutualInfo_eq_lintegral`: `I(κ | ν) = ∫⁻ z, I(κ z) ∂ν`, if `γ` is countable or `α × β` is
  countably generated and `ν` is finite.
* `mutualInfo_compProd_eq_condKL`: `I(μ ⊗ κ) = KL(κ, κ ∘ μ | μ)`.
* `mutualInfo_map_swap`: the mutual information is symmetric.
* `mutualInfo_parallelComp_comp_le`: **data-processing inequality**,
  `I((κ ∥ η) ∘ ρ) ≤ I(ρ)` for Markov kernels `κ, η`.
* `mutualInfo_compProd_comp_le`: for random variables `X → Y → Z`, `I(X, Z) ≤ I(X, Y)`.
* `klDiv_compProd_prod_eq_mutualInfo_add`: **compensation identity**, for a probability measure
  `μ` and a finite measure `ξ`, `KL(μ ⊗ κ, μ × ξ) = I(μ ⊗ κ) + KL(κ ∘ μ, ξ)`.
-/

@[expose] public section

open MeasureTheory InformationTheory ProbabilityTheory MeasurableSpace

open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

namespace ProbabilityTheory

/-- The mutual information between the two components of a joint measure. -/
noncomputable def mutualInfo (μ : Measure (α × β)) : ℝ≥0∞ :=
  klDiv μ (μ.fst.prod μ.snd)

/-- The mutual information of `μ ⊗ₘ κ` for a Markov kernel `κ` is the Kullback-Leibler divergence
between `μ ⊗ₘ κ` and the product of `μ` and `κ ∘ₘ μ`. -/
lemma mutualInfo_compProd {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) := by
  rw [mutualInfo, Measure.fst_compProd, Measure.snd_compProd]

/-- The conditional mutual information of a kernel `κ : γ ⇝ α × β` with respect to a measure `ν`
on `γ`, defined as `klDiv (ν ⊗ₘ κ) (ν ⊗ₘ (κ.fst ×ₖ κ.snd))`. In terms of random variables,
`I(X; Y | Z) = KL(P_{Z,X,Y}, P_Z ⊗ (P_{X|Z} × P_{Y|Z}))`. It is the conditional Kullback-Leibler
divergence between `κ` and the product of its marginals (`condMutualInfo_eq_condKL`).

If `γ` is countable or `α × β` is countably generated, `ν` is finite and `κ` is finite, it is equal
to `∫⁻ z, mutualInfo (κ z) ∂ν` (`condMutualInfo_eq_lintegral`). -/
noncomputable
def condMutualInfo (κ : Kernel γ (α × β)) (ν : Measure γ) : ℝ≥0∞ :=
  klDiv (ν ⊗ₘ κ) (ν ⊗ₘ (κ.fst ×ₖ κ.snd))

/-- The conditional mutual information of `κ` is the conditional Kullback-Leibler divergence
between `κ` and the product of its marginals. -/
lemma condMutualInfo_eq_condKL (κ : Kernel γ (α × β)) (ν : Measure γ) :
    condMutualInfo κ ν = condKL κ (κ.fst ×ₖ κ.snd) ν := rfl

/-- The conditional mutual information is the integral of the mutual information of the measures
`κ z`. -/
lemma condMutualInfo_eq_lintegral [CountableOrCountablyGenerated γ (α × β)]
    (κ : Kernel γ (α × β)) [IsFiniteKernel κ] (ν : Measure γ) [IsFiniteMeasure ν] :
    condMutualInfo κ ν = ∫⁻ z, mutualInfo (κ z) ∂ν := by
  simp_rw [condMutualInfo_eq_condKL, condKL_eq_lintegral, mutualInfo, Kernel.prod_apply,
    Kernel.fst_apply, Kernel.snd_apply, Measure.fst, Measure.snd]

/-- The mutual information of `μ ⊗ₘ κ` is the conditional Kullback-Leibler divergence between `κ`
and the constant kernel with value `κ ∘ₘ μ`. -/
lemma mutualInfo_compProd_eq_condKL {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) = condKL κ (Kernel.const α (κ ∘ₘ μ)) μ := by
  rw [mutualInfo_compProd, ← Measure.compProd_const, ← condKL]

/-- The mutual information is symmetric. -/
lemma mutualInfo_map_swap (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    mutualInfo (ρ.map Prod.swap) = mutualInfo ρ := by
  rw [mutualInfo, mutualInfo, Measure.fst_map_swap, Measure.snd_map_swap, ← Measure.prod_swap,
    klDiv_map_swap]

/-- **Data-processing inequality** for the mutual information: processing each component of a
pair of random variables by a Markov kernel cannot increase their mutual information. -/
theorem mutualInfo_parallelComp_comp_le (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (κ : Kernel α γ) [IsMarkovKernel κ] (η : Kernel β δ) [IsMarkovKernel η] :
    mutualInfo ((κ ∥ₖ η) ∘ₘ ρ) ≤ mutualInfo ρ := by
  rw [mutualInfo, mutualInfo, Measure.fst_parallelComp_comp, Measure.snd_parallelComp_comp,
    Measure.prod_comp_comp]
  exact klDiv_comp_right_le _ _ _

/-- If three random variables have the dependency structure `X → Y → Z`, with `μ` the law of `X`,
`μ ⊗ₘ κ` the law of `(X, Y)` and `μ ⊗ₘ (η ∘ₖ κ)` the law of `(X, Z)`, then
`I(X, Z) ≤ I(X, Y)`. -/
lemma mutualInfo_compProd_comp_le (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (η : Kernel β γ) [IsMarkovKernel η] :
    mutualInfo (μ ⊗ₘ (η ∘ₖ κ)) ≤ mutualInfo (μ ⊗ₘ κ) := by
  rw [← Measure.parallelComp_comp_compProd]
  exact mutualInfo_parallelComp_comp_le _ _ _

/-- **Compensation identity**: for a probability measure `μ`, a Markov kernel `κ` and a finite
measure `ξ`, `KL(μ ⊗ κ, μ × ξ) = I(μ ⊗ κ) + KL(κ ∘ μ, ξ)`. -/
lemma klDiv_compProd_prod_eq_mutualInfo_add (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (ξ : Measure β) [IsFiniteMeasure ξ] :
    klDiv (μ ⊗ₘ κ) (μ.prod ξ) = mutualInfo (μ ⊗ₘ κ) + klDiv (κ ∘ₘ μ) ξ := by
  rw [klDiv_prod_eq_klDiv_snd_add, Measure.snd_compProd, mutualInfo_compProd, add_comm]

end ProbabilityTheory
