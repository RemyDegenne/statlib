/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.JensenShannon.Basic
public import Statlib.Divergence.KullbackLeibler.CondKL
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool
public import Statlib.ForMathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Variational formulas for the Jensen-Shannon divergence

Let `πₐ = boolMeasure α (1 - α)` be the prior on `Bool` with mass `α` at `false`, and
`P = boolKernel μ ν` the kernel with `P false = μ` and `P true = ν`, so that
`P ∘ₘ πₐ = α • μ + (1 - α) • ν`. For finite measures `μ`, `ν` and `ξ`, the compensation identity
`α * KL(μ, ξ) + (1 - α) * KL(ν, ξ) = JS_α(μ, ν) + KL(α • μ + (1 - α) • ν, ξ)`
holds. It follows that for probability measures `μ` and `ν`, `JS_α(μ, ν)` is the infimum over
probability measures `ξ` of `α * KL(μ, ξ) + (1 - α) * KL(ν, ξ)`, attained at
`ξ = α • μ + (1 - α) • ν`.

## Main statements

* `jensenShannon_eq_klDiv_compProd`: `JS_α(μ, ν) = KL(πₐ ⊗ₘ P, πₐ × (P ∘ₘ πₐ))`, the mutual
  information between the parameter and the observation.
* `mul_klDiv_add_mul_klDiv_eq_jensenShannon_add`: the compensation identity.
* `jensenShannon_eq_iInf_klDiv`: `JS_α(μ, ν) = ⨅ ξ, (α * KL(μ, ξ) + (1 - α) * KL(ν, ξ))`.
* `jensenShannon_eq_iInf_klDiv_compProd`: `JS_α(μ, ν) = ⨅ ξ, KL(πₐ ⊗ₘ P, πₐ × ξ)`.
* `jensenShannon_le_mul_klDiv_add_mul_klDiv`: `JS_α(μ, ν) ≤ α * KL(μ, ξ) + (1 - α) * KL(ν, ξ)`
  for every finite measure `ξ`.
* `jensenShannon_pi_le`, `jensenShannon_pi_const_le`: subadditivity for product measures,
  `JS_α(⊗ᵢ μᵢ, ⊗ᵢ νᵢ) ≤ ∑ᵢ JS_α(μᵢ, νᵢ)` and `JS_α(μ^⊗n, ν^⊗n) ≤ n * JS_α(μ, ν)`.

## Implementation notes

The compensation identity follows from two applications of the chain rule for the
Kullback-Leibler divergence to `KL(πₐ ⊗ₘ P, πₐ × ξ)`: one along the parameter, which gives
`α * KL(μ, ξ) + (1 - α) * KL(ν, ξ)`, and one along the observation
(`klDiv_prod_eq_klDiv_snd_add`), which gives `KL(P ∘ₘ πₐ, ξ) + KL(πₐ ⊗ₘ P, πₐ × (P ∘ₘ πₐ))`.
-/

@[expose] public section

open Real MeasureTheory Filter Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {α : ℝ≥0}

section Prior

/-- The prior `boolMeasure α (1 - α)` on `Bool`. -/
local notation "πₐ" => Measure.boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞)

private lemma boolKernel_comp_prior (μ ν : Measure 𝓧) :
    Kernel.boolKernel μ ν ∘ₘ πₐ = α • μ + (1 - α) • ν := by
  rw [boolKernel_comp_measure, Measure.boolMeasure_apply_true,
    Measure.boolMeasure_apply_false, add_comm, Measure.coe_nnreal_smul, Measure.coe_nnreal_smul]

/-- The Kullback-Leibler divergence between `πₐ ⊗ₘ boolKernel μ ν` and `πₐ × ξ` is
`α * KL(μ, ξ) + (1 - α) * KL(ν, ξ)`. -/
private lemma klDiv_compProd_prior_prod (μ ν ξ : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] :
    klDiv (πₐ ⊗ₘ Kernel.boolKernel μ ν) ((πₐ).prod ξ)
      = α * klDiv μ ξ + (1 - α : ℝ≥0) * klDiv ν ξ := by
  rw [klDiv_compProd_boolKernel_prod, Measure.boolMeasure_apply_false,
    Measure.boolMeasure_apply_true]

/-- The Jensen-Shannon divergence is the mutual information between the parameter and the
observation, for the prior `πₐ = boolMeasure α (1 - α)` and the kernel `P = boolKernel μ ν`:
`JS_α(μ, ν) = KL(πₐ ⊗ₘ P, πₐ × (P ∘ₘ πₐ))`. -/
theorem jensenShannon_eq_klDiv_compProd (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    jensenShannon α μ ν = klDiv (πₐ ⊗ₘ Kernel.boolKernel μ ν)
      ((πₐ).prod (Kernel.boolKernel μ ν ∘ₘ πₐ)) := by
  rw [boolKernel_comp_prior, klDiv_compProd_prior_prod, jensenShannon]

/-- `KL(πₐ ⊗ₘ P, πₐ × ξ) = KL(P ∘ₘ πₐ, ξ) + JS_α(μ, ν)`, by the chain rule along the
observation. -/
private lemma klDiv_compProd_prior_prod_eq_add (hα : α ≤ 1) (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    klDiv (πₐ ⊗ₘ Kernel.boolKernel μ ν) ((πₐ).prod ξ)
      = klDiv (α • μ + (1 - α) • ν) ξ + jensenShannon α μ ν := by
  have := Measure.isProbabilityMeasure_boolMeasure_coe hα
  rw [klDiv_prod_eq_klDiv_snd_add, Measure.snd_compProd, jensenShannon_eq_klDiv_compProd,
    boolKernel_comp_prior]

/-- **Compensation identity** for the Jensen-Shannon divergence: for finite measures `μ`, `ν`
and `ξ`, `α * KL(μ, ξ) + (1 - α) * KL(ν, ξ) = JS_α(μ, ν) + KL(α • μ + (1 - α) • ν, ξ)`. -/
theorem mul_klDiv_add_mul_klDiv_eq_jensenShannon_add (hα : α ≤ 1) (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    α * klDiv μ ξ + (1 - α : ℝ≥0) * klDiv ν ξ
      = jensenShannon α μ ν + klDiv (α • μ + (1 - α) • ν) ξ := by
  rw [← klDiv_compProd_prior_prod, klDiv_compProd_prior_prod_eq_add hα, add_comm]

/-- **Variational formula** for the Jensen-Shannon divergence: for probability measures `μ` and
`ν`, `JS_α(μ, ν) = ⨅ ξ, (α * KL(μ, ξ) + (1 - α) * KL(ν, ξ))`, where the infimum is over
probability measures `ξ`. It is attained at `ξ = α • μ + (1 - α) • ν`. -/
theorem jensenShannon_eq_iInf_klDiv (hα : α ≤ 1) (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    jensenShannon α μ ν
      = ⨅ (ξ : Measure 𝓧) (_ : IsProbabilityMeasure ξ),
          α * klDiv μ ξ + (1 - α : ℝ≥0) * klDiv ν ξ := by
  refine le_antisymm (le_iInf₂ fun ξ _ ↦ ?_) ?_
  · rw [mul_klDiv_add_mul_klDiv_eq_jensenShannon_add hα]
    exact le_self_add
  · rw [jensenShannon]
    exact iInf₂_le _ (isProbabilityMeasure_smul_add_one_sub_smul hα)

/-- **Variational formula** for the Jensen-Shannon divergence, as an infimum of Kullback-Leibler
divergences between joint measures: `JS_α(μ, ν) = ⨅ ξ, KL(πₐ ⊗ₘ P, πₐ × ξ)`, where the infimum
is over probability measures `ξ`, `πₐ = boolMeasure α (1 - α)` and `P = boolKernel μ ν`. -/
theorem jensenShannon_eq_iInf_klDiv_compProd (hα : α ≤ 1) (μ ν : Measure 𝓧)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    jensenShannon α μ ν
      = ⨅ (ξ : Measure 𝓧) (_ : IsProbabilityMeasure ξ),
          klDiv (πₐ ⊗ₘ Kernel.boolKernel μ ν) ((πₐ).prod ξ) := by
  simp_rw [klDiv_compProd_prior_prod]
  exact jensenShannon_eq_iInf_klDiv hα μ ν

end Prior

/-- `JS_α(μ, ν) ≤ α * KL(μ, ξ) + (1 - α) * KL(ν, ξ)` for any finite measure `ξ`. -/
lemma jensenShannon_le_mul_klDiv_add_mul_klDiv (hα : α ≤ 1) (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    jensenShannon α μ ν ≤ α * klDiv μ ξ + (1 - α : ℝ≥0) * klDiv ν ξ := by
  rw [mul_klDiv_add_mul_klDiv_eq_jensenShannon_add hα]
  exact le_self_add

section Pi

variable {ι : Type*} [Fintype ι]

/-- **Subadditivity** of the Jensen-Shannon divergence for product measures:
`JS_α(⊗ᵢ μᵢ, ⊗ᵢ νᵢ) ≤ ∑ᵢ JS_α(μᵢ, νᵢ)`. -/
theorem jensenShannon_pi_le (hα : α ≤ 1) {𝓨 : ι → Type*} [∀ i, MeasurableSpace (𝓨 i)]
    (μ ν : (i : ι) → Measure (𝓨 i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    jensenShannon α (Measure.pi μ) (Measure.pi ν) ≤ ∑ i, jensenShannon α (μ i) (ν i) := by
  have (i : ι) : IsProbabilityMeasure (α • μ i + (1 - α) • ν i) :=
    isProbabilityMeasure_smul_add_one_sub_smul hα
  refine (jensenShannon_le_mul_klDiv_add_mul_klDiv hα _ _
    (Measure.pi fun i ↦ α • μ i + (1 - α) • ν i)).trans_eq ?_
  simp_rw [klDiv_pi, jensenShannon, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **Subadditivity** of the Jensen-Shannon divergence for product measures:
`JS_α(μ^⊗ι, ν^⊗ι) ≤ |ι| * JS_α(μ, ν)`. -/
theorem jensenShannon_pi_const_le (hα : α ≤ 1) (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    jensenShannon α (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : ι ↦ ν)
      ≤ Fintype.card ι * jensenShannon α μ ν := by
  simpa [nsmul_eq_mul] using jensenShannon_pi_le hα (fun _ : ι ↦ μ) (fun _ : ι ↦ ν)

end Pi

end ProbabilityTheory
