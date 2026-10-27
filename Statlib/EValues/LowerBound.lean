/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Statlib.EValues.Bernoulli

/-!
# Lower bounds on the e-Rényi and e-Chernoff divergences

We compute the e-Rényi and e-Chernoff divergences between sets of probability measures on the unit
interval defined by constraints on their mean, and deduce lower bounds on the divergences between
sets of measures which are separated by the mean of a function with values in the unit interval.

The divergences between the probability measures on the unit interval with mean in `C₁` and those
with mean in `C₂` are equal to the divergences between the Bernoulli distributions with parameter
in `C₁` and those with parameter in `C₂`. Indeed, `bernoulliKernel true false` maps a probability
measure with mean `m` to the Bernoulli distribution with parameter `m`, the embedding of `Bool`
into the unit interval maps a Bernoulli distribution with parameter `q` to a measure with mean `q`,
and neither map can increase the divergences (data processing inequality).

## Main statements

* `erenyiDiv_integral_mem_eq_erenyiDiv_bernoulli`,
  `echernoffDiv_integral_mem_eq_echernoffDiv_bernoulli`: reduction to Bernoulli distributions.
* `erenyiDiv_bernoulli_le_of_integral_mem`, `echernoffDiv_bernoulli_le_of_integral_mem`: if the
  mean of a function with values in the unit interval is in `C₁` under the measures of `S` and in
  `C₂` under those of `T`, the divergence between `S` and `T` is at least the divergence between
  the Bernoulli distributions with parameter in `C₁` and those with parameter in `C₂`.
* `erenyiDiv_bounded`, `echernoffDiv_bounded`: for `δ ≤ η`, the e-Rényi divergence of order `α`
  and the e-Chernoff divergence between the probability measures on the unit interval with mean at
  most `δ` and those with mean at least `η` are the Rényi divergence of order `α` and the Chernoff
  information between the Bernoulli distributions with parameters `δ` and `η`.
* `le_erenyiDiv_of_separated`, `le_echernoffDiv_of_separated`: the corresponding explicit lower
  bounds on the divergences between sets of probability measures for which the mean of a function
  with values in the unit interval is at most `δ` and at least `η`. For `η = 1 - δ` and order
  `1/2`, the values are given by `erenyiDiv_inv_two_bernoulli_one_sub` and
  `echernoffDiv_bernoulli_one_sub`.
-/

@[expose] public section

open InformationTheory MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S T : Set (Measure 𝓧)} {α : ℝ≥0∞}

/-! ### Reduction to Bernoulli distributions -/

/-- If `f : 𝓧 → I` has mean in `C` under every probability measure of `S`, the images of the
measures of `S` by `f` are probability measures on the unit interval with mean in `C`. -/
lemma map_subset_setOf_integral_mem {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {C : Set ℝ} (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ∈ C) :
    {μ.map f | μ ∈ S} ⊆ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C} := by
  rintro _ ⟨μ, hμ, rfl⟩
  have := hS μ hμ
  refine ⟨inferInstance, ?_⟩
  rw [integral_map hf.aemeasurable (by fun_prop)]
  exact hSf μ hμ

/-- The embedding of `Bool` into the unit interval maps a Bernoulli distribution with parameter
in `C` to a probability measure with mean in `C`. -/
private lemma map_bernoulli_subset_setOf_integral_mem (C : Set ℝ) :
    {μ.map (fun b : Bool ↦ if b then (1 : I) else 0) |
        μ ∈ {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C)}}
      ⊆ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C} := by
  refine map_subset_setOf_integral_mem .of_discrete ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    infer_instance
  · rintro _ ⟨q, hq, rfl⟩
    simpa [integral_bernoulliMeasure] using hq

/-- The composition of `bernoulliKernel true false` with a probability measure on the unit
interval with mean in `C` is a Bernoulli distribution with parameter in `C`. -/
private lemma comp_bernoulliKernel_subset (C : Set ℝ) :
    {bernoulliKernel true false ∘ₘ μ |
        μ ∈ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C}}
      ⊆ {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C)} := by
  rintro _ ⟨μ, ⟨hμ, hμC⟩, rfl⟩
  refine ⟨_, ?_, (eq_bernoulliMeasure_real_true _).symm⟩
  rwa [Subtype.coe_mk, bernoulliKernel_comp_real_apply_singleton_left (by decide)]

/-- The e-Rényi divergence between the probability measures on the unit interval with mean in
`C₁` and those with mean in `C₂` is the e-Rényi divergence between the Bernoulli distributions with
parameter in `C₁` and those with parameter in `C₂`. -/
theorem erenyiDiv_integral_mem_eq_erenyiDiv_bernoulli (C₁ C₂ : Set ℝ) :
    erenyiDiv α {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C₁}
        {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C₂}
      = erenyiDiv α {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₁)}
        {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₂)} :=
  le_antisymm
    ((erenyiDiv_anti (map_bernoulli_subset_setOf_integral_mem C₁)
      (map_bernoulli_subset_setOf_integral_mem C₂)).trans (erenyiDiv_map_le .of_discrete))
    ((erenyiDiv_anti (comp_bernoulliKernel_subset C₁) (comp_bernoulliKernel_subset C₂)).trans
      (erenyiDiv_comp_le (bernoulliKernel true false)))

/-- The e-Chernoff divergence between the probability measures on the unit interval with mean in
`C₁` and those with mean in `C₂` is the e-Chernoff divergence between the Bernoulli distributions
with parameter in `C₁` and those with parameter in `C₂`. -/
theorem echernoffDiv_integral_mem_eq_echernoffDiv_bernoulli (C₁ C₂ : Set ℝ) :
    echernoffDiv {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C₁}
        {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ∈ C₂}
      = echernoffDiv {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₁)}
        {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₂)} :=
  le_antisymm
    ((echernoffDiv_anti (map_bernoulli_subset_setOf_integral_mem C₁)
      (map_bernoulli_subset_setOf_integral_mem C₂)).trans (echernoffDiv_map_le .of_discrete))
    ((echernoffDiv_anti (comp_bernoulliKernel_subset C₁) (comp_bernoulliKernel_subset C₂)).trans
      (echernoffDiv_comp_le (bernoulliKernel true false)))

/-- If the mean of a measurable `f : 𝓧 → I` is in `C₁` under the probability measures of `S` and
in `C₂` under those of `T`, the e-Rényi divergence between `S` and `T` is at least the e-Rényi
divergence between the Bernoulli distributions with parameter in `C₁` and those with parameter in
`C₂`. -/
theorem erenyiDiv_bernoulli_le_of_integral_mem {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {C₁ C₂ : Set ℝ} (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ∈ C₁)
    (hTf : ∀ ν ∈ T, ∫ ω, (f ω : ℝ) ∂ν ∈ C₂) :
    erenyiDiv α {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₁)}
        {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₂)}
      ≤ erenyiDiv α S T := by
  rw [← erenyiDiv_integral_mem_eq_erenyiDiv_bernoulli]
  exact (erenyiDiv_anti (map_subset_setOf_integral_mem hf hS hSf)
    (map_subset_setOf_integral_mem hf hT hTf)).trans (erenyiDiv_map_le hf)

/-- If the mean of a measurable `f : 𝓧 → I` is in `C₁` under the probability measures of `S` and
in `C₂` under those of `T`, the e-Chernoff divergence between `S` and `T` is at least the
e-Chernoff divergence between the Bernoulli distributions with parameter in `C₁` and those with
parameter in `C₂`. -/
theorem echernoffDiv_bernoulli_le_of_integral_mem {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {C₁ C₂ : Set ℝ} (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ∈ C₁)
    (hTf : ∀ ν ∈ T, ∫ ω, (f ω : ℝ) ∂ν ∈ C₂) :
    echernoffDiv {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₁)}
        {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ∈ C₂)}
      ≤ echernoffDiv S T := by
  rw [← echernoffDiv_integral_mem_eq_echernoffDiv_bernoulli]
  exact (echernoffDiv_anti (map_subset_setOf_integral_mem hf hS hSf)
    (map_subset_setOf_integral_mem hf hT hTf)).trans (echernoffDiv_map_le hf)

/-! ### Closed forms and lower bounds -/

/-- For `δ ≤ η`, the e-Rényi divergence of order `α < 1` between the probability measures on the
unit interval with mean at most `δ` and those with mean at least `η` is the Rényi divergence of
order `α` between the Bernoulli distributions with parameters `δ` and `η`. -/
theorem erenyiDiv_bounded (hα : α < 1) {δ η : ℝ} (hδ_pos : 0 < δ) (hδη : δ ≤ η) (hη : η < 1) :
    erenyiDiv α {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ η ≤ ∫ x, (x : ℝ) ∂μ}
      = ENNReal.ofReal ((α.toReal - 1)⁻¹ * Real.log (δ ^ α.toReal * η ^ (1 - α.toReal)
        + (1 - δ) ^ α.toReal * (1 - η) ^ (1 - α.toReal))) :=
  (erenyiDiv_integral_mem_eq_erenyiDiv_bernoulli (Set.Iic δ) (Set.Ici η)).trans
    (erenyiDiv_bernoulli hα hδ_pos hδη hη)

/-- For `δ < η`, the e-Chernoff divergence between the probability measures on the unit interval
with mean at most `δ` and those with mean at least `η` is the Chernoff information between the
Bernoulli distributions with parameters `δ` and `η`, `klBerReal r δ` for the `r` given by
`echernoffDiv_bernoulli`. -/
theorem echernoffDiv_bounded {δ η : ℝ} (hδ_pos : 0 < δ) (hδη : δ < η) (hη : η < 1) {r : ℝ}
    (hr : r = Real.log ((1 - δ) / (1 - η)) / (Real.log (η / δ) + Real.log ((1 - δ) / (1 - η)))) :
    echernoffDiv {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ η ≤ ∫ x, (x : ℝ) ∂μ}
      = ENNReal.ofReal (klBerReal r δ) :=
  (echernoffDiv_integral_mem_eq_echernoffDiv_bernoulli (Set.Iic δ) (Set.Ici η)).trans
    (echernoffDiv_bernoulli hδ_pos hδη hη hr)

/-- If the mean of a measurable `f : 𝓧 → I` is at most `δ` under the probability measures of `S`
and at least `η ≥ δ` under those of `T`, the e-Rényi divergence of order `α < 1` between `S` and
`T` is at least the Rényi divergence of order `α` between the Bernoulli distributions with
parameters `δ` and `η`. -/
theorem le_erenyiDiv_of_separated {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ) (hα : α < 1)
    {δ η : ℝ} (hδ_pos : 0 < δ) (hδη : δ ≤ η) (hη : η < 1)
    (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ≤ δ) (hTf : ∀ ν ∈ T, η ≤ ∫ ω, (f ω : ℝ) ∂ν) :
    ENNReal.ofReal ((α.toReal - 1)⁻¹ * Real.log (δ ^ α.toReal * η ^ (1 - α.toReal)
        + (1 - δ) ^ α.toReal * (1 - η) ^ (1 - α.toReal)))
      ≤ erenyiDiv α S T :=
  (erenyiDiv_bernoulli hα hδ_pos hδη hη).symm.le.trans
    (erenyiDiv_bernoulli_le_of_integral_mem hf hS hT (C₁ := Set.Iic δ) (C₂ := Set.Ici η) hSf hTf)

/-- If the mean of a measurable `f : 𝓧 → I` is at most `δ` under the probability measures of `S`
and at least `η > δ` under those of `T`, the e-Chernoff divergence between `S` and `T` is at least
the Chernoff information between the Bernoulli distributions with parameters `δ` and `η`,
`klBerReal r δ` for the `r` given by `echernoffDiv_bernoulli`. -/
theorem le_echernoffDiv_of_separated {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ η : ℝ} (hδ_pos : 0 < δ) (hδη : δ < η) (hη : η < 1) {r : ℝ}
    (hr : r = Real.log ((1 - δ) / (1 - η)) / (Real.log (η / δ) + Real.log ((1 - δ) / (1 - η))))
    (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ≤ δ) (hTf : ∀ ν ∈ T, η ≤ ∫ ω, (f ω : ℝ) ∂ν) :
    ENNReal.ofReal (klBerReal r δ) ≤ echernoffDiv S T :=
  (echernoffDiv_bernoulli hδ_pos hδη hη hr).symm.le.trans
    (echernoffDiv_bernoulli_le_of_integral_mem hf hS hT (C₁ := Set.Iic δ) (C₂ := Set.Ici η) hSf
      hTf)

end ProbabilityTheory
