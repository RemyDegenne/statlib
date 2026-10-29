/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Posterior
public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Statlib.Divergence.FDiv.CondFDiv
public import Statlib.Divergence.FDiv.CompProd

/-!
# Conditional Kullback-Leibler divergence

## Main definitions

* `condKL κ η μ`: the conditional Kullback-Leibler divergence of the kernels `κ` and `η` with
  respect to `μ`, `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.

## Main statements

* `condKL_eq_lintegral`: `condKL κ η μ = ∫⁻ a, klDiv (κ a) (η a) ∂μ`, if `α` is countable or `β`
  is countably generated and `μ` is finite.
* `condKL_ne_top_iff`: finiteness of the conditional divergence.
* `klDiv_compProd_boolKernel_prod`, `klDiv_prod_compProd_boolKernel`: for a finite measure `ρ` on
  `Bool`, `KL(ρ ⊗ₘ boolKernel μ ν, ρ × ξ) = ρ {false} * KL(μ, ξ) + ρ {true} * KL(ν, ξ)`, and the
  same with the arguments of `KL` swapped.
* `klDiv_compProd_eq_add_condKL`, `klDiv_fst_add_condKL`: chain rules for the Kullback-Leibler
  divergence.
* `klDiv_compProd_eq_add_condKL_posterior`: chain rule with the posteriors (Bayesian inverses),
  `KL(μ ⊗ₘ κ, ν ⊗ₘ η) = KL(κ ∘ₘ μ, η ∘ₘ ν) + KL(κ†μ, η†ν | κ ∘ₘ μ)`.
* `condKL_compProd_kernel`: chain rule for the conditional divergence.
* `klDiv_prod_two`, `klDiv_pi`: tensorization.

The chain rules follow from Mathlib's chain rule `InformationTheory.klDiv_compProd_eq_add`. Those
stated with composition-products (`klDiv_compProd_eq_add_condKL`, `condKL_compProd_kernel`) hold
without assumptions on the measurable spaces. `klDiv_fst_add_condKL` and
`klDiv_compProd_eq_add_condKL_posterior` need standard Borel spaces, for the disintegration and the
posterior to exist. The results expressing the conditional divergence through the kernels `κ a`
and `η a` need `CountableOrCountablyGenerated` assumptions.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : Kernel α β}

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one. -/
lemma klDiv_ae_ne_top_iff : (∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [klDiv_ne_top_iff, eventually_and]

/-- The Kullback-Leibler divergence between the kernels `κ` and `η` conditional to the measure `μ`,
defined as `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.

If `α` is countable or `β` is countably generated, `μ` is finite and `κ`, `η` are finite, it is
equal to `∫⁻ a, klDiv (κ a) (η a) ∂μ` (`condKL_eq_lintegral`). See also
`toReal_condKL_eq_integral` for its real-valued version. -/
noncomputable
def condKL (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)

lemma condKL_eq_condFDiv [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv klDivFun κ η μ :=
  klDiv_eq_fDiv

@[simp]
lemma condKL_self (κ : Kernel α β) (μ : Measure α) [SigmaFinite μ] [IsFiniteKernel κ] :
    condKL κ κ μ = 0 :=
  klDiv_self _

@[simp]
lemma condKL_zero_left [IsFiniteMeasure μ] [IsFiniteKernel η] :
    condKL 0 η μ = ∫⁻ a, η a Set.univ ∂μ := by
  rw [condKL, Measure.compProd_zero_right, klDiv_zero_left, Measure.compProd_apply .univ]
  simp

lemma condKL_zero_right [SFinite μ] [IsSFiniteKernel κ] (h : ∃ᵐ a ∂μ, κ a ≠ 0) :
    condKL κ 0 μ = ∞ := by
  -- `μ ⊗ₘ κ` is not zero since its mass is `∫⁻ a, κ a univ ∂μ`
  have h_ne : μ ⊗ₘ κ ≠ 0 := by
    intro h0
    refine h ?_
    have h_univ : ∫⁻ a, κ a .univ ∂μ = 0 := by
      have h_univ := congrArg (fun ρ : Measure (α × β) ↦ ρ .univ) h0
      simpa [Measure.compProd_apply MeasurableSet.univ] using h_univ
    filter_upwards [(lintegral_eq_zero_iff (κ.measurable_coe .univ)).mp h_univ] with a ha
    simpa using ha
  have : NeZero (μ ⊗ₘ κ) := ⟨h_ne⟩
  rw [condKL, Measure.compProd_zero_right, klDiv_zero_right]

@[simp]
lemma condKL_zero_measure : condKL κ η 0 = 0 := by simp [condKL]

@[simp]
lemma condKL_isEmpty_left [IsEmpty α] : condKL κ η μ = 0 := by
  simp [condKL, Subsingleton.elim (μ ⊗ₘ κ) 0, Subsingleton.elim (μ ⊗ₘ η) 0]

@[simp]
lemma condKL_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condKL (Kernel.const β μ) (Kernel.const β ν) ξ = (klDiv μ ν) * ξ .univ := by
  rw [condKL_eq_condFDiv, klDiv_eq_fDiv]
  exact condFDiv_const

section CondKLEq

variable [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ] [IsFiniteKernel κ]
  [IsFiniteKernel η]

/-- The conditional KL divergence is the integral of the KL divergences between the kernels. -/
lemma condKL_eq_lintegral : condKL κ η μ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  simp_rw [condKL_eq_condFDiv, condFDiv_eq_lintegral, klDiv_eq_fDiv]

@[simp]
lemma condKL_of_not_ae_ne_top (h : ¬ ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞) :
    condKL κ η μ = ∞ := by
  rw [condKL_eq_lintegral]
  by_contra h'
  exact h ((ae_lt_top (measurable_klDiv _ _) h').mono fun x hx ↦ hx.ne)

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condKL κ η μ = ∞ := by
  rw [condKL_eq_condFDiv]
  exact condFDiv_of_not_ae_ac derivAtTop_klDivFun h

lemma condKL_ne_top_iff :
    condKL κ η μ ≠ ∞
    ↔ (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
      ∧ Integrable (fun a ↦ (klDiv (κ a) (η a)).toReal) μ := by
  rw [← and_assoc, ← klDiv_ae_ne_top_iff, condKL_eq_lintegral]
  refine ⟨fun h ↦ ?_, fun ⟨h_ae, h_int⟩ ↦ ?_⟩
  · have h_ae : ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞ :=
      (ae_lt_top (measurable_klDiv κ η) h).mono fun _ ha ↦ ha.ne
    exact ⟨h_ae, (integrable_toReal_iff (measurable_klDiv κ η).aemeasurable h_ae).mpr h⟩
  · exact (integrable_toReal_iff (measurable_klDiv κ η).aemeasurable h_ae).mp h_int

lemma condKL_eq_top_iff :
    condKL κ η μ = ∞
      ↔ ¬ (∀ᵐ a ∂μ, κ a ≪ η a) ∨ ¬ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
        ∨ ¬ Integrable (fun a ↦ (klDiv (κ a) (η a)).toReal) μ := by
  rw [← not_iff_not, ← ne_eq, condKL_ne_top_iff]
  tauto

lemma toReal_condKL_eq_integral (h : condKL κ η μ ≠ ∞) :
    (condKL κ η μ).toReal = ∫ a, (klDiv (κ a) (η a)).toReal ∂μ := by
  rw [condKL_eq_lintegral] at h ⊢
  rw [integral_toReal (measurable_klDiv _ _).aemeasurable]
  exact ae_lt_top (measurable_klDiv _ _) h

end CondKLEq

section CompProd

/-- The conditional KL divergence with respect to a composition-product `μ ⊗ₘ ξ` is an iterated
conditional KL divergence. -/
lemma condKL_measure_compProd [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ∫⁻ x, condKL (κ.sectR x) (η.sectR x) (ξ x) ∂μ := by
  simp_rw [condKL_eq_condFDiv, condFDiv_measure_compProd]

/-- The Kullback-Leibler divergence between `ρ ⊗ₘ boolKernel μ ν` and `ρ × ξ` is the sum of
`KL(μ, ξ)` and `KL(ν, ξ)` weighted by `ρ {false}` and `ρ {true}`. -/
lemma klDiv_compProd_boolKernel_prod (ρ : Measure Bool) [IsFiniteMeasure ρ] (μ ν ξ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    klDiv (ρ ⊗ₘ Kernel.boolKernel μ ν) (ρ.prod ξ)
      = ρ {false} * klDiv μ ξ + ρ {true} * klDiv ν ξ := by
  rw [← Measure.compProd_const, ← condKL, condKL_eq_lintegral, lintegral_bool]
  simp [mul_comm]

/-- The Kullback-Leibler divergence between `ρ × ξ` and `ρ ⊗ₘ boolKernel μ ν` is the sum of
`KL(ξ, μ)` and `KL(ξ, ν)` weighted by `ρ {false}` and `ρ {true}`. -/
lemma klDiv_prod_compProd_boolKernel (ρ : Measure Bool) [IsFiniteMeasure ρ] (μ ν ξ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    klDiv (ρ.prod ξ) (ρ ⊗ₘ Kernel.boolKernel μ ν)
      = ρ {false} * klDiv ξ μ + ρ {true} * klDiv ξ ν := by
  rw [← Measure.compProd_const, ← condKL, condKL_eq_lintegral, lintegral_bool]
  simp [mul_comm]

section ChainRule

/-- The **chain rule** for the KL divergence. -/
lemma klDiv_compProd_eq_add_condKL [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + condKL κ η μ :=
  klDiv_compProd_eq_add μ ν κ η

/-- The **chain rule** for the KL divergence. -/
lemma klDiv_fst_add_condKL [StandardBorelSpace β] [Nonempty β] {μ ν : Measure (α × β)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.fst ν.fst + condKL μ.condKernel ν.condKernel μ.fst = klDiv μ ν := by
  rw [← klDiv_compProd_eq_add_condKL, μ.disintegrate, ν.disintegrate]

/-- **Chain rule** for the KL divergence, with the posteriors (Bayesian inverses) `κ†μ` and `η†ν`:
`KL(μ ⊗ₘ κ, ν ⊗ₘ η) = KL(κ ∘ₘ μ, η ∘ₘ ν) + KL(κ†μ, η†ν | κ ∘ₘ μ)`. -/
lemma klDiv_compProd_eq_add_condKL_posterior [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv (κ ∘ₘ μ) (η ∘ₘ ν) + condKL (κ†μ) (η†ν) (κ ∘ₘ μ) := by
  rw [← klDiv_map_swap, ← compProd_posterior_eq_map_swap, ← compProd_posterior_eq_map_swap,
    klDiv_compProd_eq_add_condKL]

/-- The **chain rule** for the conditional KL divergence:
`KL(κ₁ ⊗ κ₂, η₁ ⊗ η₂ | μ) = KL(κ₁, η₁ | μ) + KL(κ₂, η₂ | μ ⊗ κ₁)`. That is,
`KL(μ ⊗ (κ₁ ⊗ κ₂), μ ⊗ (η₁ ⊗ η₂)) = KL(μ ⊗ κ₁, μ ⊗ η₁) + KL((μ ⊗ κ₁) ⊗ κ₂, (μ ⊗ κ₁) ⊗ η₂)`. -/
lemma condKL_compProd_kernel [IsFiniteMeasure μ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = condKL κ₁ η₁ μ + condKL κ₂ η₂ (μ ⊗ₘ κ₁) := by
  simp only [condKL]
  rw [← Measure.compProd_assoc', ← Measure.compProd_assoc',
    klDiv_map_measurableEmbedding _ _ MeasurableEquiv.prodAssoc.measurableEmbedding,
    klDiv_compProd_eq_add]

end ChainRule

end CompProd

end Conditional

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

/-- **Data-processing inequality**: composing a measure with two kernels decreases their
conditional KL divergence. -/
lemma klDiv_comp_left_le (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condKL κ η μ := by
  rw [klDiv_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_comp_left_le μ κ η

end DataProcessingInequality

section Tensorization

variable {β : Type*} {mβ : MeasurableSpace β}

/-- The Kullback-Leibler divergence between two products with the same first factor. -/
lemma klDiv_prod_right [IsFiniteMeasure μ] {ξ ψ : Measure β} [IsFiniteMeasure ξ]
    [IsFiniteMeasure ψ] :
    klDiv (μ.prod ξ) (μ.prod ψ) = μ .univ * klDiv ξ ψ := by
  rw [klDiv_eq_fDiv, klDiv_eq_fDiv, fDiv_prod_right]

lemma klDiv_prod_two' {ξ ψ : Measure β} [IsProbabilityMeasure ξ] [IsProbabilityMeasure ψ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod ξ) (ν.prod ψ) = klDiv μ ν + klDiv ξ ψ * (μ .univ) := by
  rw [← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_right, mul_comm]

/-- Tensorization property for KL divergence -/
lemma klDiv_prod_two {ξ ψ : Measure β} [IsProbabilityMeasure ξ] [IsProbabilityMeasure ψ]
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod ξ) (ν.prod ψ) = klDiv μ ν + klDiv ξ ψ := by
  simp only [klDiv_prod_two', measure_univ, mul_one]

lemma klDiv_pi {ι : Type*} [hι : Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ ν : (i : ι) → Measure (β i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {β : ι → Type u_4}
    [(i : ι) → MeasurableSpace (β i)]
    {μ ν : (i : ι) → Measure (β i)} [∀ (i : ι), IsProbabilityMeasure (μ i)]
    [∀ (i : ι), IsProbabilityMeasure (ν i)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i : ι, klDiv (μ i) (ν i) ) ?_ ?_ ?_ ι
  · intro ι ι' hι' e h β _ μ ν _ _
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    specialize h (β := fun i ↦ β (e i)) (μ := fun i ↦ μ (e i)) (ν := fun i ↦ ν (e i))
    rw [Fintype.sum_equiv e.symm _ (fun i ↦ klDiv (μ (e i)) (ν (e i)))
      (fun i ↦ by rw [Equiv.apply_symm_apply]), ← h, klDiv_eq_fDiv, klDiv_eq_fDiv]
    let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
      MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
    have me := MeasurableEquiv.measurableEmbedding e_meas.symm
    convert (fDiv_map_measurableEmbedding me).symm
      <;> try {rw [← Measure.pi_map_piCongrLeft e, MeasurableEquiv.map_symm_map]}
      <;> infer_instance
  · intro β _ μ ν _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, klDiv_self, Finset.univ_eq_empty,
      Finset.sum_empty]
  · intro ι hι ind_h β _ μ ν _ _
    specialize ind_h (β := fun i ↦ β i) (μ := fun i ↦ μ i) (ν := fun i ↦ ν i)
    have h : klDiv (Measure.pi μ) (Measure.pi ν) = klDiv ((Measure.pi (fun (i : ι) ↦ μ i)).prod
        (μ none)) ((Measure.pi (fun (i : ι) ↦ ν i)).prod (ν none)) := by
      rw [klDiv_eq_fDiv, klDiv_eq_fDiv]
      let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
        MeasurableEquiv.piOptionEquivProd β |>.symm
      have me := MeasurableEquiv.measurableEmbedding e_meas
      convert fDiv_map_measurableEmbedding me
        <;> try {exact Measure.pi_map_piOptionEquivProd _ |>.symm} <;> infer_instance
    rw [Fintype.sum_option, h, add_comm, ← ind_h]
    convert klDiv_prod_two <;> infer_instance

lemma klDiv_pi_const {ι : Type*} [hι : Fintype ι]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) = hι.card * klDiv μ ν := by
  rw [klDiv_pi, Finset.sum_const, (Finset.card_eq_iff_eq_univ _).mpr rfl, nsmul_eq_mul]

end Tensorization

end ProbabilityTheory
