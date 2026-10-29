/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Kernel.Integral
public import Statlib.Divergence.FDiv.CompProd
public import Statlib.Divergence.FDiv.Measurable
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!

# Conditional f-divergence

## Main definitions

* `condFDiv f κ η μ`: the conditional f-divergence `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)` between the
  kernels `κ` and `η` with respect to the measure `μ`.

## Main statements

* `condFDiv_eq_lintegral`: `condFDiv f κ η μ = ∫⁻ x, fDiv f (κ x) (η x) ∂μ`, if `α` is countable
  or `β` is countably generated and `μ` is σ-finite.
* `condFDiv_ne_top_iff`, `condFDiv_eq_top_iff`: finiteness of the conditional f-divergence.
* `fDiv_comp_left_le`: `fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ`.
* `condFDiv_measure_compProd`: the conditional f-divergence with respect to a
  composition-product `μ ⊗ₘ ξ` is an iterated conditional f-divergence.

## Implementation details

The conditional f-divergence is defined with composition-products rather than as the integral
`∫⁻ x, fDiv f (κ x) (η x) ∂μ`. The function `x ↦ fDiv f (κ x) (η x)` is known to be measurable
only under assumptions on the measurable spaces (`CountableOrCountablyGenerated α β`), while
results on composition-products like the data-processing inequality hold without them. Under
those assumptions, the two definitions agree for σ-finite `μ` (`condFDiv_eq_lintegral`).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : DivFunction}

section Conditional

/-- The conditional f-divergence between the kernels `κ` and `η` with respect to the measure `μ`,
defined as `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`.

If `α` is countable or `β` is countably generated, `μ` is σ-finite and `κ`, `η` are finite, it is
equal to `∫⁻ x, fDiv f (κ x) (η x) ∂μ` (`condFDiv_eq_lintegral`) and to
`∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ + f.derivAtTop * ∫⁻ a, (κ a).singularPart (η a) univ ∂μ`
(`condFDiv_eq_add`). See also `toReal_condFDiv_eq_integral` for its real-valued version. -/
noncomputable
def condFDiv (f : DivFunction) (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional f divergence, the second version is the preferred one. -/
lemma fDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞)
    ↔ (∀ᵐ a ∂μ, ∫⁻ x, f ((∂κ a/∂η a) x) ∂η a ≠ ∞) ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  simp_rw [fDiv_ne_top_iff, eventually_and, eventually_all]

@[simp]
lemma condFDiv_self (κ : Kernel α β) (μ : Measure α) [SigmaFinite μ] [IsFiniteKernel κ] :
    condFDiv f κ κ μ = 0 :=
  fDiv_self _

@[simp]
lemma condFDiv_zero_left [SFinite μ] [IsSFiniteKernel η] :
    condFDiv f 0 η μ = f 0 * ∫⁻ a, η a .univ ∂μ := by
  rw [condFDiv, Measure.compProd_zero_right, fDiv_zero_measure_left,
    Measure.compProd_apply .univ]
  simp

@[simp]
lemma condFDiv_zero_measure : condFDiv f κ η 0 = 0 := by simp [condFDiv]

@[simp]
lemma condFDiv_of_isEmpty_left [IsEmpty α] : condFDiv f κ η μ = 0 := by
  simp [condFDiv, Subsingleton.elim (μ ⊗ₘ κ) 0, Subsingleton.elim (μ ⊗ₘ η) 0]

@[simp]
lemma condFDiv_of_isEmpty_right [IsEmpty β] : condFDiv f κ η μ = 0 := by
  simp [condFDiv, Subsingleton.elim (μ ⊗ₘ κ) 0, Subsingleton.elim (μ ⊗ₘ η) 0]

@[simp]
lemma condFDiv_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condFDiv f (Kernel.const β μ) (Kernel.const β ν) ξ = (fDiv f μ ν) * ξ .univ := by
  rw [condFDiv, Measure.compProd_const, Measure.compProd_const, fDiv_prod_right, mul_comm]

/-- **Data-processing inequality**: composing a measure with two kernels decreases their
conditional f-divergence. -/
lemma fDiv_comp_left_le (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ :=
  fDiv_comp_le_compProd μ μ κ η

section CondFDivEq

variable [CountableOrCountablyGenerated α β]

/-- The conditional f-divergence as a sum of an integral of `f` and of a singular part term. -/
lemma condFDiv_eq_add [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∫⁻ a, ∫⁻ y, f ((∂κ a/∂η a) y) ∂η a ∂μ
      + f.derivAtTop * ∫⁻ a, (κ a).singularPart (η a) .univ ∂μ := by
  rw [condFDiv, fDiv, Measure.lintegral_compProd DivFunction.measurable_comp_rnDeriv,
    lintegral_singularPart _ _ _ .univ, univ_prod_univ]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [rnDeriv_measure_compProd_right' μ κ η] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

/-- The conditional f-divergence is the integral of the f-divergences between the kernels. -/
lemma condFDiv_eq_lintegral [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∫⁻ x, fDiv f (κ x) (η x) ∂μ := by
  have h_meas : Measurable fun a ↦ (κ a).singularPart (η a) .univ :=
    (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
  simp_rw [condFDiv_eq_add, fDiv]
  rw [lintegral_add_right _ (h_meas.const_mul _), lintegral_const_mul _ h_meas]

/-- Equivalence between two possible versions of the second condition for the finiteness of the
conditional f divergence, the second version is the preferred one. -/
lemma lintegral_fDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, fDiv f (κ x) (η x) ∂μ ≠ ∞ ↔ ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ ≠ ∞ := by
  by_cases h_top : f.derivAtTop = ∞
  · rw [lintegral_congr_ae]
    filter_upwards [h_ac h_top] with a ha
    rw [fDiv_of_absolutelyContinuous ha]
  · simp_rw [fDiv]
    rw [lintegral_add_right]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact (Kernel.measurable_coe _ .univ).const_mul _
    simp only [ne_eq, ENNReal.add_eq_top, not_or, and_iff_left_iff_imp]
    intro _
    rw [lintegral_const_mul]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact Kernel.measurable_coe _ .univ
    refine ENNReal.mul_ne_top h_top ?_
    rw [lintegral_singularPart _ _ _ .univ]
    simp

@[simp]
lemma condFDiv_of_not_ae_finite [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞) :
    condFDiv f κ η μ = ∞ := by
  rw [condFDiv_eq_lintegral]
  by_contra h_not
  exact h <| (ae_lt_top (measurable_fDiv κ η) h_not).mono fun _ ha ↦ ha.ne

@[simp]
lemma condFDiv_of_not_ae_ac [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_top : f.derivAtTop = ∞) (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ∞ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

@[simp]
lemma condFDiv_of_lintegral_eq_top [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ = ∞) :
    condFDiv f κ η μ = ∞ := by
  by_cases h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞
  swap; · exact condFDiv_of_not_ae_finite h_top
  rw [condFDiv_eq_lintegral]
  by_contra h_ne
  exact (lintegral_fDiv_ne_top_iff (fDiv_ae_ne_top_iff.mp h_top).2).mp h_ne hf

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ ≠ ∞
        ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  refine ⟨fun h ↦ ⟨fun h_eq ↦ h (condFDiv_of_lintegral_eq_top h_eq), fun h_eq_top ↦ ?_⟩,
    fun ⟨h1, h2⟩ ↦ ?_⟩
  · by_contra h_not
    exact h <| condFDiv_of_not_ae_ac h_eq_top h_not
  · rw [condFDiv_eq_lintegral]
    exact (lintegral_fDiv_ne_top_iff h2).mpr h1

lemma condFDiv_eq_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ = ∞
        ∨ (f.derivAtTop = ∞ ∧ ¬ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  have h := condFDiv_ne_top_iff (κ := κ) (η := η) (μ := μ) (f := f)
  tauto

lemma toReal_condFDiv_eq_integral [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : condFDiv f κ η μ ≠ ∞) :
    (condFDiv f κ η μ).toReal = ∫ x, (fDiv f (κ x) (η x)).toReal ∂μ := by
  rw [condFDiv_eq_lintegral] at h ⊢
  rw [integral_toReal (measurable_fDiv _ _).aemeasurable]
  exact ae_lt_top (measurable_fDiv _ _) h

lemma condFDiv_of_ae_ac [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ∫⁻ a, ∫⁻ y, f ((∂κ a/∂η a) y) ∂η a ∂μ := by
  rw [condFDiv_eq_add]
  suffices ∫⁻ a, ((κ a).singularPart (η a)) univ ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff]
  swap; · exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
  filter_upwards [h_ac] with x hx
  simp only [Pi.zero_apply, Measure.measure_univ_eq_zero]
  exact Measure.singularPart_eq_zero_of_ac hx

end CondFDivEq

section CompProdMeasure

variable {γ : Type*} {mγ : MeasurableSpace γ}

/-- The conditional f-divergence with respect to a composition-product `μ ⊗ₘ ξ` is an iterated
conditional f-divergence. -/
lemma condFDiv_measure_compProd [CountableOrCountablyGenerated (α × β) γ] [SigmaFinite μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η (μ ⊗ₘ ξ) = ∫⁻ x, condFDiv f (κ.sectR x) (η.sectR x) (ξ x) ∂μ := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condFDiv_eq_lintegral, Measure.lintegral_compProd (measurable_fDiv _ _)]
  refine lintegral_congr fun x ↦ ?_
  rw [condFDiv_eq_lintegral]
  rfl

end CompProdMeasure

end Conditional

section OfReal

/-! ### Conditional f-divergences for a `DivFunction` given by `DivFunction.ofReal` -/

variable {μ : Measure α} {κ η : Kernel α β}

lemma integrable_fDiv_ofReal_iff_of_ne_top [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (h_ne : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  have h : ∀ᵐ a ∂μ, (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal
      = ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal
          * ((κ a).singularPart (η a) .univ).toReal := by
    filter_upwards [h_int] with a h_int
    exact toReal_fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int h_ne
  rw [integrable_congr h, integrable_add_iff_integrable_left']
  refine Integrable.const_mul ?_ _
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  · rw [lintegral_singularPart _ _ _ .univ]
    simp

lemma integrable_fDiv_ofReal_iff_of_ac [IsFiniteKernel κ]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hμη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  refine integrable_congr ?_
  filter_upwards [h_int, hμη] with a h_int hμη
  exact toReal_fDiv_ofReal_eq_integral_add_of_ac hf_nonneg h_cont h_int hμη

end OfReal

end ProbabilityTheory
