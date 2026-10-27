/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Bernoulli distribution: integrals, symmetry and the Bernoulli kernel

Complements to `Mathlib.Probability.Distributions.Bernoulli`: the Lebesgue integral against
`Ber(x, y, p)`, its masses at `x` and `y`, Bernoulli distributions on `Bool`, and the Markov
kernel from the unit interval which maps `p` to `Ber(x, y, p)`.

## Main definitions

* `bernoulliKernel x y`: the Markov kernel `p ↦ Ber(x, y, p)` from the unit interval.

## Main statements

* `lintegral_bernoulliMeasure`: the Lebesgue integral against `Ber(x, y, p)`.
* `bernoulliMeasure_swap`: `Ber(y, x, σ p) = Ber(x, y, p)`.
* `eq_bernoulliMeasure_real_true`: every probability measure on `Bool` is a Bernoulli distribution.
* `bernoulliKernel_comp_apply_singleton_left`: for `x ≠ y`, the composition of `bernoulliKernel x y`
  with a measure `μ` on the unit interval gives mass `∫⁻ p, p ∂μ` to `x`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace unitInterval

lemma coe_toNNReal_eq_ofReal (p : I) : (toNNReal p : ℝ≥0∞) = ENNReal.ofReal p := by
  rw [ENNReal.ofReal, show Real.toNNReal p = toNNReal p from Real.toNNReal_of_nonneg p.2.1]

lemma coe_toNNReal_symm_eq_ofReal (p : I) :
    (toNNReal (σ p) : ℝ≥0∞) = ENNReal.ofReal (1 - p) := by
  rw [coe_toNNReal_eq_ofReal, coe_symm_eq]

end unitInterval

open unitInterval

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

lemma bernoulliMeasure_swap (x y : 𝓧) (p : I) : Ber(y, x, σ p) = Ber(x, y, p) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, symm_symm, add_comm]

lemma lintegral_bernoulliMeasure [MeasurableSingletonClass 𝓧] (x y : 𝓧) (p : I)
    (f : 𝓧 → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal, smul_eq_mul, smul_eq_mul]

/-- Version of `lintegral_bernoulliMeasure` for a measurable function, without
`MeasurableSingletonClass`. -/
lemma lintegral_bernoulliMeasure' (x y : 𝓧) (p : I) {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac' _ hf, lintegral_dirac' _ hf,
    coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal, smul_eq_mul, smul_eq_mul]

lemma bernoulliMeasure_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧} (hxy : x ≠ y)
    (p : I) :
    Ber(x, y, p) {x} = ENNReal.ofReal p := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem p (.singleton _) rfl hxy.symm,
    coe_toNNReal_eq_ofReal]

lemma bernoulliMeasure_apply_singleton_right [MeasurableSingletonClass 𝓧] {x y : 𝓧} (hxy : x ≠ y)
    (p : I) :
    Ber(x, y, p) {y} = ENNReal.ofReal (1 - p) := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem p (.singleton _) hxy rfl,
    coe_toNNReal_symm_eq_ofReal]

/-- A probability measure on `Bool` is the Bernoulli distribution with parameter its mass at
`true`. -/
lemma eq_bernoulliMeasure_real_true (R : Measure Bool) [IsProbabilityMeasure R] :
    R = Ber(true, false,
      ⟨R.real {true}, Set.mem_Icc.mpr ⟨measureReal_nonneg, measureReal_le_one⟩⟩) := by
  have h_false : R {false} = 1 - R {true} := by
    rw [← measure_univ (μ := R), ← measure_add_measure_compl (MeasurableSet.singleton true),
      show ({true} : Set Bool)ᶜ = {false} by ext b; simp, ENNReal.add_sub_cancel_left
        (measure_ne_top _ _)]
  refine Measure.ext_of_singleton fun b ↦ ?_
  cases b
  · rw [h_false, bernoulliMeasure_apply_singleton_right (by decide),
      ENNReal.ofReal_sub _ measureReal_nonneg, ENNReal.ofReal_one, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [bernoulliMeasure_apply_singleton_left (by decide)]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- The Markov kernel from the unit interval to `𝓧` which maps `p` to the Bernoulli distribution
`Ber(x, y, p)`. -/
noncomputable def bernoulliKernel (x y : 𝓧) : Kernel I 𝓧 where
  toFun p := Ber(x, y, p)
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp_rw [bernoulliMeasure_apply _ hs]
    split_ifs <;> fun_prop

lemma bernoulliKernel_apply (x y : 𝓧) (p : I) : bernoulliKernel x y p = Ber(x, y, p) := rfl

instance (x y : 𝓧) : IsMarkovKernel (bernoulliKernel x y) :=
  ⟨fun p ↦ by rw [bernoulliKernel_apply]; infer_instance⟩

/-- The mass at `x` of the composition of `bernoulliKernel x y` with a measure on the unit interval
is the integral of the identity. -/
lemma bernoulliKernel_comp_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧}
    (hxy : x ≠ y) (μ : Measure I) :
    (bernoulliKernel x y ∘ₘ μ) {x} = ∫⁻ p, ENNReal.ofReal p ∂μ := by
  rw [Measure.bind_apply (MeasurableSet.singleton x) (bernoulliKernel x y).aemeasurable]
  simp_rw [bernoulliKernel_apply, bernoulliMeasure_apply_singleton_left hxy]

/-- The mass at `x` of the composition of `bernoulliKernel x y` with a finite measure on the unit
interval is the integral of the identity. -/
lemma bernoulliKernel_comp_real_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧}
    (hxy : x ≠ y) (μ : Measure I) [IsFiniteMeasure μ] :
    (bernoulliKernel x y ∘ₘ μ).real {x} = ∫ p, (p : ℝ) ∂μ := by
  have h_int : Integrable (fun p : I ↦ (p : ℝ)) μ :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun p ↦ by rw [Real.norm_of_nonneg p.2.1]; exact p.2.2)
  rw [measureReal_def, bernoulliKernel_comp_apply_singleton_left hxy,
    ← ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ fun p ↦ p.2.1),
    ENNReal.toReal_ofReal (integral_nonneg fun p ↦ p.2.1)]

end ProbabilityTheory
