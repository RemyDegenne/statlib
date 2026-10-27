/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.Probability.Notation
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# Extended integrals of log-likelihood ratios

Lemmas about the integrability, in the sense of `EIntegrable`, of functions involving
Radon-Nikodym derivatives and log-likelihood ratios.

## Main statements

* `MeasureTheory.eintegrable_rnDeriv_mul_iff`: for `μ ≪ ν`, `f` is `EIntegrable` with respect to
  `μ` iff `(∂μ/∂ν) * f` is `EIntegrable` with respect to `ν`.
* `MeasureTheory.eintegrable_llr`: if `μ ≪ ν` are finite measures, the log-likelihood ratio
  `llr μ ν` is `EIntegrable` with respect to `μ`.
-/

@[expose] public section

open scoped ENNReal ProbabilityTheory

open InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : MeasureTheory.Measure 𝓧}

namespace MeasureTheory

lemma lintegral_rnDeriv_mul_le (μ ν : Measure 𝓧) {X : 𝓧 → ℝ≥0∞} (hX : Measurable X) :
    ∫⁻ ω, (∂μ/∂ν) ω * X ω ∂ν ≤ ∫⁻ ω, X ω ∂μ := by
  calc ∫⁻ ω, (∂μ/∂ν) ω * X ω ∂ν
  _ = ∫⁻ ω, X ω ∂(ν.withDensity (∂μ/∂ν)) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hX]; simp
  _ ≤ ∫⁻ ω, X ω ∂μ := lintegral_mono' (μ.withDensity_rnDeriv_le ν) le_rfl

/-- For `μ ≪ ν`, a function `f` is `EIntegrable` with respect to `μ` iff `(∂μ/∂ν) * f` is
`EIntegrable` with respect to `ν`. -/
lemma eintegrable_rnDeriv_mul_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : 𝓧 → EReal} (hμν : μ ≪ ν) (hf : Measurable f) :
    EIntegrable (fun a ↦ (μ.rnDeriv ν a).toReal * f a) ν ↔ EIntegrable f μ := by
  have h_eq {g : 𝓧 → EReal} (hg : Measurable g) :
      ∫⁻ a, (((μ.rnDeriv ν a).toReal : EReal) * g a).toENNReal ∂ν = ∫⁻ a, (g a).toENNReal ∂μ := by
    nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    rw [Pi.mul_apply, EReal.toENNReal_mul (by simp)]
    simp [ENNReal.ofReal_toReal hx]
  rw [EIntegrable, EIntegrable, h_eq hf]
  simp_rw [← mul_neg]
  rw [h_eq (g := fun x ↦ -f x) hf.neg]

lemma llr_ae_eq_log_inv_rnDeriv [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    llr P μ =ᵐ[P] fun x ↦ Real.log ((μ.rnDeriv P)⁻¹ x).toReal := by
  filter_upwards [Measure.inv_rnDeriv' h_ac] with a ha using by rw [llr, ha]

lemma eintegrable_klFun_rnDeriv (P μ : Measure 𝓧) :
    EIntegrable (fun ω ↦ klFun (μ.rnDeriv P ω).toReal) P := by
  refine eintegrable_of_nonneg ?_
  simp only [EReal.coe_nonneg]
  exact fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg

lemma eintegrable_rnDeriv_mul_log_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    EIntegrable (fun a ↦ (μ.rnDeriv ν a).toReal * Real.log (μ.rnDeriv ν a).toReal) ν
      ↔ EIntegrable (fun a ↦ llr μ ν a) μ := eintegrable_rnDeriv_mul_iff hμν (by fun_prop)

lemma eintegrable_llr [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    EIntegrable (fun ω ↦ llr P μ ω) P := by
  rw [← eintegrable_rnDeriv_mul_log_iff h_ac]
  have h_eq a : (((∂P/∂μ) a).toReal * Real.log ((∂P/∂μ) a).toReal : EReal) =
      ((klFun (P.rnDeriv μ a).toReal + (P.rnDeriv μ a).toReal - 1 : ℝ) : EReal) := by
    simp [klFun]
  rw [eintegrable_congr (ae_of_all _ h_eq)]
  have h_int := eintegrable_klFun_rnDeriv μ P
  simp only [EReal.coe_sub, EReal.coe_add, EReal.coe_one]
  simp_rw [sub_eq_add_neg]
  refine eintegrable_add_of_ne_bot (by fun_prop) (by fun_prop) ?_ (by simp)
  refine eintegral_add_ne_bot (by fun_prop) (by fun_prop) ?_ ?_
  · rw [eintegral_eq_lintegral_of_nonneg]
    · simp
    · simp only [EReal.coe_nonneg]
      exact fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [eintegral_eq_lintegral_of_nonneg]
    · simp
    · simp

lemma eintegrable_ennreal_log_rnDeriv [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    EIntegrable (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) P := by
  have h_ae : (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) =ᵐ[P]
      (fun ω ↦ (Real.log ((μ.rnDeriv P)⁻¹ ω).toReal)) := by
    filter_upwards [Measure.rnDeriv_ne_top μ P, Measure.rnDeriv_pos' h_ac] with x hx1 hx2
    simp [ENNReal.log, hx1, hx2.ne']
  rw [eintegrable_congr h_ae]
  have h_ae' : (fun ω ↦ (llr P μ ω : EReal)) =ᵐ[P]
      fun x ↦ (Real.log ((μ.rnDeriv P)⁻¹ x).toReal : EReal) := by
    filter_upwards [llr_ae_eq_log_inv_rnDeriv h_ac] with x hx using by simp [hx]
  rw [eintegrable_congr h_ae'.symm]
  exact eintegrable_llr h_ac

end MeasureTheory
