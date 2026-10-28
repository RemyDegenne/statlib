/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.Probability.Notation
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# Extended integrals of log-likelihood ratios

Lemmas about the integrability, in the sense of `EIntegrable`, of functions involving
Radon-Nikodym derivatives and log-likelihood ratios.

## Main statements

* `MeasureTheory.eintegral_llr_ne_bot`: if `μ ≪ ν` with `ν` finite, the negative part of the
  log-likelihood ratio `llr μ ν` has finite integral with respect to `μ`, hence `llr μ ν` is
  `EIntegrable` with respect to `μ` (`MeasureTheory.eintegrable_llr`).
-/

@[expose] public section

open scoped ENNReal ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : MeasureTheory.Measure 𝓧}

namespace MeasureTheory

lemma lintegral_rnDeriv_mul_le (μ ν : Measure 𝓧) {X : 𝓧 → ℝ≥0∞} (hX : Measurable X) :
    ∫⁻ ω, (∂μ/∂ν) ω * X ω ∂ν ≤ ∫⁻ ω, X ω ∂μ := by
  calc ∫⁻ ω, (∂μ/∂ν) ω * X ω ∂ν
  _ = ∫⁻ ω, X ω ∂(ν.withDensity (∂μ/∂ν)) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hX]; simp
  _ ≤ ∫⁻ ω, X ω ∂μ := lintegral_mono' (μ.withDensity_rnDeriv_le ν) le_rfl

lemma llr_ae_eq_log_inv_rnDeriv [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    llr P μ =ᵐ[P] fun x ↦ Real.log ((μ.rnDeriv P)⁻¹ x).toReal := by
  filter_upwards [Measure.inv_rnDeriv' h_ac] with a ha using by rw [llr, ha]

/-- If `μ ≪ ν` with `ν` finite, the negative part of the log-likelihood ratio `llr μ ν` has finite
integral with respect to `μ`: it is at most `(∂μ/∂ν)⁻¹ = ∂ν/∂μ`. -/
lemma eintegral_llr_ne_bot {μ ν : Measure 𝓧} [SigmaFinite μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    ∫ᵉ x, llr μ ν x ∂μ ≠ ⊥ := by
  rw [eintegral_ne_bot_iff_lintegral_ne_top]
  refine ne_top_of_le_ne_top (measure_ne_top ν .univ) ?_
  calc ∫⁻ x, (-(llr μ ν x : EReal)).toENNReal ∂μ
  _ ≤ ∫⁻ x, ν.rnDeriv μ x ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [Measure.inv_rnDeriv h_ac, Measure.rnDeriv_pos h_ac,
      h_ac.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx h_pos h_lt_top
    have hy : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
    rw [← hx, Pi.inv_apply, ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr h_pos.ne'),
      ENNReal.toReal_inv, ← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toReal_coe, llr_def, ← Real.log_inv]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (Real.log_le_sub_one_of_pos (inv_pos.mpr hy)).trans (by linarith)
  _ ≤ ν .univ := Measure.lintegral_rnDeriv_le

/-- If `μ ≪ ν` with `ν` finite, the log-likelihood ratio `llr μ ν` is `EIntegrable` with respect
to `μ`. -/
lemma eintegrable_llr {μ ν : Measure 𝓧} [SigmaFinite μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    EIntegrable (fun x ↦ llr μ ν x) μ :=
  eintegrable_of_eintegral_ne_bot (eintegral_llr_ne_bot h_ac)

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

section ExpLLR

open Real Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- If `μ ≪ ν`, then `exp (a * llr μ ν) = (∂μ/∂ν) ^ a`, `μ`-almost everywhere. -/
lemma exp_mul_llr_of_ac [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) {a : ℝ} :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [hμν <| rnDeriv_lt_top μ ν, rnDeriv_pos hμν] with x hx_lt_top hx_pos
  have h_pos : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [llr_def, ← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

/-- If `ν ≪ μ`, then `exp (a * llr μ ν) = (∂μ/∂ν) ^ a`, `ν`-almost everywhere. -/
lemma exp_mul_llr_of_ac' [SigmaFinite μ] [SigmaFinite ν] (hνμ : ν ≪ μ)
    {a : ℝ} :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [rnDeriv_lt_top μ ν, rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
  have h_pos : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [llr_def, ← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

end ExpLLR

end MeasureTheory
