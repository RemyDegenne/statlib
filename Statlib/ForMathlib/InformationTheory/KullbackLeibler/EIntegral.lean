/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
public import Statlib.ForMathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The Kullback-Leibler divergence as an extended integral

For `μ ≪ ν` finite measures, the Kullback-Leibler divergence `klDiv μ ν` is
`∫ᵉ x, llr μ ν x ∂μ + ν univ - μ univ`, including when the log-likelihood ratio is not integrable:
its negative part always has finite integral (`eintegral_llr_ne_bot`), so the extended integral is
then `⊤`.

## Main statements

* `coe_klDiv_eq_eintegral_llr`: `(klDiv μ ν : EReal) = ∫ᵉ x, llr μ ν x ∂μ + ν univ - μ univ` for
  `μ ≪ ν`.
* `coe_klDiv_eq_eintegral_llr_of_measure_eq`: `(klDiv μ ν : EReal) = ∫ᵉ x, llr μ ν x ∂μ` for
  `μ ≪ ν` with `μ univ = ν univ`.
-/

@[expose] public section

open MeasureTheory

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- For `μ ≪ ν` finite measures, the Kullback-Leibler divergence is the extended integral of the
log-likelihood ratio, plus `ν univ - μ univ`. -/
lemma coe_klDiv_eq_eintegral_llr [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    (klDiv μ ν : EReal) = ∫ᵉ x, llr μ ν x ∂μ + ν.real .univ - μ.real .univ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_of_ac_of_integrable h_ac h_int, EReal.coe_ennreal_ofReal,
      max_eq_left (integral_llr_add_sub_measure_univ_nonneg h_ac h_int),
      eintegral_eq_integral h_int]
    norm_cast
  -- the negative part of `llr μ ν` is integrable, hence its positive part is not
  have h_top : ∫ᵉ x, llr μ ν x ∂μ = ⊤ := by
    by_contra h_ne_top
    refine h_int ?_
    simpa using (integrable_toReal_iff_eintegral_ne_bot_and_ne_top
      (f := fun x ↦ (llr μ ν x : EReal)) (by fun_prop) (ae_of_all _ fun _ ↦ EReal.coe_ne_bot _)
      (ae_of_all _ fun _ ↦ EReal.coe_ne_top _)).mpr ⟨eintegral_llr_ne_bot h_ac, h_ne_top⟩
  rw [klDiv_of_not_integrable h_int, EReal.coe_ennreal_top, h_top, EReal.top_add_coe,
    EReal.top_sub_coe]

/-- For `μ ≪ ν` finite measures with the same total mass, the Kullback-Leibler divergence is the
extended integral of the log-likelihood ratio. -/
lemma coe_klDiv_eq_eintegral_llr_of_measure_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ≪ ν) (h_univ : μ .univ = ν .univ) :
    (klDiv μ ν : EReal) = ∫ᵉ x, llr μ ν x ∂μ := by
  rw [coe_klDiv_eq_eintegral_llr h_ac, measureReal_def, measureReal_def, h_univ,
    EReal.add_sub_cancel_right]

end InformationTheory
