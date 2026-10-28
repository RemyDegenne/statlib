/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.Renyi.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral

/-!
# Variational formula for the Rényi divergence

For probability measures `μ`, `ν` and `a ∈ (0, 1)`, the Rényi divergence of order `a` is given by
the variational formula `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))`, where the
infimum is over probability measures `ξ`.

The infimum is attained at the tilted measure `renyiMeasure a μ ν`, whose density with respect to
`μ + ν` is proportional to `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)`: for `ξ ≪ μ` and `ξ ≪ ν`,
the log-likelihood ratios satisfy
`a * llr ξ μ + (1 - a) * llr ξ ν = llr ξ (renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)` almost
everywhere, hence
`a * KL(ξ, μ) + (1 - a) * KL(ξ, ν) = KL(ξ, renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`.

## Main definitions

* `renyiMeasure a μ ν`: the tilted measure with density
  `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a) * exp ((1 - a) * Rₐ(μ, ν))` with respect to
  `μ + ν`.

## Main statements

* `isProbabilityMeasure_renyiMeasure`: for probability measures that are not mutually singular and
  `a ∈ (0, 1)`, `renyiMeasure a μ ν` is a probability measure.
* `mul_klDiv_add_mul_klDiv`: for `ξ ≪ μ` and `ξ ≪ ν`,
  `a * KL(ξ, μ) + (1 - a) * KL(ξ, ν) = KL(ξ, renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`.
* `mul_renyiDiv_eq_iInf_klDiv`: the variational formula
  `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))`.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), Theorem 30.

The definition of `renyiMeasure` is adapted from the testing-lower-bounds project of Rémy Degenne
and Lorenzo Luccioli (https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α} {a : ℝ}

section RenyiMeasure

/-- Density of the Rényi measure `renyiMeasure a μ ν` with respect to `μ + ν`. -/
noncomputable
def renyiDensity (a : ℝ) (μ ν : Measure α) (x : α) : ℝ≥0∞ :=
  ((∂μ/∂(μ + ν)) x) ^ a * ((∂ν/∂(μ + ν)) x) ^ (1 - a)
    * ENNReal.ofReal (exp (- (a - 1) * (renyiDiv a μ ν).toReal))

/-- Tilted measure of `μ` with respect to `ν` parametrized by `a`. For probability measures `μ`
and `ν` and `a ∈ (0, 1)` with `μ` and `ν` not mutually singular, its density with respect to
`μ + ν` is `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)` divided by the total mass of that
function. -/
noncomputable
def renyiMeasure (a : ℝ) (μ ν : Measure α) : Measure α :=
  (μ + ν).withDensity (renyiDensity a μ ν)

@[fun_prop]
lemma measurable_renyiDensity (a : ℝ) (μ ν : Measure α) : Measurable (renyiDensity a μ ν) := by
  unfold renyiDensity
  fun_prop

lemma renyiMeasure_absolutelyContinuous_add (a : ℝ) (μ ν : Measure α) :
    renyiMeasure a μ ν ≪ μ + ν :=
  withDensity_absolutelyContinuous _ _

lemma rnDeriv_renyiMeasure (a : ℝ) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (renyiMeasure a μ ν).rnDeriv (μ + ν) =ᵐ[μ + ν] renyiDensity a μ ν :=
  Measure.rnDeriv_withDensity _ (measurable_renyiDensity a μ ν)

lemma sigmaFinite_renyiMeasure [SigmaFinite μ] [SigmaFinite ν] (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SigmaFinite (renyiMeasure a μ ν) := by
  refine SigmaFinite.withDensity_of_ne_top ?_
  filter_upwards [Measure.rnDeriv_lt_top μ (μ + ν), Measure.rnDeriv_lt_top ν (μ + ν)]
    with x hp hq
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ha0 hp.ne)
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr ha1) hq.ne)) ENNReal.ofReal_ne_top

/-- For `0 < a`, `renyiMeasure a μ ν ≪ μ`. -/
lemma renyiMeasure_absolutelyContinuous_left (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (ha0 : 0 < a) :
    renyiMeasure a μ ν ≪ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hμs ↦ ?_
  rw [← Measure.setLIntegral_rnDeriv' (Measure.AbsolutelyContinuous.rfl.add_right ν) hs,
    lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _), EventuallyEq,
    ae_restrict_iff' hs] at hμs
  rw [renyiMeasure, withDensity_apply _ hs, lintegral_eq_zero_iff (measurable_renyiDensity a μ ν),
    EventuallyEq, ae_restrict_iff' hs]
  filter_upwards [hμs] with x hx hxs
  simp [renyiDensity, hx hxs, ENNReal.zero_rpow_of_pos ha0]

/-- For `a < 1`, `renyiMeasure a μ ν ≪ ν`. -/
lemma renyiMeasure_absolutelyContinuous_right (μ : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (ha1 : a < 1) :
    renyiMeasure a μ ν ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  rw [← Measure.setLIntegral_rnDeriv' (Measure.AbsolutelyContinuous.rfl.add_right' μ) hs,
    lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _), EventuallyEq,
    ae_restrict_iff' hs] at hνs
  rw [renyiMeasure, withDensity_apply _ hs, lintegral_eq_zero_iff (measurable_renyiDensity a μ ν),
    EventuallyEq, ae_restrict_iff' hs]
  filter_upwards [hνs] with x hx hxs
  simp [renyiDensity, hx hxs, ENNReal.zero_rpow_of_pos (sub_pos.mpr ha1)]

/-- A measure absolutely continuous with respect to both `μ` and `ν` is absolutely continuous with
respect to `renyiMeasure a μ ν`. -/
lemma absolutelyContinuous_renyiMeasure (a : ℝ) [SigmaFinite μ] [SigmaFinite ν] (hξμ : ξ ≪ μ)
    (hξν : ξ ≪ ν) :
    ξ ≪ renyiMeasure a μ ν := by
  have hξ : ξ ≪ μ + ν := hξμ.add_right ν
  have h_ne_zero : ∀ᵐ x ∂ξ, renyiDensity a μ ν x ≠ 0 := by
    filter_upwards [hξμ (Measure.rnDeriv_pos (Measure.AbsolutelyContinuous.rfl.add_right ν)),
      hξν (Measure.rnDeriv_pos (Measure.AbsolutelyContinuous.rfl.add_right' μ)),
      hξ (Measure.rnDeriv_lt_top μ (μ + ν)), hξ (Measure.rnDeriv_lt_top ν (μ + ν))]
      with x hp hq hp_top hq_top
    exact mul_ne_zero (mul_ne_zero (ENNReal.rpow_pos hp hp_top.ne).ne'
      (ENNReal.rpow_pos hq hq_top.ne).ne') (ENNReal.ofReal_pos.mpr (exp_pos _)).ne'
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
  rw [renyiMeasure, withDensity_apply _ hs, lintegral_eq_zero_iff (measurable_renyiDensity a μ ν),
    EventuallyEq, ae_restrict_iff' hs] at h0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hξ h0, h_ne_zero] with x hx h_ne hxs
  exact h_ne (hx hxs)

/-- For probability measures that are not mutually singular and `a ∈ (0, 1)`, the tilted measure
`renyiMeasure a μ ν` is a probability measure. -/
lemma isProbabilityMeasure_renyiMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    IsProbabilityMeasure (renyiMeasure a μ ν) := by
  constructor
  set Z := ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν with hZ
  have hZ_pos : 0 < Z := (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha0.ne'
    (integrable_rpow_rnDeriv_of_lt_one ha0.le ha1)).mpr h_ms
  have h_exp : exp (-(a - 1) * (renyiDiv a μ ν).toReal) = Z⁻¹ := by
    rw [toReal_renyiDiv_of_lt_one ha0 ha1 h_ms]
    simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero, ← hZ]
    rw [← mul_assoc, neg_mul, mul_inv_cancel₀ (sub_ne_zero.mpr ha1.ne), neg_one_mul, exp_neg,
      exp_log hZ_pos]
  have h_int : ∫⁻ x, (μ.rnDeriv ν x) ^ a ∂ν = ENNReal.ofReal Z := by
    rw [hZ, ofReal_integral_eq_lintegral_ofReal (integrable_rpow_rnDeriv_of_lt_one ha0.le ha1)
      (ae_of_all _ fun _ ↦ by positivity)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx_top
    rw [ENNReal.toReal_rpow,
      ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg ha0.le hx_top.ne)]
  rw [renyiMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [renyiDensity]
  rw [lintegral_mul_const _ (by fun_prop),
    lintegral_rpow_rnDeriv_add_mul_rpow_rnDeriv_add ha0.le ha1, h_int, h_exp,
    ← ENNReal.ofReal_mul hZ_pos.le, mul_inv_cancel₀ hZ_pos.ne', ENNReal.ofReal_one]

end RenyiMeasure

section Variational

/-- For `ξ ≪ μ` and `ξ ≪ ν`, the log-likelihood ratios satisfy
`a * llr ξ μ + (1 - a) * llr ξ ν = llr ξ (renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`,
`ξ`-almost everywhere. -/
lemma mul_llr_add_mul_llr_ae_eq [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, a * llr ξ μ x + (1 - a) * llr ξ ν x
      = llr ξ (renyiMeasure a μ ν) x + (1 - a) * (renyiDiv a μ ν).toReal := by
  have := sigmaFinite_renyiMeasure (μ := μ) (ν := ν) ha0 ha1
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hξ : ξ ≪ μ + ν := hξμ.add_right ν
  have hξR : ξ ≪ renyiMeasure a μ ν := absolutelyContinuous_renyiMeasure a hξμ hξν
  filter_upwards [hξμ.ae_le (Measure.rnDeriv_eq_div hξ hμ),
    hξν.ae_le (Measure.rnDeriv_eq_div hξ hν),
    hξR.ae_le (Measure.rnDeriv_eq_div hξ (renyiMeasure_absolutelyContinuous_add a μ ν)),
    hξ.ae_le (rnDeriv_renyiMeasure a μ ν), Measure.rnDeriv_pos hξ,
    hξ.ae_le (Measure.rnDeriv_lt_top ξ (μ + ν)), hξμ.ae_le (Measure.rnDeriv_pos hμ),
    hξ.ae_le (Measure.rnDeriv_lt_top μ (μ + ν)), hξν.ae_le (Measure.rnDeriv_pos hν),
    hξ.ae_le (Measure.rnDeriv_lt_top ν (μ + ν))]
    with x h1 h2 h3 h4 hr hr_top hp hp_top hq hq_top
  have hr' : 0 < (ξ.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_pos hr.ne' hr_top.ne
  have hp' : 0 < (μ.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_pos hp.ne' hp_top.ne
  have hq' : 0 < (ν.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_pos hq.ne' hq_top.ne
  have hpa : 0 < (μ.rnDeriv (μ + ν) x).toReal ^ a := rpow_pos_of_pos hp' a
  have hqa : 0 < (ν.rnDeriv (μ + ν) x).toReal ^ (1 - a) := rpow_pos_of_pos hq' (1 - a)
  simp only [llr, h1, h2, h3, h4, renyiDensity, ENNReal.toReal_div, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (exp_pos _).le]
  rw [log_div hr'.ne' hp'.ne', log_div hr'.ne' hq'.ne',
    log_div hr'.ne' (mul_pos (mul_pos hpa hqa) (exp_pos _)).ne',
    log_mul (mul_pos hpa hqa).ne' (exp_pos _).ne', log_mul hpa.ne' hqa.ne', log_rpow hp',
    log_rpow hq', log_exp]
  ring

/-- For `ξ ≪ μ` and `ξ ≪ ν` with `ξ` a probability measure, the extended integrals of the
log-likelihood ratios satisfy
`a * ∫ llr ξ μ + (1 - a) * ∫ llr ξ ν = ∫ llr ξ (renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`. -/
lemma mul_eintegral_llr_add_mul_eintegral_llr [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsProbabilityMeasure ξ] (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν) :
    (a : EReal) * ∫ᵉ x, llr ξ μ x ∂ξ + ((1 - a : ℝ) : EReal) * ∫ᵉ x, llr ξ ν x ∂ξ
      = ∫ᵉ x, llr ξ (renyiMeasure a μ ν) x ∂ξ + ((1 - a) * (renyiDiv a μ ν).toReal : ℝ) := by
  have ha1' : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have coe_mul_ne_bot {c : ℝ} (hc : 0 ≤ c) {x : EReal} (hx : x ≠ ⊥) : (c : EReal) * x ≠ ⊥ :=
    (EReal.mul_ne_bot _ _).mpr ⟨.inl (EReal.coe_ne_bot c), .inr hx, .inl (EReal.coe_ne_top c),
      .inl (EReal.coe_nonneg.mpr hc)⟩
  have h_bot_μ : ∫ᵉ x, (a : EReal) * llr ξ μ x ∂ξ ≠ ⊥ := by
    rw [eintegral_real_const_mul_of_nonneg ha0]
    exact coe_mul_ne_bot ha0 (eintegral_llr_ne_bot hξμ)
  have h_bot_ν : ∫ᵉ x, ((1 - a : ℝ) : EReal) * llr ξ ν x ∂ξ ≠ ⊥ := by
    rw [eintegral_real_const_mul_of_nonneg ha1']
    exact coe_mul_ne_bot ha1' (eintegral_llr_ne_bot hξν)
  calc (a : EReal) * ∫ᵉ x, llr ξ μ x ∂ξ + ((1 - a : ℝ) : EReal) * ∫ᵉ x, llr ξ ν x ∂ξ
  _ = ∫ᵉ x, (a : EReal) * llr ξ μ x + ((1 - a : ℝ) : EReal) * llr ξ ν x ∂ξ := by
    rw [eintegral_add (by fun_prop) (by fun_prop) (eintegrable_of_eintegral_ne_bot h_bot_ν)
      (.inl h_bot_μ) (.inr h_bot_ν), eintegral_real_const_mul_of_nonneg ha0,
      eintegral_real_const_mul_of_nonneg ha1']
  _ = ∫ᵉ x, llr ξ (renyiMeasure a μ ν) x + ((1 - a) * (renyiDiv a μ ν).toReal : ℝ) ∂ξ := by
    refine eintegral_congr_ae ?_
    filter_upwards [mul_llr_add_mul_llr_ae_eq ha0 ha1 hξμ hξν] with x hx
    exact_mod_cast hx
  _ = ∫ᵉ x, llr ξ (renyiMeasure a μ ν) x ∂ξ + ((1 - a) * (renyiDiv a μ ν).toReal : ℝ) := by
    have h_const : ∫ᵉ _, (((1 - a) * (renyiDiv a μ ν).toReal : ℝ) : EReal) ∂ξ
        = ((1 - a) * (renyiDiv a μ ν).toReal : ℝ) := by
      rw [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
    rw [eintegral_add' (by fun_prop) (by fun_prop) (by rw [h_const]; exact EReal.coe_ne_top _)
      (by rw [h_const]; exact EReal.coe_ne_bot _), h_const]

/-- For probability measures `ξ ≪ μ` and `ξ ≪ ν` and `a ∈ (0, 1)`,
`a * KL(ξ, μ) + (1 - a) * KL(ξ, ν) = KL(ξ, renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`. -/
theorem mul_klDiv_add_mul_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] (ha0 : 0 < a) (ha1 : a < 1) (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν) :
    ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν
      = klDiv ξ (renyiMeasure a μ ν) + ENNReal.ofReal (1 - a) * renyiDiv a μ ν := by
  have h_ms : ¬ μ ⟂ₘ ν := fun h ↦ IsProbabilityMeasure.ne_zero ξ
    (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hξν
      (h.mono_ac hξμ Measure.AbsolutelyContinuous.rfl))
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  have h_top : renyiDiv a μ ν ≠ ∞ :=
    (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).not.mpr h_ms
  rw [← EReal.coe_ennreal_eq_coe_ennreal_iff]
  simp only [EReal.coe_ennreal_add, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left ha0.le, max_eq_left (sub_nonneg.mpr ha1.le)]
  rw [coe_klDiv_eq_eintegral_llr_of_measure_eq hξμ (by simp),
    coe_klDiv_eq_eintegral_llr_of_measure_eq hξν (by simp),
    coe_klDiv_eq_eintegral_llr_of_measure_eq (absolutelyContinuous_renyiMeasure a hξμ hξν)
      (by simp),
    mul_eintegral_llr_add_mul_eintegral_llr ha0.le ha1.le hξμ hξν, ← EReal.coe_ennreal_toReal h_top,
    EReal.coe_mul]

/-- **Variational formula** for the Rényi divergence: for probability measures `μ`, `ν` and
`a ∈ (0, 1)`, `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))` over probability
measures `ξ`. The infimum is attained at `renyiMeasure a μ ν` if `μ` and `ν` are not mutually
singular. -/
theorem mul_renyiDiv_eq_iInf_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ha0 : 0 < a)
    (ha1 : a < 1) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      = ⨅ (ξ : Measure α) (_ : IsProbabilityMeasure ξ),
          ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν := by
  have ha : ENNReal.ofReal a ≠ 0 := by simp [ha0]
  have ha' : ENNReal.ofReal (1 - a) ≠ 0 := by simp [ha1]
  -- if `ξ` is not absolutely continuous with respect to both measures, the right-hand side is `∞`
  have h_top (ξ : Measure α) (h : ¬ (ξ ≪ μ ∧ ξ ≪ ν)) :
      ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν = ∞ := by
    rw [not_and_or] at h
    rcases h with h | h
    · simp [klDiv_of_not_ac h, ENNReal.mul_top ha]
    · simp [klDiv_of_not_ac h, ENNReal.mul_top ha']
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mpr h_ms, ENNReal.mul_top ha',
      eq_comm, iInf₂_eq_top]
    refine fun ξ hξ ↦ h_top ξ fun h ↦ IsProbabilityMeasure.ne_zero ξ ?_
    exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
      (h_ms.mono_ac h.1 Measure.AbsolutelyContinuous.rfl)
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  refine le_antisymm (le_iInf₂ fun ξ hξ ↦ ?_) (iInf₂_le_of_le (renyiMeasure a μ ν) this ?_)
  · by_cases h : ξ ≪ μ ∧ ξ ≪ ν
    · rw [mul_klDiv_add_mul_klDiv ha0 ha1 h.1 h.2]
      exact le_add_self
    · rw [h_top ξ h]
      exact le_top
  · rw [mul_klDiv_add_mul_klDiv ha0 ha1 (renyiMeasure_absolutelyContinuous_left ν ha0)
      (renyiMeasure_absolutelyContinuous_right μ ha1), klDiv_self, zero_add]

end Variational

end ProbabilityTheory
