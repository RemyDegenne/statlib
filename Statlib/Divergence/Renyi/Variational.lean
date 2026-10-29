/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.KullbackLeibler.CondKL
public import Statlib.Divergence.Renyi.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral

/-!
# The Rényi measure and the variational formula for the Rényi divergence

For probability measures `μ`, `ν` and `a ∈ (0, 1)`, the Rényi divergence of order `a` is given by
the variational formula `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))`, where the
infimum is over probability measures `ξ`.

The infimum is attained at the tilted measure `renyiMeasure a μ ν`, whose density with respect to
`μ + ν` is proportional to `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a)`: for `ξ ≪ μ` and `ξ ≪ ν`,
the log-likelihood ratios satisfy
`a * llr ξ μ + (1 - a) * llr ξ ν = llr ξ (renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)` almost
everywhere, hence
`a * KL(ξ, μ) + (1 - a) * KL(ξ, ν) = KL(ξ, renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`.
We also compute the Radon-Nikodym derivatives of the Rényi measure with respect to `μ` and `ν`, and
rephrase the variational formula as an infimum of Kullback-Leibler divergences between joint
measures on `Bool × α`.

## Main definitions

* `renyiMeasure a μ ν`: the tilted measure with density
  `(∂μ/∂(μ + ν)) ^ a * (∂ν/∂(μ + ν)) ^ (1 - a) * exp ((1 - a) * Rₐ(μ, ν))` with respect to
  `μ + ν`.

## Main statements

* `isProbabilityMeasure_renyiMeasure`: for probability measures that are not mutually singular and
  `a ∈ (0, 1)`, `renyiMeasure a μ ν` is a probability measure.
* `rnDeriv_renyiMeasure_right`: for `a ∈ [0, 1]`,
  `∂(renyiMeasure a μ ν)/∂ν = (∂μ/∂ν) ^ a * exp (-(a - 1) Rₐ(μ, ν))`, `ν`-almost everywhere.
  `rnDeriv_renyiMeasure_right_of_absolutelyContinuous` is the same formula for `a ≥ 0` and `μ ≪ ν`.
* `rnDeriv_renyiMeasure_left`: for `a ∈ [0, 1]`,
  `∂(renyiMeasure a μ ν)/∂μ = (∂ν/∂μ) ^ (1 - a) * exp (-(a - 1) Rₐ(μ, ν))`, `μ`-almost everywhere.
* `renyiMeasure_eq_withDensity`: for `a ∈ [0, 1)` or `μ ≪ ν`, the Rényi measure is
  `ν.withDensity ((∂μ/∂ν) ^ a * exp (-(a - 1) Rₐ(μ, ν)))`.
* `lintegral_renyiMeasure`: integrals with respect to the Rényi measure.
* `renyiMeasure_smul_smul`: for `c, d ∈ (0, ∞)` and `a ∈ [0, 1)` or `μ ≪ ν`,
  `renyiMeasure a (c • μ) (d • ν) = (c ^ a * d ^ (1 - a)) • renyiMeasure a μ ν`.
* `isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top`: for probability measures, `a > 0` and
  `Rₐ(μ, ν) < ∞`, the Rényi measure is a probability measure.
* `mul_klDiv_add_mul_klDiv`: for `ξ ≪ μ` and `ξ ≪ ν`,
  `a * KL(ξ, μ) + (1 - a) * KL(ξ, ν) = KL(ξ, renyiMeasure a μ ν) + (1 - a) * Rₐ(μ, ν)`.
* `mul_renyiDiv_eq_iInf_klDiv`: the variational formula
  `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))`.
* `mul_renyiDiv_eq_mul_klDiv_renyiMeasure`: for probability measures that are not mutually singular,
  the infimum is attained at the Rényi measure.
* `mul_renyiDiv_eq_iInf_klDiv_prod`: with `πₐ = (a, 1 - a)` the prior on `Bool` and
  `P = boolKernel μ ν`, `(1 - a) * Rₐ(μ, ν) = ⨅ ξ, KL(πₐ × ξ, πₐ ⊗ P)`. The infimum is attained at
  the Rényi measure (`mul_renyiDiv_eq_klDiv_prod_renyiMeasure`), and
  `klDiv_boolMeasure_prod_renyiMeasure` computes `KL(πₐ × ξ, ρ ⊗ P)` at that point for any finite
  measure `ρ` on `Bool`.

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

/-- The Rényi measure of order `1` is `μ`. -/
@[simp]
lemma renyiMeasure_one [SigmaFinite μ] [SigmaFinite ν] : renyiMeasure 1 μ ν = μ := by
  have : renyiDensity 1 μ ν = μ.rnDeriv (μ + ν) := by
    ext x
    simp [renyiDensity]
  rw [renyiMeasure, this,
    Measure.withDensity_rnDeriv_eq _ _ (Measure.AbsolutelyContinuous.rfl.add_right ν)]

/-- The Rényi measure of order `a > 0` between the zero measure and `ν` is zero. -/
@[simp]
lemma renyiMeasure_zero_left (ha : 0 < a) (ν : Measure α) : renyiMeasure a 0 ν = 0 := by
  rw [renyiMeasure, zero_add, ← withDensity_zero]
  refine withDensity_congr_ae ?_
  filter_upwards [ν.rnDeriv_zero] with x hx
  simp [renyiDensity, hx, ENNReal.zero_rpow_of_pos ha]

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

section RnDeriv

/-- Radon-Nikodym derivative of the Rényi measure with respect to `ν`:
`∂(renyiMeasure a μ ν)/∂ν = (∂μ/∂ν) ^ a * exp (-(a - 1) Rₐ(μ, ν))`, `ν`-almost everywhere. -/
lemma rnDeriv_renyiMeasure_right [SigmaFinite μ] [SigmaFinite ν] (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (renyiMeasure a μ ν).rnDeriv ν =ᵐ[ν]
      fun x ↦ (μ.rnDeriv ν x) ^ a * ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal)) := by
  have := sigmaFinite_renyiMeasure (μ := μ) (ν := ν) ha0 ha1
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  filter_upwards [Measure.rnDeriv_eq_div (renyiMeasure_absolutelyContinuous_add a μ ν) hν,
    Measure.rnDeriv_eq_div hμ hν, hν.ae_le (rnDeriv_renyiMeasure a μ ν),
    Measure.rnDeriv_pos hν, hν.ae_le (Measure.rnDeriv_lt_top ν (μ + ν))]
    with x h1 h2 h3 hq_pos hq_top
  set p := μ.rnDeriv (μ + ν) x
  set q := ν.rnDeriv (μ + ν) x
  set C := ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal))
  have hq0 : q ≠ 0 := hq_pos.ne'
  have hqa0 : q ^ a ≠ 0 := (ENNReal.rpow_pos hq_pos hq_top.ne).ne'
  have hqa_top : q ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha0 hq_top.ne
  rw [h1, h3, h2, renyiDensity, ENNReal.div_rpow_of_nonneg _ _ ha0,
    ENNReal.rpow_sub _ _ hq0 hq_top.ne, ENNReal.rpow_one]
  calc p ^ a * (q / q ^ a) * C / q = p ^ a * C * (q ^ a)⁻¹ * (q * q⁻¹) := by
        simp only [div_eq_mul_inv]; ring
  _ = p ^ a / q ^ a * C := by
        rw [ENNReal.mul_inv_cancel hq0 hq_top.ne, mul_one, div_eq_mul_inv]; ring

/-- Radon-Nikodym derivative of the Rényi measure with respect to `μ`:
`∂(renyiMeasure a μ ν)/∂μ = (∂ν/∂μ) ^ (1 - a) * exp (-(a - 1) Rₐ(μ, ν))`, `μ`-almost
everywhere. -/
lemma rnDeriv_renyiMeasure_left [SigmaFinite μ] [SigmaFinite ν] (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (renyiMeasure a μ ν).rnDeriv μ =ᵐ[μ] fun x ↦
      (ν.rnDeriv μ x) ^ (1 - a) * ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal)) := by
  have := sigmaFinite_renyiMeasure (μ := μ) (ν := ν) ha0 ha1
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have ha1' : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  filter_upwards [Measure.rnDeriv_eq_div (renyiMeasure_absolutelyContinuous_add a μ ν) hμ,
    Measure.rnDeriv_eq_div hν hμ, hμ.ae_le (rnDeriv_renyiMeasure a μ ν),
    Measure.rnDeriv_pos hμ, hμ.ae_le (Measure.rnDeriv_lt_top μ (μ + ν))]
    with x h1 h2 h3 hp_pos hp_top
  set p := μ.rnDeriv (μ + ν) x
  set q := ν.rnDeriv (μ + ν) x
  set C := ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal))
  have hp0 : p ≠ 0 := hp_pos.ne'
  have h0 : p ^ (1 - a) ≠ 0 := (ENNReal.rpow_pos hp_pos hp_top.ne).ne'
  have htop : p ^ (1 - a) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha1' hp_top.ne
  have key : p ^ a = p * (p ^ (1 - a))⁻¹ := by
    have h : p ^ (1 - a) * p ^ a = p := by
      rw [← ENNReal.rpow_add _ _ hp0 hp_top.ne, sub_add_cancel, ENNReal.rpow_one]
    calc p ^ a = (p ^ (1 - a) * p ^ a) * (p ^ (1 - a))⁻¹ := by
          rw [mul_comm (p ^ (1 - a)), mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]
    _ = p * (p ^ (1 - a))⁻¹ := by rw [h]
  rw [h1, h3, h2, renyiDensity, ENNReal.div_rpow_of_nonneg _ _ ha1', key]
  calc p * (p ^ (1 - a))⁻¹ * q ^ (1 - a) * C / p
      = q ^ (1 - a) * C * (p ^ (1 - a))⁻¹ * (p * p⁻¹) := by
        simp only [div_eq_mul_inv]; ring
  _ = q ^ (1 - a) / p ^ (1 - a) * C := by
        rw [ENNReal.mul_inv_cancel hp0 hp_top.ne, mul_one, div_eq_mul_inv]; ring

end RnDeriv

section WithDensity

/-- For `a ∈ [0, 1)` or `μ ≪ ν`, the Rényi measure is
`ν.withDensity ((∂μ/∂ν) ^ a * exp (-(a - 1) Rₐ(μ, ν)))`. -/
lemma renyiMeasure_eq_withDensity [SigmaFinite μ] [SigmaFinite ν] (ha : 0 ≤ a)
    (h : a < 1 ∨ μ ≪ ν) :
    renyiMeasure a μ ν = ν.withDensity
      (fun x ↦ ((∂μ/∂ν) x) ^ a * ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal))) := by
  rcases h with ha1 | hμν
  · have := sigmaFinite_renyiMeasure (μ := μ) (ν := ν) ha ha1.le
    rw [← Measure.withDensity_rnDeriv_eq _ ν (renyiMeasure_absolutelyContinuous_right μ ha1)]
    exact withDensity_congr_ae (rnDeriv_renyiMeasure_right ha ha1.le)
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  ext s hs
  rw [renyiMeasure, withDensity_apply _ hs, withDensity_apply _ hs,
    ← setLIntegral_rnDeriv_mul hν (by fun_prop) hs]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ + ν) hμν,
    Measure.rnDeriv_lt_top ν (μ + ν)] with x hx hq_top
  set q := ν.rnDeriv (μ + ν) x
  have hq : q ^ a * q ^ (1 - a) = q := by
    rw [← ENNReal.rpow_add_of_add_pos hq_top.ne _ _ (by simp), add_sub_cancel, ENNReal.rpow_one]
  rw [renyiDensity, ← hx, Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ ha, mul_assoc _ (q ^ a), hq]
  ring

/-- For `μ ≪ ν`, the Rényi measure is σ-finite. -/
lemma sigmaFinite_renyiMeasure_of_absolutelyContinuous [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (ha : 0 ≤ a) :
    SigmaFinite (renyiMeasure a μ ν) := by
  rw [renyiMeasure_eq_withDensity ha (.inr hμν)]
  refine SigmaFinite.withDensity_of_ne_top ?_
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ha hx.ne) ENNReal.ofReal_ne_top

/-- Radon-Nikodym derivative of the Rényi measure with respect to `ν`, for `μ ≪ ν`. -/
lemma rnDeriv_renyiMeasure_right_of_absolutelyContinuous [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (ha : 0 ≤ a) :
    (renyiMeasure a μ ν).rnDeriv ν =ᵐ[ν]
      fun x ↦ (μ.rnDeriv ν x) ^ a * ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal)) := by
  rw [renyiMeasure_eq_withDensity ha (.inr hμν)]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

/-- Integral with respect to the Rényi measure, for `a ∈ [0, 1)` or `μ ≪ ν`. -/
lemma lintegral_renyiMeasure [SigmaFinite μ] [SigmaFinite ν] (ha : 0 ≤ a) (h : a < 1 ∨ μ ≪ ν)
    {g : α → ℝ≥0∞} :
    ∫⁻ x, g x ∂(renyiMeasure a μ ν)
      = ENNReal.ofReal (exp (-(a - 1) * (renyiDiv a μ ν).toReal))
        * ∫⁻ x, ((∂μ/∂ν) x) ^ a * g x ∂ν := by
  rw [renyiMeasure_eq_withDensity ha h,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop) ?_,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · congr with x
    simp only [Pi.mul_apply]
    ring
  · filter_upwards [μ.rnDeriv_lt_top ν] with x hx
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha hx.ne) ENNReal.ofReal_lt_top

/-- Scaling the measures scales the Rényi measure: for `c, d ∈ (0, ∞)` and `a ∈ [0, 1)` or `μ ≪ ν`,
`renyiMeasure a (c • μ) (d • ν) = (c ^ a * d ^ (1 - a)) • renyiMeasure a μ ν`. -/
lemma renyiMeasure_smul_smul [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha : 0 ≤ a)
    (h : a < 1 ∨ μ ≪ ν) {c d : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (hd0 : d ≠ 0) (hd : d ≠ ∞) :
    renyiMeasure a (c • μ) (d • ν) = (c ^ a * d ^ (1 - a)) • renyiMeasure a μ ν := by
  have := μ.smul_finite hc
  have := ν.smul_finite hd
  have h' : a < 1 ∨ c • μ ≪ d • ν := h.imp_right fun hμν ↦
    Measure.smul_absolutelyContinuous.trans (hμν.trans (Measure.absolutelyContinuous_smul hd0))
  -- `∂(c • μ)/∂(d • ν) = d⁻¹ * c * ∂μ/∂ν`, `ν`-almost everywhere
  have h_eq : (fun x ↦ (c • μ).rnDeriv (d • ν) x ^ a)
      =ᵐ[ν] fun x ↦ (d⁻¹ * c) ^ a * (∂μ/∂ν) x ^ a := by
    filter_upwards [Measure.rnDeriv_smul_right_of_ne_top' (c • μ) ν hd0 hd,
      Measure.rnDeriv_smul_left_of_ne_top' μ ν hc] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_rpow_of_nonneg _ _ ha]
  have h_const : d * (d⁻¹ * c) ^ a = c ^ a * d ^ (1 - a) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.inv_rpow, ENNReal.rpow_sub _ _ hd0 hd,
      ENNReal.rpow_one, div_eq_mul_inv]
    ring
  rw [renyiMeasure_eq_withDensity ha h', renyiMeasure_eq_withDensity ha h,
    renyiDiv_smul_smul ha hc0 hc hd0 hd, withDensity_smul_measure, ← h_const, ← smul_smul,
    ← withDensity_smul' _ _ (ENNReal.rpow_ne_top_of_nonneg ha
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hd0) hc))]
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [h_eq] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, hx, mul_assoc]

/-- For probability measures and `a > 0` with `Rₐ(μ, ν) < ∞`, the Rényi measure is a probability
measure. -/
lemma isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ha : 0 < a) (h : renyiDiv a μ ν ≠ ∞) :
    IsProbabilityMeasure (renyiMeasure a μ ν) := by
  rcases lt_trichotomy a 1 with ha1 | rfl | ha1
  · exact isProbabilityMeasure_renyiMeasure ha ha1
      fun h_ms ↦ h (renyiDiv_of_mutuallySingular ha.le h_ms)
  · rw [renyiMeasure_one]
    infer_instance
  obtain ⟨h_int, hμν⟩ := (renyiDiv_ne_top_iff_of_one_lt ha1).mp h
  have h_pos := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha h
  have h_lint : ∫⁻ x, ((∂μ/∂ν) x) ^ a ∂ν = ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
    rw [integral_rpow_rnDeriv_eq_toReal_lintegral ha.le,
      ENNReal.ofReal_toReal ((integrable_rpow_rnDeriv_iff_lintegral_ne_top ha.le).mp h_int)]
  constructor
  rw [← setLIntegral_one, Measure.restrict_univ, lintegral_renyiMeasure ha.le (.inr hμν)]
  simp only [mul_one]
  rw [h_lint, ← ENNReal.ofReal_mul (exp_pos _).le,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha ha1.ne' h, ← mul_assoc, neg_mul,
    mul_inv_cancel₀ (sub_ne_zero.mpr ha1.ne'), neg_one_mul, exp_neg, exp_log h_pos,
    inv_mul_cancel₀ h_pos.ne', ENNReal.ofReal_one]

end WithDensity

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

/-- For probability measures, `a ∈ (0, 1)` and every probability measure `ξ`,
`(1 - a) * Rₐ(μ, ν) ≤ a * KL(ξ, μ) + (1 - a) * KL(ξ, ν)`. This is the easy half of the variational
formula `mul_renyiDiv_eq_iInf_klDiv`. -/
lemma mul_renyiDiv_le_mul_klDiv_add_mul_klDiv (μ ν ξ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] (ha0 : 0 < a) (ha1 : a < 1) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      ≤ ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν :=
  (mul_renyiDiv_eq_iInf_klDiv ha0 ha1).trans_le (iInf₂_le ξ ‹_›)

/-- For probability measures `μ`, `ν` that are not mutually singular and `a ∈ (0, 1)`,
`(1 - a) * Rₐ(μ, ν) = a * KL(μ^(a, ν), μ) + (1 - a) * KL(μ^(a, ν), ν)`, in which
`μ^(a, ν) = renyiMeasure a μ ν`. -/
theorem mul_renyiDiv_eq_mul_klDiv_renyiMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      = ENNReal.ofReal a * klDiv (renyiMeasure a μ ν) μ
        + ENNReal.ofReal (1 - a) * klDiv (renyiMeasure a μ ν) ν := by
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  rw [mul_klDiv_add_mul_klDiv ha0 ha1 (renyiMeasure_absolutelyContinuous_left ν ha0)
    (renyiMeasure_absolutelyContinuous_right μ ha1), klDiv_self, zero_add]

/-- For probability measures that are not mutually singular and `a ∈ (0, 1)`, the
Kullback-Leibler divergence from the tilted measure `renyiMeasure a μ ν` to `μ` is finite. -/
lemma klDiv_renyiMeasure_left_ne_top [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    klDiv (renyiMeasure a μ ν) μ ≠ ∞ := by
  have h := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 1 - a))
    (mt (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mp h_ms)
  rw [mul_renyiDiv_eq_mul_klDiv_renyiMeasure ha0 ha1 h_ms] at h
  exact fun h' ↦ (ENNReal.add_ne_top.mp h).1 (by rw [h', ENNReal.mul_top (by simpa using ha0)])

/-- For probability measures that are not mutually singular and `a ∈ (0, 1)`, the
Kullback-Leibler divergence from the tilted measure `renyiMeasure a μ ν` to `ν` is finite. -/
lemma klDiv_renyiMeasure_right_ne_top [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    klDiv (renyiMeasure a μ ν) ν ≠ ∞ := by
  have h := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 1 - a))
    (mt (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mp h_ms)
  rw [mul_renyiDiv_eq_mul_klDiv_renyiMeasure ha0 ha1 h_ms] at h
  exact fun h' ↦ (ENNReal.add_ne_top.mp h).2 (by rw [h', ENNReal.mul_top (by simpa using ha1)])

/-- **Variational formula** for the Rényi divergence, as an infimum of Kullback-Leibler divergences
between joint measures: let `πₐ = boolMeasure a (1 - a)` be the prior on `Bool` and
`P = boolKernel μ ν` the kernel with `P false = μ` and `P true = ν`. Then for `a ∈ (0, 1)`,
`(1 - a) * Rₐ(μ, ν) = ⨅ ξ, KL(πₐ × ξ, πₐ ⊗ₘ P)` over probability measures `ξ`. -/
theorem mul_renyiDiv_eq_iInf_klDiv_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      = ⨅ (ξ : Measure α) (_ : IsProbabilityMeasure ξ),
          klDiv ((Measure.boolMeasure (ENNReal.ofReal a) (ENNReal.ofReal (1 - a))).prod ξ)
            (Measure.boolMeasure (ENNReal.ofReal a) (ENNReal.ofReal (1 - a))
              ⊗ₘ Kernel.boolKernel μ ν) := by
  rw [mul_renyiDiv_eq_iInf_klDiv ha0 ha1]
  congr with ξ
  congr with hξ
  rw [klDiv_prod_compProd_boolKernel, Measure.boolMeasure_apply_false,
    Measure.boolMeasure_apply_true]

/-- The infimum in `mul_renyiDiv_eq_iInf_klDiv_prod` is attained at the Rényi measure
`renyiMeasure a μ ν`. -/
lemma mul_renyiDiv_eq_klDiv_prod_renyiMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      = klDiv ((Measure.boolMeasure (ENNReal.ofReal a) (ENNReal.ofReal (1 - a))).prod
          (renyiMeasure a μ ν))
        (Measure.boolMeasure (ENNReal.ofReal a) (ENNReal.ofReal (1 - a))
          ⊗ₘ Kernel.boolKernel μ ν) := by
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  rw [klDiv_prod_compProd_boolKernel, Measure.boolMeasure_apply_false,
    Measure.boolMeasure_apply_true, mul_renyiDiv_eq_mul_klDiv_renyiMeasure ha0 ha1 h_ms]

/-- For `πₐ = (a, 1 - a)`, the Rényi measure `ξ = renyiMeasure a μ ν` and a finite measure `ρ` on
`Bool`, `KL(πₐ × ξ, ρ ⊗ₘ boolKernel μ ν) = KL(πₐ, ρ) + (1 - a) * Rₐ(μ, ν)`. For `ρ = πₐ`, this is
`mul_renyiDiv_eq_klDiv_prod_renyiMeasure`. -/
lemma klDiv_boolMeasure_prod_renyiMeasure (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ρ : Measure Bool) [IsFiniteMeasure ρ] (ha0 : 0 < a) (ha1 : a < 1)
    (h_ms : ¬ μ ⟂ₘ ν) :
    klDiv ((Measure.boolMeasure (.ofReal a) (.ofReal (1 - a))).prod (renyiMeasure a μ ν))
        (ρ ⊗ₘ Kernel.boolKernel μ ν)
      = klDiv (Measure.boolMeasure (.ofReal a) (.ofReal (1 - a))) ρ
        + ENNReal.ofReal (1 - a) * renyiDiv a μ ν := by
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  rw [mul_renyiDiv_eq_klDiv_prod_renyiMeasure ha0 ha1 h_ms, ← Measure.compProd_const,
    klDiv_compProd_eq_add_condKL, ← condKL]

end Variational

end ProbabilityTheory
