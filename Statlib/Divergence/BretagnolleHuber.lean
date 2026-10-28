/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.Conj
public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.Divergence.TotalVariation

/-!
# The Bretagnolle-Huber inequality

We prove lower bounds on f-divergences between probability measures in terms of their total
variation distance, and deduce the Bretagnolle-Huber inequality for the Kullback-Leibler divergence.

We use Mathlib's convention for the total variation distance: `tvDist μ ν ∈ [0, 2]` for probability
measures `μ, ν`, and the bounds are stated in terms of `tvDist μ ν / 2 ∈ [0, 1]`.

## Main statements

* `apply_one_add_etvDist_div_two_add_apply_one_sub_le_fDiv`: for probability measures,
  `f (1 + etvDist μ ν / 2) + f (1 - etvDist μ ν / 2) ≤ fDiv f μ ν`.
* `conj_one_add_etvDist_div_two_add_conj_one_sub_le_fDiv`: the same bound for the conjugate
  function `f.conj`.
* `neg_log_one_sub_tvDist_div_two_sq_le_klDiv`: the **Bretagnolle-Huber inequality**
  `-log (1 - (tvDist μ ν / 2) ^ 2) ≤ klDiv μ ν`.
* `exp_neg_klDiv_le_one_sub_tvDist_div_two_sq`, `exp_neg_klDiv_le_two_sub_tvDist`: exponential forms
  of the Bretagnolle-Huber inequality, for `klDiv μ ν ≠ ∞`.

## References

* J. Bretagnolle and C. Huber, *Estimation des densités : risque minimax*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 47 (1979).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {f : DivFunction}

/-- **Bretagnolle-Huber** type lower bound on an f-divergence in terms of the total variation
distance. -/
theorem apply_one_add_etvDist_div_two_add_apply_one_sub_le_fDiv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    f (1 + etvDist μ ν / 2) + f (1 - etvDist μ ν / 2) ≤ fDiv f μ ν := by
  set T := etvDist μ ν / 2
  have hT : ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = T := lintegral_one_sub_rnDeriv_eq_etvDist_div_two (by simp)
  have hT_ne_top : T ≠ ∞ := ENNReal.div_ne_top (etvDist_ne_top μ ν) two_ne_zero
  have hr : Measurable (∂μ/∂ν) := Measure.measurable_rnDeriv μ ν
  -- We split `∂μ/∂ν` into `max (∂μ/∂ν) 1` and `min (∂μ/∂ν) 1`, and apply Jensen's inequality to
  -- each part. The integrals of the two parts are `1 + T` (with the singular part of `μ`) and
  -- `1 - T`.
  have h_min : ∫⁻ x, min ((∂μ/∂ν) x) 1 ∂ν = 1 - T := by
    have h_eq x : min ((∂μ/∂ν) x) 1 = 1 - (1 - (∂μ/∂ν) x) := by
      rcases le_total ((∂μ/∂ν) x) 1 with h | h
      · rw [min_eq_left h, ENNReal.sub_sub_cancel ENNReal.one_ne_top h]
      · rw [min_eq_right h, tsub_eq_zero_of_le h, tsub_zero]
    simp_rw [h_eq]
    rw [lintegral_sub (g := fun x ↦ 1 - (∂μ/∂ν) x) (measurable_const.sub hr) (hT ▸ hT_ne_top)
      (ae_of_all _ fun _ ↦ tsub_le_self), lintegral_const, measure_univ, one_mul, hT]
  have h_max : ∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν + μ.singularPart ν univ = 1 + T := by
    have h_eq x : max ((∂μ/∂ν) x) 1 = (∂μ/∂ν) x + (1 - (∂μ/∂ν) x) := by
      rcases le_total ((∂μ/∂ν) x) 1 with h | h
      · rw [max_eq_right h, add_tsub_cancel_of_le h]
      · rw [max_eq_left h, tsub_eq_zero_of_le h, add_zero]
    simp_rw [h_eq]
    rw [lintegral_add_left hr, hT, add_right_comm, add_comm (∫⁻ x, (∂μ/∂ν) x ∂ν),
      Measure.singularPart_add_lintegral_rnDeriv, measure_univ]
  have h_split x : f ((∂μ/∂ν) x) = f (max ((∂μ/∂ν) x) 1) + f (min ((∂μ/∂ν) x) 1) := by
    rcases le_total ((∂μ/∂ν) x) 1 with h | h
    · simp [max_eq_right h, min_eq_left h]
    · simp [max_eq_left h, min_eq_right h]
  have h_max_ne_top : ∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hT_ne_top⟩)
      (le_self_add.trans h_max.le)
  have h_min_ne_top : ∫⁻ x, min ((∂μ/∂ν) x) 1 ∂ν ≠ ∞ := by
    rw [h_min]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h_jensen_max := f.map_lintegral_le (hr.max measurable_const).aemeasurable h_max_ne_top
  have h_jensen_min := f.map_lintegral_le (hr.min measurable_const).aemeasurable h_min_ne_top
  rw [h_min] at h_jensen_min
  calc f (1 + T) + f (1 - T)
      = f (∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν + μ.singularPart ν univ) + f (1 - T) := by rw [h_max]
    _ ≤ f (∫⁻ x, max ((∂μ/∂ν) x) 1 ∂ν) + f.derivAtTop * μ.singularPart ν univ
        + ∫⁻ x, f (min ((∂μ/∂ν) x) 1) ∂ν := by
      gcongr
      exact f.apply_add_le _ _
    _ ≤ ∫⁻ x, f (max ((∂μ/∂ν) x) 1) ∂ν + f.derivAtTop * μ.singularPart ν univ
        + ∫⁻ x, f (min ((∂μ/∂ν) x) 1) ∂ν := by gcongr
    _ = fDiv f μ ν := by
      have h_meas : Measurable fun x ↦ f (max ((∂μ/∂ν) x) 1) :=
        f.measurable.comp (hr.max measurable_const)
      rw [fDiv, lintegral_congr (fun x ↦ h_split x), lintegral_add_left h_meas]
      ring

/-- **Bretagnolle-Huber** type lower bound on an f-divergence in terms of the total variation
distance, obtained by applying `apply_one_add_etvDist_div_two_add_apply_one_sub_le_fDiv` to
`f.conj`. For `t ≠ 0`, `f.conj t = t * f t⁻¹`. -/
theorem conj_one_add_etvDist_div_two_add_conj_one_sub_le_fDiv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    f.conj (1 + etvDist μ ν / 2) + f.conj (1 - etvDist μ ν / 2) ≤ fDiv f μ ν := by
  rw [← fDiv_conj, etvDist_comm]
  exact apply_one_add_etvDist_div_two_add_apply_one_sub_le_fDiv ν μ

/-- **Bretagnolle-Huber inequality**: `-log (1 - (tvDist μ ν / 2) ^ 2) ≤ klDiv μ ν`.
If `tvDist μ ν = 2`, the left-hand side is `0` since `Real.log 0 = 0`. -/
theorem neg_log_one_sub_tvDist_div_two_sq_le_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ENNReal.ofReal (-Real.log (1 - (tvDist μ ν / 2) ^ 2)) ≤ klDiv μ ν := by
  have h := conj_one_add_etvDist_div_two_add_conj_one_sub_le_fDiv (f := klDivFun) μ ν
  rw [← klDiv_eq_fDiv] at h
  refine le_trans ?_ h
  set t := tvDist μ ν / 2 with ht
  have hT : etvDist μ ν / 2 = ENNReal.ofReal t := by
    rw [ht, ← ofReal_tvDist, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  have ht0 : 0 ≤ t := div_nonneg tvDist_nonneg zero_le_two
  have ht1 : t ≤ 1 := by
    have := tvDist_le_add (μ := μ) (ν := ν)
    simp only [probReal_univ] at this
    linarith
  rcases ht1.lt_or_eq with ht1 | ht1
  swap
  · simp [ht1]
  rw [hT, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one ht0, ← ENNReal.ofReal_sub _ ht0,
    conj_klDivFun_ofReal (by linarith), conj_klDivFun_ofReal (by linarith),
    ← ENNReal.ofReal_add (sub_nonneg.2 (Real.log_le_sub_one_of_pos (by linarith)))
      (sub_nonneg.2 (Real.log_le_sub_one_of_pos (by linarith)))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [show 1 - t ^ 2 = (1 + t) * (1 - t) by ring, Real.log_mul (by linarith) (by linarith)]
  ring

/-- If the Kullback-Leibler divergence between probability measures is finite, then their total
variation distance is less than `2`, its maximal value. -/
lemma tvDist_lt_two_of_klDiv_ne_top {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : klDiv μ ν ≠ ∞) :
    tvDist μ ν < 2 := by
  refine (tvDist_le_add.trans_eq (by rw [probReal_univ, probReal_univ]; norm_num)).lt_of_ne
    fun h_eq ↦ h ?_
  -- if `tvDist μ ν = 2`, the lower bound contains `klDivFun.conj 0 = ∞`
  have h_conj := conj_one_add_etvDist_div_two_add_conj_one_sub_le_fDiv (f := klDivFun) μ ν
  have hT : etvDist μ ν / 2 = 1 := by
    rw [← ofReal_tvDist, h_eq, ENNReal.ofReal_ofNat,
      ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top]
  rw [hT, tsub_self, DivFunction.conj_zero, derivAtTop_klDivFun, add_top, top_le_iff,
    ← klDiv_eq_fDiv] at h_conj
  exact h_conj

/-- **Bretagnolle-Huber inequality**, exponential form: if `klDiv μ ν ≠ ∞`, then
`exp (-klDiv μ ν) ≤ 1 - (tvDist μ ν / 2) ^ 2`. -/
theorem exp_neg_klDiv_le_one_sub_tvDist_div_two_sq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : klDiv μ ν ≠ ∞) :
    Real.exp (-(klDiv μ ν).toReal) ≤ 1 - (tvDist μ ν / 2) ^ 2 := by
  have h_pos : 0 < 1 - (tvDist μ ν / 2) ^ 2 := by
    have := tvDist_lt_two_of_klDiv_ne_top h
    nlinarith [tvDist_nonneg (μ := μ) (ν := ν)]
  have h_log := neg_log_one_sub_tvDist_div_two_sq_le_klDiv μ ν
  rw [ENNReal.ofReal_le_iff_le_toReal h] at h_log
  calc Real.exp (-(klDiv μ ν).toReal)
  _ ≤ Real.exp (Real.log (1 - (tvDist μ ν / 2) ^ 2)) := by gcongr; linarith
  _ = 1 - (tvDist μ ν / 2) ^ 2 := Real.exp_log h_pos

/-- **Bretagnolle-Huber inequality**: if `klDiv μ ν ≠ ∞`, then
`exp (-klDiv μ ν) ≤ 2 - tvDist μ ν`. Since the sum of the errors `μ s + ν sᶜ` of a test is at least
`1 - tvDist μ ν / 2`, it is at least `exp (-klDiv μ ν) / 2`. -/
theorem exp_neg_klDiv_le_two_sub_tvDist (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : klDiv μ ν ≠ ∞) :
    Real.exp (-(klDiv μ ν).toReal) ≤ 2 - tvDist μ ν := by
  have h_sq := exp_neg_klDiv_le_one_sub_tvDist_div_two_sq μ ν h
  have h_lt := tvDist_lt_two_of_klDiv_ne_top h
  nlinarith [tvDist_nonneg (μ := μ) (ν := ν)]

end ProbabilityTheory
