/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Notation
public import Statlib.Divergence.FDiv.DivFunction.OfReal
public import Statlib.Divergence.StatInfo.StatInfoFun

/-!
# The divergence functions of the statistical information

## Main definitions

* `statInfoDivFun β γ`: the `DivFunction` obtained from the hockey-stick function
  `statInfoFun β γ`.

## Main statements

* `derivAtTop_statInfoDivFun_eq`: the derivative at infinity of `statInfoDivFun β γ`.
* `measurable_lintegral_statInfoDivFun`: measurability in the parameters `(β, γ)`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory.DivFunction

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {β γ : ℝ}

/-- The `DivFunction` associated with the convex function `statInfoFun β γ`. -/
noncomputable
def statInfoDivFun (β γ : ℝ) : DivFunction :=
  DivFunction.ofReal
    (statInfoFun β γ) ((convexOn_statInfoFun β γ).subset (subset_univ _) (convex_Ioi 0))
    statInfoFun_apply_one

lemma statInfoDivFun_apply_of_ne_top {x : ℝ≥0∞} (hx : x ≠ ∞) :
    statInfoDivFun β γ x = ENNReal.ofReal (statInfoFun β γ x.toReal) :=
  DivFunction.ofReal_apply_of_continuousWithinAt continuous_statInfoFun.continuousWithinAt hx

/-- The integral of `statInfoDivFun β γ` against `ν` of the Radon-Nikodym derivative is a
measurable function of the parameters `(β, γ)`. -/
lemma measurable_lintegral_statInfoDivFun [SigmaFinite μ] [SFinite ν] :
    Measurable fun p : ℝ × ℝ ↦ ∫⁻ x, statInfoDivFun p.1 p.2 ((∂μ/∂ν) x) ∂ν := by
  have h_meas : Measurable fun q : (ℝ × ℝ) × α ↦
      ENNReal.ofReal (statInfoFun q.1.1 q.1.2 ((∂μ/∂ν) q.2).toReal) :=
    ENNReal.measurable_ofReal.comp (measurable_statInfoFun.comp
      (measurable_fst.prodMk ((Measure.measurable_rnDeriv _ _).ennreal_toReal.comp measurable_snd)))
  have h_eq (p : ℝ × ℝ) : ∫⁻ x, statInfoDivFun p.1 p.2 ((∂μ/∂ν) x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (statInfoFun p.1 p.2 ((∂μ/∂ν) x).toReal) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx
    exact statInfoDivFun_apply_of_ne_top hx
  simp_rw [h_eq]
  exact h_meas.lintegral_prod_right'

section derivAtTop

lemma derivAtTop_statInfoDivFun :
    (statInfoDivFun β γ).derivAtTop = (derivAtTop (statInfoFun β γ)).toENNReal :=
  DivFunction.derivAtTop_ofReal

lemma derivAtTop_statInfoDivFun_of_nonneg_of_le (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (statInfoDivFun β γ).derivAtTop = 0 := by
  rw [derivAtTop_statInfoDivFun, derivAtTop_statInfoFun_of_nonneg_of_le hβ hγ,
    EReal.toENNReal_zero]

lemma derivAtTop_statInfoDivFun_of_nonneg_of_gt (hβ : 0 ≤ β) (hγ : γ > β) :
    (statInfoDivFun β γ).derivAtTop = ENNReal.ofReal β := by
  rw [derivAtTop_statInfoDivFun, derivAtTop_statInfoFun_of_nonneg_of_gt hβ hγ,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma derivAtTop_statInfoDivFun_of_nonpos_of_le (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (statInfoDivFun β γ).derivAtTop = ENNReal.ofReal (-β) := by
  rw [derivAtTop_statInfoDivFun, derivAtTop_statInfoFun_of_nonpos_of_le hβ hγ, ← EReal.coe_neg,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma derivAtTop_statInfoDivFun_of_nonpos_of_gt (hβ : β ≤ 0) (hγ : γ > β) :
    (statInfoDivFun β γ).derivAtTop = 0 := by
  rw [derivAtTop_statInfoDivFun, derivAtTop_statInfoFun_of_nonpos_of_gt hβ hγ,
    EReal.toENNReal_zero]

lemma derivAtTop_statInfoDivFun_eq :
    (statInfoDivFun β γ).derivAtTop
      = if 0 ≤ β then (if γ ≤ β then 0 else ENNReal.ofReal β)
        else if γ ≤ β then ENNReal.ofReal (-β) else 0 := by
  by_cases hβ : 0 ≤ β <;> by_cases hγ : γ ≤ β <;> simp [derivAtTop_statInfoDivFun_of_nonneg_of_le,
    derivAtTop_statInfoDivFun_of_nonneg_of_gt, derivAtTop_statInfoDivFun_of_nonpos_of_le,
    derivAtTop_statInfoDivFun_of_nonpos_of_gt, hβ, hγ, lt_of_not_ge, le_of_lt (lt_of_not_ge _)]

lemma derivAtTop_statInfoDivFun_ne_top (β γ : ℝ) :
    (statInfoDivFun β γ).derivAtTop ≠ ∞ := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_gt γ β with (hγ | hγ) <;>
    simp [derivAtTop_statInfoDivFun_of_nonneg_of_le, derivAtTop_statInfoDivFun_of_nonneg_of_gt,
      derivAtTop_statInfoDivFun_of_nonpos_of_le, derivAtTop_statInfoDivFun_of_nonpos_of_gt, hβ, hγ]

end derivAtTop

end ProbabilityTheory
