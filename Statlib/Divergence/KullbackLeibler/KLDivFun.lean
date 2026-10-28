/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.Divergence.FDiv.DivFunction.Conj
public import Statlib.Divergence.FDiv.DivFunction.OfReal

/-!
# The divergence function of the Kullback-Leibler divergence

`klDivFun` is the `DivFunction` obtained from Mathlib's `InformationTheory.klFun`,
`x ↦ x * log x + 1 - x`.

## Main definitions

* `klDivFun`: the `DivFunction` of the Kullback-Leibler divergence.

## Main statements

* `klDivFun_apply`: `klDivFun x = ENNReal.ofReal (x * log x + 1 - x)` for `x ≠ ∞`.
* `derivAtTop_klDivFun`: the derivative at infinity of `klDivFun` is `∞`.
* `strictConvexOn_klDivFun`: the real function of `klDivFun` is strictly convex on `[0, ∞)`.
* `conj_klDivFun_ofReal`: the conjugate of `klDivFun` is `s ↦ s - 1 - log s` on `(0, ∞)`.
* `lintegral_klDivFun_rnDeriv`: `∫⁻ x, klDivFun (∂μ/∂ν x) ∂ν = ∫⁻ x, ofReal (klFun (∂μ/∂ν x)) ∂ν`,
  which is used to identify `fDiv klDivFun` with Mathlib's `klDiv`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section KLDivFun

/-- The `DivFunction` of the Kullback-Leibler divergence, `x ↦ x * log x + 1 - x` on `[0, ∞)`. -/
noncomputable
def klDivFun : DivFunction := DivFunction.ofReal klFun convexOn_Ioi_klFun klFun_one

@[simp] lemma klDivFun_apply_top : klDivFun ∞ = ∞ := by
  rw [klDivFun, DivFunction.ofReal_apply_top_of_tendsto_atTop]
  exact tendsto_klFun_atTop

lemma klDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) :
    klDivFun x = ENNReal.ofReal (x.toReal * log x.toReal + 1 - x.toReal) := by
  by_cases hx0 : x = 0
  · rw [klDivFun, hx0, DivFunction.ofReal_apply_zero_of_continuousWithinAt]
    · simp [klFun_zero]
    · exact continuous_klFun.continuousWithinAt
  · rw [klDivFun, DivFunction.ofReal_apply hx0 hx, klFun_apply]

@[simp]
lemma klDivFun_zero : klDivFun 0 = 1 := by simp [klDivFun_apply ENNReal.zero_ne_top]

@[simp]
lemma klDivFun_realFun_apply {x : ℝ} (hx : 0 ≤ x) : klDivFun.realFun x = x * log x + 1 - x := by
  rw [DivFunction.realFun, klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal]
  exact klFun_nonneg hx

@[simp] lemma derivAtTop_klDivFun : klDivFun.derivAtTop = ∞ :=
  DivFunction.derivAtTop_ofReal_of_tendsto_atTop tendsto_rightDeriv_klFun_atTop

lemma eqOn_klDivFun_realFun : EqOn klDivFun.realFun (fun x ↦ x * log x + 1 - x) (Ici 0) :=
  fun _ hx ↦ klDivFun_realFun_apply hx

lemma strictConvexOn_klDivFun : StrictConvexOn ℝ (Ici 0) klDivFun.realFun :=
  StrictConvexOn.congr strictConvexOn_klFun eqOn_klDivFun_realFun.symm

lemma lintegral_klDivFun_rnDeriv [SigmaFinite μ] :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  refine lintegral_congr_ae ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  rw [klDivFun_apply hx, klFun_apply]

/-- The conjugate of `klDivFun` is `s ↦ s - 1 - log s` on `(0, ∞)`. -/
lemma conj_klDivFun_ofReal {s : ℝ} (hs : 0 < s) :
    klDivFun.conj (ENNReal.ofReal s) = ENNReal.ofReal (s - 1 - log s) := by
  rw [DivFunction.conj_of_ne_zero (ENNReal.ofReal_pos.2 hs).ne', ← ENNReal.ofReal_inv_of_pos hs,
    klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (inv_nonneg.2 hs.le),
    ← ENNReal.ofReal_mul hs.le, log_inv]
  congr 1
  field_simp
  ring

end KLDivFun

end ProbabilityTheory
