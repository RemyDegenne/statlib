/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.Hellinger.HellingerFun

/-!
# The divergence function of the Hellinger divergence

## Main definitions

* `hellingerDivFun a`: the `DivFunction` of the Hellinger divergence of order `a`, obtained from
  `hellingerFun a` for `0 < a` (it is `klDivFun` for `a = 1`), and equal to `0` for `a ≤ 0`.

## Main statements

* `hellingerDivFun_one`: `hellingerDivFun 1 = klDivFun`.
* `derivAtTop_hellingerDivFun_of_one_le`, `derivAtTop_hellingerDivFun_of_lt_one`: the derivative
  at infinity is `∞` for `1 ≤ a` and `a / (1 - a)` for `a < 1`.
* `conj_hellingerDivFun_ofReal`: the conjugate of `hellingerDivFun a` is
  `u ↦ (u ^ (1 - a) - u - a * (1 - u)) / (a - 1)` on `(0, ∞)`.
* `conj_hellingerDivFun_inv_two`: `hellingerDivFun 2⁻¹` is self-conjugate.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- The divergence function of the Hellinger divergence of order `a`: for `0 < a`, it is the
`DivFunction` obtained from `hellingerFun a` (which is `klFun` for `a = 1`). For `a ≤ 0` it is `0`:
`hellingerFun a` is not convex for `a < 0`, and for `a = 0` the value of a `DivFunction` at `0` is
determined by continuity, so the indicator of `{0}` cannot be used. -/
noncomputable
def hellingerDivFun (a : ℝ) : DivFunction :=
  if ha : a ≤ 0 then 0
  else DivFunction.ofReal (hellingerFun a)
    ((convexOn_hellingerFun (not_le.mp ha).le).subset (Ioi_subset_Ici le_rfl) (convex_Ioi _))
    hellingerFun_apply_one_eq_zero

@[simp]
lemma hellingerDivFun_of_nonpos (ha : a ≤ 0) : hellingerDivFun a = 0 := dite_eq_left ha

lemma hellingerDivFun_zero : hellingerDivFun 0 = 0 := dite_eq_left le_rfl

lemma hellingerDivFun_of_pos (ha_pos : 0 < a) :
    hellingerDivFun a = DivFunction.ofReal (hellingerFun a)
      ((convexOn_hellingerFun ha_pos.le).subset (Ioi_subset_Ici le_rfl) (convex_Ioi _))
      hellingerFun_apply_one_eq_zero :=
  dite_eq_right (not_le.mpr ha_pos)

@[simp]
lemma hellingerDivFun_one : hellingerDivFun 1 = klDivFun := by
  rw [hellingerDivFun_of_pos zero_lt_one, klDivFun]
  congr 1
  ext x
  simp [hellingerFun_one, InformationTheory.klFun_apply]

lemma hellingerDivFun_apply_zero_of_pos (ha_pos : 0 < a) : hellingerDivFun a 0 = 1 := by
  rw [hellingerDivFun_of_pos ha_pos,
    DivFunction.ofReal_apply_zero_of_continuousWithinAt
      (continuous_hellingerFun ha_pos).continuousWithinAt]
  simp

@[simp]
lemma hellingerDivFun_apply_zero :
    hellingerDivFun a 0 = if a ≤ 0 then 0 else 1 := by
  split_ifs with h0
  · simp [h0]
  · exact hellingerDivFun_apply_zero_of_pos (not_le.mp h0)

lemma hellingerDivFun_apply_of_pos_of_ne_one (ha_pos : 0 < a) (ha_one : a ≠ 1)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    hellingerDivFun a x = ENNReal.ofReal ((a - 1)⁻¹ * (x.toReal ^ a - 1 - a * (x.toReal - 1))) := by
  rw [hellingerDivFun_of_pos ha_pos]
  by_cases hx0 : x = 0
  · rw [hx0, DivFunction.ofReal_apply_zero_of_continuousWithinAt]
    · simp only [hellingerFun_apply_zero, ENNReal.ofReal_one, ENNReal.toReal_zero, ne_eq,
        ha_pos.ne', not_false_eq_true, zero_rpow, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
      rw [add_comm, ← sub_eq_add_neg, inv_mul_cancel₀, ENNReal.ofReal_one]
      rwa [sub_ne_zero]
    · exact (continuous_hellingerFun ha_pos).continuousWithinAt
  · rw [DivFunction.ofReal_apply hx0 hx, hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha_one]

@[simp]
lemma derivAtTop_hellingerDivFun :
    (hellingerDivFun a).derivAtTop =
      if a ≤ 0 then 0
      else if a < 1 then ENNReal.ofReal (a * (1 - a)⁻¹)
      else ∞ := by
  split_ifs with h h_one
  · simp [h]
  · rw [hellingerDivFun_of_pos (not_le.mp h)]
    exact DivFunction.derivAtTop_ofReal_of_tendsto_nhds
      (tendsto_rightDeriv_hellingerFun_atTop_of_lt_one h_one)
  · by_cases ha_one : a = 1
    · simp [ha_one]
    rw [hellingerDivFun_of_pos (not_le.mp h)]
    exact DivFunction.derivAtTop_ofReal_of_tendsto_atTop
      (tendsto_rightDeriv_hellingerFun_atTop_of_one_lt
        ((not_lt.mp h_one).lt_of_ne (Ne.symm ha_one)))

lemma derivAtTop_hellingerDivFun_of_lt_one (ha_pos : 0 < a) (ha_lt : a < 1) :
    (hellingerDivFun a).derivAtTop = ENNReal.ofReal (a * (1 - a)⁻¹) := by
  simp [derivAtTop_hellingerDivFun, not_le.mpr ha_pos, ha_lt]

lemma derivAtTop_hellingerDivFun_of_one_le (ha_le : 1 ≤ a) :
    (hellingerDivFun a).derivAtTop = ∞ := by
  simp [derivAtTop_hellingerDivFun, not_le.mpr (zero_lt_one.trans_le ha_le), ha_le]

lemma derivAtTop_hellingerDivFun_eq_top_iff : (hellingerDivFun a).derivAtTop = ∞ ↔ 1 ≤ a := by
  simp only [derivAtTop_hellingerDivFun]
  split_ifs with h1 h2
  · simp [h1.trans_lt zero_lt_one]
  · simp [h2]
  · simp [not_lt.mp h2]

lemma lintegral_hellingerDivFun_of_pos_of_ne_one_of_integrable
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫⁻ x, hellingerDivFun a (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal ((a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by
  calc ∫⁻ x, hellingerDivFun a (μ.rnDeriv ν x) ∂ν
  _ = ∫⁻ x, ENNReal.ofReal (hellingerFun a (μ.rnDeriv ν x).toReal) ∂ν := by
    rw [hellingerDivFun_of_pos ha_pos]
    exact DivFunction.lintegral_ofReal_of_continuous
      (continuous_hellingerFun ha_pos).continuousWithinAt
  _ = ENNReal.ofReal (∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_hellingerFun_iff_integrable_rpow ha_ne]
    · exact ae_of_all _ fun x ↦ hellingerFun_nonneg ha_pos.le ENNReal.toReal_nonneg
  _ = ENNReal.ofReal ((a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by
      rw [integral_hellingerFun_of_pos_of_ne_one_of_integrable ha_pos ha_ne h_int]

lemma lintegral_hellingerDivFun_of_pos_of_ne_one_of_integrable_of_ac
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν)
    (hμν : μ ≪ ν) :
    ∫⁻ x, hellingerDivFun a (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal ((a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ univ).toReal) := by
  rw [lintegral_hellingerDivFun_of_pos_of_ne_one_of_integrable ha_pos ha_ne h_int,
    Measure.integral_toReal_rnDeriv hμν, measureReal_def]

/-- The conjugate `u ↦ u * f (1 / u)` of `f = hellingerDivFun a` is
`u ↦ (u ^ (1 - a) - u - a * (1 - u)) / (a - 1)` on `(0, ∞)`. -/
lemma conj_hellingerDivFun_ofReal (ha_pos : 0 < a) (ha_ne : a ≠ 1) {u : ℝ} (hu : 0 < u) :
    (hellingerDivFun a).conj (ENNReal.ofReal u)
      = ENNReal.ofReal ((a - 1)⁻¹ * (u ^ (1 - a) - u - a * (1 - u))) := by
  have hu0 : ENNReal.ofReal u ≠ 0 := by simpa using hu
  rw [DivFunction.conj_of_ne_zero hu0, hellingerDivFun_apply_of_pos_of_ne_one ha_pos ha_ne
    (ENNReal.inv_ne_top.mpr hu0), ENNReal.toReal_inv, ENNReal.toReal_ofReal hu.le,
    ← ENNReal.ofReal_mul hu.le]
  congr 1
  have h1 : u * u⁻¹ ^ a = u ^ (1 - a) := by
    rw [Real.inv_rpow hu.le, Real.rpow_sub hu, Real.rpow_one, div_eq_mul_inv]
  have h2 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  linear_combination (a - 1)⁻¹ * h1 - a * (a - 1)⁻¹ * h2

/-- The divergence function of order `2⁻¹` is self-conjugate. -/
lemma conj_hellingerDivFun_inv_two : (hellingerDivFun 2⁻¹).conj = hellingerDivFun 2⁻¹ := by
  refine DivFunction.eq_of_forall_ne_zero_ne_top fun x hx0 hx_top ↦ ?_
  have hx : 0 < x.toReal := ENNReal.toReal_pos hx0 hx_top
  rw [← ENNReal.ofReal_toReal hx_top, conj_hellingerDivFun_ofReal (by norm_num) (by norm_num) hx,
    hellingerDivFun_apply_of_pos_of_ne_one (by norm_num) (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hx.le]
  norm_num
  ring_nf

end ProbabilityTheory
