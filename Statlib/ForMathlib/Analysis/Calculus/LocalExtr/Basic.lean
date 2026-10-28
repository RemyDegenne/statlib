/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.LocalExtr

/-!
# One-sided derivatives at a local minimum

At a local minimum `x` of `f : ℝ → ℝ`, the right derivative `derivWithin f (Ioi x) x` is
nonnegative and the left derivative `derivWithin f (Iio x) x` is nonpositive. No differentiability
is assumed: if `f` is not differentiable on the corresponding side, the derivative is `0`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), where these results were stated for convex
functions.
-/

@[expose] public section

open Filter Set Topology

variable {f : ℝ → ℝ} {x : ℝ}

/-- At a local minimum, the right derivative is nonnegative. -/
lemma IsLocalMin.rightDeriv_nonneg (h : IsLocalMin f x) : 0 ≤ derivWithin f (Ioi x) x := by
  by_cases hd : DifferentiableWithinAt ℝ f (Ioi x) x
  · refine ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
      hd.hasDerivWithinAt) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h] with y (hy : x < y) hfy
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr hfy) (sub_pos.mpr hy).le
  · rw [derivWithin_zero_of_not_differentiableWithinAt hd]

/-- At a local minimum, the left derivative is nonpositive. -/
lemma IsLocalMin.leftDeriv_nonpos (h : IsLocalMin f x) : derivWithin f (Iio x) x ≤ 0 := by
  by_cases hd : DifferentiableWithinAt ℝ f (Iio x) x
  · refine le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp
      hd.hasDerivWithinAt) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h] with y (hy : y < x) hfy
    rw [slope_def_field]
    exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hfy) (sub_neg.mpr hy).le
  · rw [derivWithin_zero_of_not_differentiableWithinAt hd]
