/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Statlib.ForMathlib.Analysis.Convex.DerivAtTop

/-!
# Integrability of `f ∘ ∂μ/∂ν`

## Main statements

* `ConvexOn.measurable_comp_of_nonneg`: a function convex on `(0, ∞)`, composed with a nonnegative
  measurable function, is measurable. No measurability of `f` is needed, since `f` is continuous
  on `(0, ∞)`.
* `MeasureTheory.integrable_f_rnDeriv_of_derivAtTop_ne_top`: for finite measures `μ, ν` and a
  function `f` convex on `[0, ∞)` with `derivAtTop f ≠ ⊤`, the function `x ↦ f (∂μ/∂ν x).toReal`
  is `ν`-integrable: it lies between an affine function of `∂μ/∂ν` and
  `f 0 + (derivAtTop f).toReal * ∂μ/∂ν`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Filter Set Topology

/-- A function convex on `(0, ∞)`, composed with a nonnegative measurable function, is measurable.
-/
lemma ConvexOn.measurable_comp_of_nonneg {α : Type*} {mα : MeasurableSpace α} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) {g : α → ℝ} (hg : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x) :
    Measurable fun x ↦ f (g x) := by
  -- `f ∘ max · 0` is continuous outside of `0`: constant on `(-∞, 0)`, convex on `(0, ∞)`
  have h_cont : ContinuousOn (fun y ↦ f (max y 0)) {0}ᶜ := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · refine ((continuousAt_const (y := f 0)).congr ?_).continuousWithinAt
      filter_upwards [eventually_lt_nhds hy] with z hz
      rw [max_eq_right hz.le]
    · have h_int : interior (Ioi (0 : ℝ)) ∈ 𝓝 y := isOpen_interior.mem_nhds (by simpa using hy)
      refine ((hf.continuousOn_interior.continuousAt h_int).congr ?_).continuousWithinAt
      filter_upwards [eventually_gt_nhds hy] with z hz
      rw [max_eq_left hz.le]
  convert (measurable_of_continuousOn_compl_singleton 0 h_cont).comp hg using 2 with x
  simp [max_eq_left (hg_nonneg x)]

namespace MeasureTheory

lemma integrable_f_rnDeriv_of_derivAtTop_ne_top {α : Type*} {mα : MeasurableSpace α}
    {f : ℝ → ℝ} (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_deriv : derivAtTop f ≠ ⊤) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  obtain ⟨c, c', h⟩ := hf_cvx.exists_affine_le
  refine integrable_of_le_of_le (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
    (g₂ := fun x ↦ (derivAtTop f).toReal * (μ.rnDeriv ν x).toReal + f 0) ?_ ?_ ?_ ?_ ?_
  · exact ((hf_cvx.subset Ioi_subset_Ici_self (convex_Ioi 0)).measurable_comp_of_nonneg
      (μ.measurable_rnDeriv ν).ennreal_toReal
      fun _ ↦ ENNReal.toReal_nonneg).aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ h _ ENNReal.toReal_nonneg
  · refine ae_of_all _ fun x ↦ ?_
    have h_le := hf_cvx.le_add_derivAtTop hf_deriv le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
    rw [sub_zero] at h_le
    linarith
  · exact (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  · exact (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)

end MeasureTheory
