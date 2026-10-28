/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Statlib.Divergence.FDiv.Basic
public import Statlib.Divergence.StatInfo.Basic

/-!
# Total variation distance, statistical information and f-divergences

Mathlib's total variation distance `MeasureTheory.tvDist μ ν` (and its `ℝ≥0∞`-valued version
`MeasureTheory.etvDist μ ν`) is, up to a factor `2` and a correction for the difference of the
masses of `μ` and `ν`, the statistical information `statInfo μ ν (boolMeasure 1 1)` for the uniform
prior. We use this to transfer results about the statistical information to the total variation
distance.

## Main definitions

* `tvDivFun`: the `DivFunction` `x ↦ |1 - x|`.

## Main statements

* `tvDist_eq_two_mul_toReal_statInfo_add_abs`: for finite measures,
  `tvDist μ ν = 2 * (statInfo μ ν (boolMeasure 1 1)).toReal + |μ.real univ - ν.real univ|`.
* `etvDist_eq_two_mul_statInfo`, `tvDist_eq_two_mul_toReal_statInfo`: for finite measures with the
  same mass, in particular for probability measures, the total variation distance is twice the
  statistical information for the uniform prior.
* `tvDist_comp_le`, `etvDist_comp_le`: **data-processing inequality** for the total variation
  distance.
* `lintegral_one_sub_rnDeriv_eq_etvDist_div_two`: for finite measures with the same mass,
  `∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = etvDist μ ν / 2`.
* `fDiv_tvDivFun`: for finite measures, `etvDist μ ν` is the f-divergence for the function
  `tvDivFun = x ↦ |1 - x|`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), where the total variation distance was
defined as the statistical information for the uniform prior.
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳}

/-- The total variation distance in terms of the statistical information for the uniform prior. -/
lemma tvDist_eq_two_mul_toReal_statInfo_add_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν
      = 2 * (statInfo μ ν (Measure.boolMeasure 1 1)).toReal + |μ.real .univ - ν.real .univ| := by
  rw [toReal_statInfo_eq_integral_abs, tvDist_eq_integral_abs_rnDeriv_add_singularPart]
  simp only [Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true, one_mul,
    ENNReal.toReal_one, Measure.real, abs_sub_comm _ (1 : ℝ)]
  ring

/-- For finite measures with the same mass, in particular probability measures, the total variation
distance is twice the statistical information for the uniform prior. -/
lemma tvDist_eq_two_mul_toReal_statInfo [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ .univ = ν .univ) :
    tvDist μ ν = 2 * (statInfo μ ν (Measure.boolMeasure 1 1)).toReal := by
  rw [tvDist_eq_two_mul_toReal_statInfo_add_abs, measureReal_def, h, ← measureReal_def, sub_self,
    abs_zero, add_zero]

/-- For finite measures with the same mass, in particular probability measures, the total variation
distance is twice the statistical information for the uniform prior. -/
lemma etvDist_eq_two_mul_statInfo [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ .univ = ν .univ) :
    etvDist μ ν = 2 * statInfo μ ν (Measure.boolMeasure 1 1) := by
  rw [← ofReal_tvDist, tvDist_eq_two_mul_toReal_statInfo h, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (statInfo_ne_top _ _ _)]

/-- **Data processing inequality** for the total variation distance. -/
lemma tvDist_comp_le (μ ν : Measure 𝒳) (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [tvDist_eq_two_mul_toReal_statInfo_add_abs, tvDist_eq_two_mul_toReal_statInfo_add_abs]
    simp only [measureReal_def, Measure.comp_apply_univ]
    gcongr
    · exact statInfo_ne_top _ _ _
    · exact statInfo_comp_le μ ν _ κ
  · have h_comp : ¬ (IsFiniteMeasure (κ ∘ₘ μ) ∧ IsFiniteMeasure (κ ∘ₘ ν)) := by
      rwa [isFiniteMeasure_iff (μ := κ ∘ₘ μ), isFiniteMeasure_iff (μ := κ ∘ₘ ν),
        Measure.comp_apply_univ, Measure.comp_apply_univ, ← isFiniteMeasure_iff,
        ← isFiniteMeasure_iff]
    rw [tvDist_of_not_isFiniteMeasure h_comp]
    exact tvDist_nonneg

/-- **Data processing inequality** for the total variation distance. -/
lemma etvDist_comp_le (μ ν : Measure 𝒳) (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    etvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [← ofReal_tvDist, ← ofReal_tvDist]
    exact ENNReal.ofReal_le_ofReal (tvDist_comp_le μ ν κ)
  · rw [etvDist_of_not_isFiniteMeasure h]
    exact le_top

/-- For the uniform prior, the statistical information is `∫⁻ x, 1 - (∂μ/∂ν) x ∂ν`, provided that
`ν` has at most the mass of `μ`. -/
lemma lintegral_one_sub_rnDeriv_eq_statInfo [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν .univ ≤ μ .univ) :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = statInfo μ ν (Measure.boolMeasure 1 1) := by
  simp [statInfo_eq_lintegral_of_ge (π := Measure.boolMeasure 1 1) (by simpa using h)]

/-- For finite measures with the same mass, in particular probability measures,
`∫⁻ x, 1 - (∂μ/∂ν) x ∂ν` is half the total variation distance. -/
lemma lintegral_one_sub_rnDeriv_eq_etvDist_div_two [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ .univ = ν .univ) :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = etvDist μ ν / 2 := by
  rw [lintegral_one_sub_rnDeriv_eq_statInfo h.ge, etvDist_eq_two_mul_statInfo h, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

section FDiv

/-! ### The total variation distance as an f-divergence -/

/-- The `DivFunction` `x ↦ |1 - x|`. Its f-divergence is the total variation distance
(`fDiv_tvDivFun`). -/
noncomputable def tvDivFun : DivFunction :=
  DivFunction.ofReal (fun x ↦ |1 - x|)
    ((convexOn_dist (1 : ℝ) (convex_Ioi 0)).congr fun x _ ↦ abs_sub_comm x 1)
    (by simp)

lemma tvDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) : tvDivFun x = ENNReal.ofReal |1 - x.toReal| :=
  DivFunction.ofReal_apply_of_continuousWithinAt
    (continuous_abs.comp (continuous_sub_left 1)).continuousWithinAt hx

@[simp] lemma derivAtTop_tvDivFun : tvDivFun.derivAtTop = 1 := by
  -- for `x > 1`, the derivative of `y ↦ |1 - y|` at `x` is `1`
  have h : Tendsto (fun x ↦ derivWithin (fun y : ℝ ↦ |1 - y|) (Ioi x) x) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have h_eq : (fun y : ℝ ↦ |1 - y|) =ᶠ[𝓝 x] fun y ↦ y - 1 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [abs_of_neg (sub_neg.mpr hy), neg_sub]
    exact ((((hasDerivAt_id' x).sub_const 1).congr_of_eventuallyEq h_eq).hasDerivWithinAt
      |>.derivWithin (uniqueDiffWithinAt_Ioi x)).symm
  rw [tvDivFun, DivFunction.derivAtTop_ofReal_of_tendsto_nhds h, ENNReal.ofReal_one]

/-- The total variation distance between finite measures is the f-divergence for the function
`x ↦ |1 - x|`. -/
lemma fDiv_tvDivFun (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv tvDivFun μ ν = etvDist μ ν := by
  rw [fDiv, derivAtTop_tvDivFun, one_mul, etvDist_eq_lintegral_enorm_rnDeriv_add_singularPart]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  rw [tvDivFun_apply hx, ← Real.norm_eq_abs, ofReal_norm]

end FDiv

end ProbabilityTheory
