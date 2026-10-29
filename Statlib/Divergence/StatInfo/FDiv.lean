/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.FDiv.Basic
public import Statlib.Divergence.StatInfo.Basic
public import Statlib.Divergence.StatInfo.StatInfoDivFun

/-!
# The statistical information as an f-divergence

The f-divergence for the function `statInfoDivFun β γ` is, up to an explicit correction term, the
statistical information for the prior `boolMeasure β γ`. On probability measures, the correction
term vanishes and the statistical information is an f-divergence.

## Main statements

* `toReal_fDiv_statInfoDivFun_eq_integral_add`: `fDiv (statInfoDivFun β γ) μ ν` as a Bochner
  integral, plus the singular part.
* `toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg`: for `0 ≤ β, γ`, the f-divergence for
  `statInfoDivFun β γ` is the statistical information for the prior `boolMeasure β γ`, up to a
  correction term which vanishes when `β * μ univ = γ * ν univ`.
* `statInfo_eq_fDiv`: for finite measures with the same total mass, the statistical information
  with prior `π` is the f-divergence for `statInfoDivFun (π {false}) (π {true})`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {β γ : ℝ}

section StatInfoFun

open Set Filter ConvexOn

lemma integrable_statInfoFun_rnDeriv (β γ : ℝ) (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ statInfoFun β γ ((∂μ/∂ν) x).toReal) ν :=
  integrable_f_rnDeriv_of_derivAtTop_ne_top _ _
    ((convexOn_statInfoFun β γ).subset (subset_univ _) (convex_Ici 0))
    (derivAtTop_statInfoFun_ne_top β γ)

lemma measurable_fDiv_statInfoDivFun (μ ν : Measure 𝒳) [SigmaFinite μ] [SFinite ν] :
    Measurable (Function.uncurry fun β γ ↦ fDiv (statInfoDivFun β γ) μ ν) := by
  simp_rw [fDiv]
  · refine Measurable.add ?_ ?_
    · exact measurable_lintegral_statInfoDivFun
    simp_rw [derivAtTop_statInfoDivFun_eq]
    refine Measurable.mul_const ?_ _
    apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
      <;> refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ ?_ <;> fun_prop

section FDivStatInfo

lemma fDiv_statInfoDivFun_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoDivFun β γ) μ ν
      = ENNReal.ofReal (∫ x, statInfoFun β γ ((∂μ/∂ν) x).toReal ∂ν)
        + (statInfoDivFun β γ).derivAtTop * μ.singularPart ν univ := by
  unfold statInfoDivFun
  rw [fDiv_ofReal_eq_integral_add]
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _

lemma fDiv_statInfoDivFun_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    fDiv (statInfoDivFun β γ) μ ν
      = ∫⁻ x, ENNReal.ofReal (statInfoFun β γ ((∂μ/∂ν) x).toReal) ∂ν := by
  unfold statInfoDivFun
  rw [fDiv_ofReal_eq_lintegral_of_ac _ _ _ hμν]
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _

lemma toReal_fDiv_statInfoDivFun_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, statInfoFun β γ ((∂μ/∂ν) x).toReal ∂ν
        + (statInfoDivFun β γ).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  unfold statInfoDivFun
  rw [toReal_fDiv_ofReal_eq_integral_add]
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _
  · exact derivAtTop_statInfoDivFun_ne_top _ _

lemma fDiv_statInfoDivFun_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoDivFun β γ) μ ν ≠ ∞ := by
  refine fDiv_ne_top_of_derivAtTop_ne_top ?_ (derivAtTop_statInfoDivFun_ne_top _ _)
  unfold statInfoDivFun
  simp [DivFunction.ofReal_apply_zero_of_continuousWithinAt continuousWithinAt_statInfoFun_zero]

lemma toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonneg_of_le
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν := by
  simp_rw [toReal_fDiv_statInfoDivFun_eq_integral_add,
    derivAtTop_statInfoDivFun_of_nonneg_of_le hβ hγ,
    ENNReal.toReal_zero, zero_mul, add_zero, statInfoFun_of_le hγ]

lemma toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonneg_of_gt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : 0 ≤ β) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν + β * (μ.singularPart ν univ).toReal := by
  simp_rw [toReal_fDiv_statInfoDivFun_eq_integral_add,
    derivAtTop_statInfoDivFun_of_nonneg_of_gt hβ hγ,
    statInfoFun_of_gt hγ, ENNReal.toReal_ofReal hβ]

lemma toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonpos_of_le
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
        - β * (μ.singularPart ν univ).toReal := by
  simp_rw [toReal_fDiv_statInfoDivFun_eq_integral_add,
    derivAtTop_statInfoDivFun_of_nonpos_of_le hβ hγ, statInfoFun_of_le hγ]
  rw [ENNReal.toReal_ofReal, sub_eq_add_neg, neg_mul]
  simp [hβ]

lemma toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonpos_of_gt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : β ≤ 0) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν := by
  simp_rw [toReal_fDiv_statInfoDivFun_eq_integral_add,
    derivAtTop_statInfoDivFun_of_nonpos_of_gt hβ hγ, statInfoFun_of_gt hγ, ENNReal.toReal_zero,
    zero_mul, add_zero]

lemma fDiv_statInfoDivFun_eq_zero_of_nonneg_of_nonpos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ 0) :
    fDiv (statInfoDivFun β γ) μ ν = 0 := by
  refine (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right fDiv_statInfoDivFun_ne_top
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonneg_of_le hβ (hγ.trans hβ)]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <| hγ.trans <| mul_nonneg hβ ENNReal.toReal_nonneg

lemma fDiv_statInfoDivFun_eq_zero_of_nonpos_of_pos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : 0 < γ) :
    fDiv (statInfoDivFun β γ) μ ν = 0 := by
  refine (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right fDiv_statInfoDivFun_ne_top
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonpos_of_gt hβ (hβ.trans_lt hγ)]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <|
    (mul_nonpos_iff.mpr <| Or.inr ⟨hβ, ENNReal.toReal_nonneg⟩).trans hγ.le

/-- `max 0 a` in terms of the absolute value, in the form used below. -/
private lemma max_zero_eq_half (a : ℝ) : max 0 a = 2⁻¹ * (0 + a + |0 - a|) := by
  rw [zero_sub, abs_neg, zero_add]
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, abs_of_nonneg h]
    ring
  · rw [max_eq_left h, abs_of_nonpos h]
    ring

/-- Auxiliary lemma for `toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_le` and
`toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonpos_of_le`. -/
private lemma integral_max_eq_integral_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν + γ * (ν univ).toReal - β * (μ univ).toReal
        + β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_zero_eq_half, zero_add, zero_sub, neg_sub, integral_const_mul]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ γ - β * ((∂μ/∂ν) x).toReal) ν := (integrable_const γ).sub h_int
  rw [integral_add h_int', integral_sub (integrable_const γ) h_int, integral_const, smul_eq_mul,
    mul_comm, integral_const_mul, add_comm, add_sub_assoc, add_assoc, sub_eq_add_neg,
    sub_eq_add_neg, add_assoc, ← mul_neg, ← mul_neg, ← mul_add]
  swap; · exact (integrable_add_const_iff.mpr h_int).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

/-- Auxiliary lemma for `toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_gt` and
`toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonpos_of_gt`. -/
private lemma integral_max_eq_integral_abs' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν - γ * (ν univ).toReal + β * (μ univ).toReal
        - β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_zero_eq_half, zero_add, zero_sub, abs_neg, integral_const_mul]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal - γ) ν := h_int.sub (integrable_const γ)
  rw [integral_add h_int', integral_sub h_int (integrable_const γ), integral_const, smul_eq_mul,
    mul_comm, integral_const_mul, add_comm, add_sub_assoc, sub_eq_add_neg, add_comm (β * _),
    ← add_assoc, ← sub_eq_add_neg]
  swap; · exact (h_int.sub (integrable_const _)).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

lemma toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_le
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
        + β * (μ.singularPart ν univ).toReal + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonneg_of_le hβ hγ,
    integral_max_eq_integral_abs,
    sub_eq_add_neg, add_assoc, add_comm (- _), ← add_assoc, ← sub_eq_add_neg, add_assoc,
    add_comm (_ * _), add_assoc]

lemma toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_gt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : 0 ≤ β) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν univ).toReal + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  have h_eq : β * (μ.singularPart ν univ).toReal
      = 2⁻¹ * (2 * β * (μ.singularPart ν univ).toReal) := by simp [mul_assoc]
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonneg_of_gt hβ hγ,
    integral_max_eq_integral_abs', h_eq,
    ← mul_add]
  simp_rw [sub_eq_add_neg, add_assoc]
  congr 2
  ring

lemma toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonpos_of_le
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν univ).toReal + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  have h_eq : β * (μ.singularPart ν univ).toReal
      = 2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal) := by simp [mul_assoc]
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonpos_of_le hβ hγ,
    integral_max_eq_integral_abs, h_eq,
    sub_eq_add_neg, ← mul_neg, ← mul_add]
  simp_rw [sub_eq_add_neg, add_assoc]
  congr 2
  ring

lemma toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonpos_of_gt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hβ : β ≤ 0) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν univ).toReal + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [toReal_fDiv_statInfoDivFun_eq_integral_max_of_nonpos_of_gt hβ hγ,
    integral_max_eq_integral_abs']
  simp_rw [sub_eq_add_neg]
  ring_nf

end FDivStatInfo

section FDivStatInfoEqStatInfo

lemma toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Measure.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [toReal_statInfo_eq_integral_abs]
  simp only [Measure.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Measure.boolMeasure_apply_true, hγ]
  rw [toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_le hβ hγβ, ← mul_add]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, sub_self, zero_add]

lemma toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Measure.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [toReal_statInfo_eq_integral_abs]
  simp only [Measure.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Measure.boolMeasure_apply_true, hγ]
  rw [toReal_fDiv_statInfoDivFun_eq_integral_abs_of_nonneg_of_gt hβ hγβ, ← mul_add]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, sub_self, zero_add]

-- N.B. we cannot use the Real.sign function here because it is 0 at 0, but we need it to be -1.
lemma toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Measure.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + (if γ ≤ β then -1 else 1) * (β * (μ univ).toReal - γ * (ν univ).toReal)) := by
  rcases le_or_gt γ β with (hβγ | hβγ)
  · rw [toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg_of_le hβ hγ hβγ, ite_eq_left hβγ,
      neg_one_mul,
      neg_sub, sub_eq_add_neg, add_assoc, ← sub_eq_add_neg]
  · rw [toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg_of_gt hβ hγ hβγ, ite_eq_right hβγ.not_ge,
      one_mul, add_sub_assoc]

/-- For finite measures with the same total mass (for example probability measures), the
statistical information with prior `π` is the f-divergence for the function
`statInfoDivFun (π {false}) (π {true})`. -/
lemma statInfo_eq_fDiv (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_univ : μ univ = ν univ) (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = fDiv (statInfoDivFun (π {false}).toReal (π {true}).toReal) μ ν := by
  set β := (π {false}).toReal
  set γ := (π {true}).toReal
  have h := toReal_fDiv_statInfoDivFun_eq_statInfo_of_nonneg (μ := μ) (ν := ν) (β := β) (γ := γ)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have h_corr : |β * (μ univ).toReal - γ * (ν univ).toReal|
      + (if γ ≤ β then -1 else 1) * (β * (μ univ).toReal - γ * (ν univ).toReal) = 0 := by
    rw [h_univ, ← sub_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    split_ifs with hβγ
    · rw [abs_of_nonneg (sub_nonneg.mpr hβγ)]
      ring
    · rw [abs_of_neg (sub_neg.mpr (not_le.mp hβγ))]
      ring
  rw [h_corr, mul_zero, add_zero] at h
  simp only [β, γ, ENNReal.ofReal_toReal (measure_ne_top π _), ← Measure.eq_boolMeasure] at h
  exact ((ENNReal.toReal_eq_toReal_iff' fDiv_statInfoDivFun_ne_top
    (statInfo_ne_top _ _ _)).mp h).symm

end FDivStatInfoEqStatInfo

end StatInfoFun

end ProbabilityTheory
