/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.FDiv.DivFunction.CurvatureMeasure
public import Statlib.Divergence.StatInfo.FDiv

/-!
# Integral representation of f-divergences

Every f-divergence is an integral of the f-divergences of the functions `statInfoDivFun 1 x`
against the curvature measure of `f`. For finite measures with the same mass, those f-divergences
are statistical informations (`statInfo_eq_fDiv`), hence every f-divergence is an integral of
statistical informations (Liese and Vajda).

## Main statements

* `DivFunction.realFun_eq_integral_statInfoFun`: Taylor formula for a divergence function in terms
  of the hockey-stick functions, `f t = f'(1) (t - 1) + ∫ y, statInfoFun 1 y t ∂γ_f`.
* `fDiv_add_eq_lintegral_fDiv_statInfoDivFun_add`:
  `fDiv f μ ν + f.rightDeriv 1 * ν univ
    = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal + f.rightDeriv 1 * μ univ`.
* `fDiv_eq_lintegral_fDiv_statInfoDivFun`: the same, for `f` with `f.rightDeriv 1 = 0`:
  `fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal`.
* `fDiv_eq_lintegral_statInfo`: for finite measures with `μ univ = ν univ`,
  `D_f(μ, ν) = ∫ y, I_{(1, y)}(μ, ν) ∂γ_f`, where `I_π` is the statistical information with
  prior `π` (for probability measures and `1 ≤ y`, `I_{(1, y)}(μ, ν)` is the hockey-stick
  divergence `E_y(μ, ν) = sup_E (μ(E) - y ν(E))`).
* `fDiv_eq_lintegral_statInfo_prior`: the representation of Liese and Vajda,
  `D_f(μ, ν) = ∫ p, I_{(p, 1 - p)}(μ, ν) ∂Γ_f`, where `I_{(p, 1 - p)}` is the DeGroot statistical
  information and `Γ_f` is the image of the measure `(1 + y) γ_f(dy)` by `y ↦ (1 + y)⁻¹`.

## References

* F. Liese, I. Vajda, *On divergences and informations in statistics and information theory*,
  IEEE Transactions on Information Theory 52(10) (2006).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f : DivFunction}

section StatInfoFun

open Set Filter ConvexOn

lemma measurable_fDiv_statInfoDivFun_right [SigmaFinite μ] [SFinite ν] :
    Measurable fun y ↦ fDiv (statInfoDivFun 1 y) μ ν :=
  (measurable_fDiv_statInfoDivFun μ ν).comp (f := fun y ↦ ((1 : ℝ), y)) measurable_prodMk_left

lemma measurable_derivAtTop_statInfoDivFun :
    Measurable fun x : ℝ ↦ (statInfoDivFun 1 x).derivAtTop := by
  simp_rw [derivAtTop_statInfoDivFun_eq]
  simp only [zero_le_one, ↓reduceIte, ENNReal.ofReal_one]
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma lintegral_derivAtTop_statInfoDivFun_eq_toENNReal :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
      = ((f.derivAtTop : EReal) - f.rightDerivStieltjes 1).toENNReal := by
  simp_rw [derivAtTop_statInfoDivFun_eq]
  simp only [zero_le_one, ↓reduceIte, ENNReal.ofReal_one]
  have : (fun x : ℝ ↦ if x ≤ 1 then (0 : ℝ≥0∞) else 1) = (Ioi 1).indicator 1 := by
    ext x
    split_ifs with h
    · simp [h]
    · simp [not_le.mp h]
  simp_rw [this, lintegral_indicator_one measurableSet_Ioi]
  rw [f.curvatureMeasureReal_apply measurableSet_Ioi]
  have : ENNReal.toReal ⁻¹' Ioi 1 = Ioo 1 ∞ := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Ioo]
    constructor <;> intro h
    · by_cases hx_top : x = ∞
      · simp only [hx_top, ENNReal.toReal_top] at h
        exact absurd h (not_lt.mpr zero_le_one)
      · rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top hx_top] at h
        exact ⟨h, Ne.lt_top hx_top⟩
    · rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.2.ne]
      exact h.1
  rw [this]
  simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true,
    DivFunction.curvatureMeasure_Ioo_top_eq_curvatureMeasure_Ioi, f.curvatureMeasure_Ioi,
    ENNReal.toReal_one]
  rw [ERealStieltjes.measure_Ioi f.rightDerivStieltjes f.tendsto_rightDerivStieltjes_atTop]

/-- The integral of the `derivAtTop` of the `statInfoDivFun 1 x` against the curvature measure of
`f` is `f.derivAtTop`, up to the right derivative of `f` at `1`. -/
lemma lintegral_derivAtTop_statInfoDivFun :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
      + ENNReal.ofReal (f.rightDeriv 1) = f.derivAtTop := by
  rw [lintegral_derivAtTop_statInfoDivFun_eq_toENNReal, DivFunction.rightDerivStieltjes_one]
  by_cases h_top : f.derivAtTop = ∞
  · rw [h_top, EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.toENNReal_top, top_add]
  · have h_le : f.rightDeriv 1 ≤ f.derivAtTop.toReal := by
      rw [DivFunction.rightDeriv_def, ENNReal.toReal_one]
      exact f.derivWithin_realFun_le_toReal_derivAtTop h_top
        (by simpa using DivFunction.xmin_lt_one) (by simpa using DivFunction.one_lt_xmax)
    rw [← EReal.coe_ennreal_toReal h_top, ← EReal.coe_sub,
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
      ← ENNReal.ofReal_add (sub_nonneg.mpr h_le) f.rightDeriv_one_nonneg, sub_add_cancel,
      ENNReal.ofReal_toReal h_top]

lemma lintegral_statInfoFun_curvatureMeasureReal_add {t : ℝ≥0∞} (ht_ne : t ≠ ∞) :
    ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
      + ENNReal.ofReal (f.rightDeriv 1) * t
      = f t + ENNReal.ofReal (f.rightDeriv 1) := by
  rcases le_total 1 t with ht | ht
  · have ht' : 1 ≤ t.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ht_ne ht
    have h_int : ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
        = ∫⁻ x in Ioc 1 t, t - x ∂f.curvatureMeasure := by
      simp_rw [statInfoFun_of_one_of_one_le_right ht']
      have : ∀ y, ENNReal.ofReal ((Ioc 1 t.toReal).indicator (fun y ↦ t.toReal - y) y)
          = (Ioc 1 t.toReal).indicator (fun y ↦ ENNReal.ofReal (t.toReal - y)) y := fun y ↦ by
        by_cases hy : y ∈ Ioc 1 t.toReal <;> simp [hy]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Ioc,
        f.setLIntegral_Ioc_curvatureMeasureReal (by fun_prop) zero_le_one, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal ht_ne]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht_ne,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ht_ne hx.2)]
    rw [h_int, f.taylor_one_right ht ht_ne]
    have : ENNReal.ofReal (f.rightDeriv 1) * t
        = ENNReal.ofReal (f.rightDeriv 1) * (t - 1)
          + ENNReal.ofReal (f.rightDeriv 1) := by
      conv_lhs => rw [← tsub_add_cancel_of_le ht, mul_add, mul_one]
    rw [this]
    ring
  · have ht' : t.toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top ht
    have h_int : ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
        = ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure := by
      simp_rw [statInfoFun_of_one_of_right_le_one ht']
      have : ∀ y, ENNReal.ofReal ((Ioc t.toReal 1).indicator (fun y ↦ y - t.toReal) y)
          = (Ioc t.toReal 1).indicator (fun y ↦ ENNReal.ofReal (y - t.toReal)) y := fun y ↦ by
        by_cases hy : y ∈ Ioc t.toReal 1 <;> simp [hy]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Ioc,
        f.setLIntegral_Ioc_curvatureMeasureReal (by fun_prop) ENNReal.toReal_nonneg,
        ENNReal.ofReal_one, ENNReal.ofReal_toReal ht_ne]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht_ne,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx.2)]
    rw [h_int, ← f.taylor_one_left ht, add_assoc, ← mul_add, tsub_add_cancel_of_le ht,
      mul_one]

/-- **Taylor formula** for a divergence function, in terms of the hockey-stick functions: for
`0 ≤ t` in the effective domain of `f`,
`f t = f'(1) (t - 1) + ∫ y, statInfoFun 1 y t ∂γ_f`, where `γ_f` is the curvature measure of `f`.
See `lintegral_statInfoFun_curvatureMeasureReal_add` for a version in `ℝ≥0∞`. -/
theorem DivFunction.realFun_eq_integral_statInfoFun (f : DivFunction) {t : ℝ} (ht : 0 ≤ t)
    (ht_top : f (ENNReal.ofReal t) ≠ ∞) :
    f.realFun t
      = f.rightDeriv 1 * (t - 1) + ∫ y, statInfoFun 1 y t ∂f.curvatureMeasureReal := by
  have h := lintegral_statInfoFun_curvatureMeasureReal_add (f := f)
    (ENNReal.ofReal_ne_top (r := t))
  rw [ENNReal.toReal_ofReal ht] at h
  have h_meas : Measurable fun y ↦ ENNReal.ofReal (statInfoFun 1 y t) :=
    (measurable_statInfoFun.comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)).ennreal_ofReal
  have h_lint_ne_top :
      ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t) ∂f.curvatureMeasureReal ≠ ∞ := by
    intro h_top
    rw [h_top, top_add] at h
    exact ENNReal.add_ne_top.mpr ⟨ht_top, ENNReal.ofReal_ne_top⟩ h.symm
  have h_int : Integrable (fun y ↦ statInfoFun 1 y t) f.curvatureMeasureReal := by
    have := integrable_toReal_of_lintegral_ne_top h_meas.aemeasurable h_lint_ne_top
    simpa only [ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _)] using this
  rw [← ofReal_integral_eq_lintegral_ofReal h_int
    (ae_of_all _ fun y ↦ statInfoFun_nonneg _ _ _)] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_add ht_top ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg fun y ↦ statInfoFun_nonneg _ _ _),
    ENNReal.toReal_ofReal f.rightDeriv_one_nonneg, ENNReal.toReal_ofReal ht] at h'
  simp only [DivFunction.realFun]
  linarith

lemma lintegral_f_rnDeriv_add_eq_lintegral_fDiv_statInfoDivFun_add_of_ac
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + ENNReal.ofReal (f.rightDeriv 1) * ν univ
      = ∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) μ ν ∂f.curvatureMeasure
        + ENNReal.ofReal (f.rightDeriv 1) * μ univ := by
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    measurable_statInfoFun.comp <|
      (measurable_const.prodMk measurable_snd).prodMk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  simp_rw [fDiv_statInfoDivFun_eq_lintegral_of_ac h_ac]
  have : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + ENNReal.ofReal (f.rightDeriv 1) * ν univ
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y ((∂μ/∂ν) x).toReal)
          ∂f.curvatureMeasureReal ∂ν + ENNReal.ofReal (f.rightDeriv 1) * μ univ := by
    rw [← lintegral_const, ← lintegral_add_right _ measurable_const]
    have h_eq : ∀ᵐ x ∂ν, f ((∂μ/∂ν) x) + ENNReal.ofReal (f.rightDeriv 1)
        = ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y ((∂μ/∂ν) x).toReal) ∂f.curvatureMeasureReal
          + ENNReal.ofReal (f.rightDeriv 1) * (∂μ/∂ν) x := by
      filter_upwards [μ.rnDeriv_ne_top ν] with x hx
      rw [lintegral_statInfoFun_curvatureMeasureReal_add hx]
    rw [lintegral_congr_ae h_eq,
      lintegral_add_left (Measurable.lintegral_prod_right h_meas.ennreal_ofReal),
      lintegral_const_mul _ (μ.measurable_rnDeriv ν), Measure.lintegral_rnDeriv h_ac]
  rw [this, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    DivFunction.lintegral_curvatureMeasureReal]
  exact Measurable.lintegral_prod_left h_meas.ennreal_ofReal

/-- Integral representation of `fDiv f μ ν` in terms of the f-divergences of the
`statInfoDivFun 1 x` and the curvature measure of `f`. The Taylor formula at `1` carries a linear
term, hence the correction term `f.rightDeriv 1 * (μ univ - ν univ)`, split here on both
sides of the equality to stay in `ℝ≥0∞`. See `fDiv_eq_lintegral_fDiv_statInfoDivFun` for the case
`f.rightDeriv 1 = 0`. -/
theorem fDiv_add_eq_lintegral_fDiv_statInfoDivFun_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν + ENNReal.ofReal (f.rightDeriv 1) * ν univ
      = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal
        + ENNReal.ofReal (f.rightDeriv 1) * μ univ := by
  have h_ac : ν.withDensity (∂μ/∂ν) ≪ ν := withDensity_absolutelyContinuous _ _
  have hμ : μ univ = ν.withDensity (∂μ/∂ν) univ + μ.singularPart ν univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [add_apply, add_comm]
  have h_in : ∀ x, fDiv (statInfoDivFun 1 x) μ ν
      = fDiv (statInfoDivFun 1 x) (ν.withDensity (∂μ/∂ν)) ν
        + (statInfoDivFun 1 x).derivAtTop * μ.singularPart ν univ :=
    fun x ↦ fDiv_eq_add_withDensity_derivAtTop μ ν
  simp_rw [h_in]
  rw [fDiv_eq_add_withDensity_derivAtTop,
    lintegral_add_right _ (measurable_derivAtTop_statInfoDivFun.mul_const _),
    lintegral_mul_const _ measurable_derivAtTop_statInfoDivFun,
    fDiv_of_absolutelyContinuous h_ac,
    f.lintegral_curvatureMeasureReal measurable_fDiv_statInfoDivFun_right,
    ← lintegral_derivAtTop_statInfoDivFun, hμ]
  have h2 := lintegral_f_rnDeriv_add_eq_lintegral_fDiv_statInfoDivFun_add_of_ac
    (f := f) h_ac
  calc ∫⁻ x, f ((∂ν.withDensity (∂μ/∂ν)/∂ν) x) ∂ν
        + (∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
            + ENNReal.ofReal (f.rightDeriv 1)) * μ.singularPart ν univ
        + ENNReal.ofReal (f.rightDeriv 1) * ν univ
      = (∫⁻ x, f ((∂ν.withDensity (∂μ/∂ν)/∂ν) x) ∂ν
          + ENNReal.ofReal (f.rightDeriv 1) * ν univ)
        + ((∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal)
            * μ.singularPart ν univ
          + ENNReal.ofReal (f.rightDeriv 1) * μ.singularPart ν univ) := by ring
    _ = (∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) (ν.withDensity (∂μ/∂ν)) ν ∂f.curvatureMeasure
          + ENNReal.ofReal (f.rightDeriv 1) * ν.withDensity (∂μ/∂ν) univ)
        + ((∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal)
            * μ.singularPart ν univ
          + ENNReal.ofReal (f.rightDeriv 1) * μ.singularPart ν univ) := by rw [h2]
    _ = _ := by ring

/-- Integral representation of `fDiv f μ ν` in terms of the f-divergences of the
`statInfoDivFun 1 x` and the curvature measure of `f`, for `f` with `f.rightDeriv 1 = 0`. -/
lemma fDiv_eq_lintegral_fDiv_statInfoDivFun [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : f.rightDeriv 1 = 0) :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  simpa [hfderiv_one] using fDiv_add_eq_lintegral_fDiv_statInfoDivFun_add (f := f) (μ := μ) (ν := ν)

end StatInfoFun

section StatInfo

/-- **Integral representation of f-divergences** in terms of statistical informations: for finite
measures with the same mass, `D_f(μ, ν) = ∫ y, I_{(1, y)}(μ, ν) ∂γ_f`, where `I_π` is the
statistical information with prior `π` and `γ_f` is the curvature measure of `f`. -/
theorem fDiv_eq_lintegral_statInfo [IsFiniteMeasure μ] (h_univ : μ univ = ν univ) :
    fDiv f μ ν
      = ∫⁻ y, statInfo μ ν (Measure.boolMeasure 1 (ENNReal.ofReal y)) ∂f.curvatureMeasureReal := by
  have : IsFiniteMeasure ν := ⟨h_univ ▸ measure_lt_top μ univ⟩
  have h := fDiv_add_eq_lintegral_fDiv_statInfoDivFun_add (f := f) (μ := μ) (ν := ν)
  rw [h_univ, ENNReal.add_left_inj (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _))] at h
  rw [h]
  refine lintegral_congr_ae ?_
  filter_upwards [f.ae_nonneg_curvatureMeasureReal] with y hy
  have : IsFiniteMeasure (Measure.boolMeasure 1 (ENNReal.ofReal y)) :=
    Measure.isFiniteMeasure_boolMeasure ENNReal.one_ne_top ENNReal.ofReal_ne_top
  rw [statInfo_eq_fDiv μ ν h_univ, Measure.boolMeasure_apply_false,
    Measure.boolMeasure_apply_true, ENNReal.toReal_one, ENNReal.toReal_ofReal hy]

/-- **Integral representation of f-divergences** of Liese and Vajda: for finite measures with the
same mass, `D_f(μ, ν) = ∫ p, I_{(p, 1 - p)}(μ, ν) ∂Γ_f`, where `I_{(p, 1 - p)}` is the DeGroot
statistical information (the statistical information with prior `(p, 1 - p)`) and `Γ_f` is the
image of the measure `(1 + y) γ_f(dy)` by `y ↦ (1 + y)⁻¹`, for `γ_f` the curvature measure of
`f`. -/
theorem fDiv_eq_lintegral_statInfo_prior [IsFiniteMeasure μ] (h_univ : μ univ = ν univ) :
    fDiv f μ ν
      = ∫⁻ p, statInfo μ ν (Measure.boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)))
          ∂((f.curvatureMeasureReal.withDensity fun y ↦ ENNReal.ofReal (1 + y)).map
            fun y ↦ (1 + y)⁻¹) := by
  have : IsFiniteMeasure ν := ⟨h_univ ▸ measure_lt_top μ univ⟩
  have h_meas : Measurable fun p : ℝ ↦
      statInfo μ ν (Measure.boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))) :=
    (measurable_statInfo_boolMeasure_ofReal μ ν).comp (f := fun p : ℝ ↦ (p, 1 - p)) (by fun_prop)
  have h_meas' : Measurable fun y : ℝ ↦ statInfo μ ν
      (Measure.boolMeasure (ENNReal.ofReal (1 + y)⁻¹) (ENNReal.ofReal (1 - (1 + y)⁻¹))) :=
    h_meas.comp (by fun_prop)
  rw [lintegral_map h_meas (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) h_meas',
    fDiv_eq_lintegral_statInfo h_univ]
  refine lintegral_congr_ae ?_
  filter_upwards [f.ae_nonneg_curvatureMeasureReal] with y hy
  have hy1 : 0 < 1 + y := by linarith
  simp only [Pi.mul_apply]
  rw [← statInfo_smul_prior μ ν _ ENNReal.ofReal_ne_top, Measure.smul_boolMeasure,
    ← ENNReal.ofReal_mul hy1.le, ← ENNReal.ofReal_mul hy1.le, mul_inv_cancel₀ hy1.ne',
    ENNReal.ofReal_one]
  congr 3
  field_simp
  ring

end StatInfo

end ProbabilityTheory
