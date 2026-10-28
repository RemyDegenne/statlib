/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.DivFunction.DerivAtTop
public import Mathlib.Topology.Order.LeftRightLim
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Divergence functions from real functions

## Main definitions

* `DivFunction.ofReal f hf hf_one`: the divergence function built from a function `f : ℝ → ℝ`
  which is convex on `(0, ∞)` with `f 1 = 0`. It is `ENNReal.ofReal ∘ f` on `(0, ∞)`, extended by
  its limits at `0` and `∞`.

## Main statements

* `DivFunction.derivAtTop_ofReal`: the `derivAtTop` of `ofReal f hf hf_one` is the slope at infinity
  `derivAtTop f` of `f`, truncated at `0`.
* `lintegral_ofReal_eq_integral_of_continuous`,
  `lintegral_ofReal_ne_top_iff_integrable_of_continuous`: relation between the integral of
  `ofReal f hf hf_one` composed with a Radon-Nikodym derivative and the Bochner integral of `f`
  composed with it.

-/

@[expose] public section

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : ℝ → ℝ}

namespace DivFunction

section OfReal

section OfRealFun

/-- The function `ℝ≥0∞ → ℝ≥0∞` underlying `DivFunction.ofReal`: it is `ENNReal.ofReal ∘ f` on
`(0, ∞)`, extended by its limits at `0` and `∞` to ensure continuity. -/
noncomputable
def ofRealFun (f : ℝ → ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = 0 then Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0
  else if x = ∞ then limsup (fun x ↦ ENNReal.ofReal (f x)) atTop
  else ENNReal.ofReal (f x.toReal)

@[simp]
lemma ofRealFun_zero : ofRealFun f 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofRealFun]

@[simp]
lemma ofRealFun_top : ofRealFun f ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofRealFun]

lemma ofRealFun_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofRealFun f x = ENNReal.ofReal (f x.toReal) := by
  simp [ofRealFun, hx_zero, hx_top]

lemma tendsto_ofReal_comp_nhdsGT_zero (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) (𝓝[>] 0) (𝓝 (ofRealFun f 0)) := by
  rw [ofRealFun_zero]
  -- `ENNReal.ofReal ∘ f` is antitone on `(0, 1]`: extend it to `(0, ∞)` by capping at 1
  have h_anti : AntitoneOn (fun x ↦ ENNReal.ofReal (f (min x 1))) (Ioi 0) := by
    intro x hx y hy hxy
    exact hf.antitoneOn_ofReal_comp hf_one ⟨lt_min hx one_pos, min_le_right _ _⟩
      ⟨lt_min hy one_pos, min_le_right _ _⟩ (min_le_min_right _ hxy)
  have h_tendsto := h_anti.tendsto_nhdsGT (OrderTop.bddAbove _)
  have h_eq : (fun x ↦ ENNReal.ofReal (f (min x 1)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun x ↦ ENNReal.ofReal (f x) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    simp [min_eq_left hx.2.le]
  rw [rightLim_eq_of_tendsto (h_tendsto.congr' h_eq)]
  exact h_tendsto.congr' h_eq

lemma tendsto_ofReal_comp_atTop (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) atTop (𝓝 (ofRealFun f ∞)) := by
  rw [ofRealFun_top]
  obtain ⟨y, hy⟩ := (hf.monotoneOn_ofReal_comp hf_one).exists_tendsto_atTop
  rw [hy.limsup_eq]
  exact hy

lemma continuous_ofRealFun (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Continuous (ofRealFun f) := by
  have h_cont : ContinuousOn f (Ioi 0) := hf.continuousOn isOpen_Ioi
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx0 : x = 0
  · subst hx0
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, ?_⟩
    · rw [← ENNReal.bot_eq_zero, Iic_bot]
      exact continuousWithinAt_singleton
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h_toReal : Tendsto ENNReal.toReal (𝓝[>] (0 : ℝ≥0∞)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top)
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ENNReal.zero_lt_top)] with y hy hy_top
        exact ENNReal.toReal_pos hy.ne' hy_top.ne
    rw [ContinuousWithinAt]
    refine ((tendsto_ofReal_comp_nhdsGT_zero hf hf_one).comp h_toReal).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ENNReal.zero_lt_top)] with y hy hy_top
    simp [ofRealFun_apply hy.ne' hy_top.ne]
  by_cases hx_top : x = ∞
  · subst hx_top
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, ?_⟩
    swap
    · rw [Ici_top]
      exact continuousWithinAt_singleton
    rw [← continuousWithinAt_Iio_iff_Iic]
    have h_toReal : Tendsto ENNReal.toReal (𝓝[<] (∞ : ℝ≥0∞)) atTop := by
      refine tendsto_atTop.mpr fun b ↦ ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ENNReal.ofReal_lt_top)] with y hy hy_gt
      exact (ENNReal.ofReal_le_iff_le_toReal hy.ne).mp hy_gt.le
    rw [ContinuousWithinAt]
    refine ((tendsto_ofReal_comp_atTop hf hf_one).comp h_toReal).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ENNReal.zero_lt_top)] with y hy hy_pos
    simp [ofRealFun_apply hy_pos.ne' hy.ne]
  have h1 : ContinuousAt (fun y : ℝ≥0∞ ↦ ENNReal.ofReal (f y.toReal)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((h_cont.continuousAt (Ioi_mem_nhds (ENNReal.toReal_pos hx0 hx_top))).comp
        (ENNReal.continuousAt_toReal hx_top))
  refine h1.congr ?_
  filter_upwards [Ioo_mem_nhds (pos_iff_ne_zero.mpr hx0) (lt_top_iff_ne_top.mpr hx_top)] with y hy
  exact (ofRealFun_apply hy.1.ne' hy.2.ne).symm

lemma convexOn_ofRealFun (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    ConvexOn ℝ≥0 univ (ofRealFun f) := by
  have h_cont := continuous_ofRealFun hf hf_one
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ ?_⟩
  -- the convexity inequality on `(0, ∞) × (0, ∞)` follows from the convexity of `f`
  have h_Ioo : ∀ x ∈ Ioo (0 : ℝ≥0∞) ∞, ∀ y ∈ Ioo (0 : ℝ≥0∞) ∞,
      ofRealFun f (a • x + b • y) ≤ a • ofRealFun f x + b • ofRealFun f y := by
    intro x hx y hy
    have hxy_top : a • x + b • y ≠ ∞ := by
      simp only [ENNReal.smul_def, smul_eq_mul]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hx.2.ne,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hy.2.ne⟩
    have hxy_zero : a • x + b • y ≠ 0 := by
      intro h
      rw [add_eq_zero, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_eq_zero,
        mul_eq_zero] at h
      simp only [ENNReal.coe_eq_zero, hx.1.ne', hy.1.ne', or_false] at h
      simp [h.1, h.2] at hab
    have h_toReal : (a • x + b • y).toReal = a * x.toReal + b * y.toReal := by
      simp only [ENNReal.smul_def, smul_eq_mul]
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hx.2.ne)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hy.2.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, ENNReal.coe_toReal]
    rw [ofRealFun_apply hxy_zero hxy_top, ofRealFun_apply hx.1.ne' hx.2.ne,
      ofRealFun_apply hy.1.ne' hy.2.ne, h_toReal]
    have h_cvx := hf.2 (mem_Ioi.mpr (ENNReal.toReal_pos hx.1.ne' hx.2.ne))
      (mem_Ioi.mpr (ENNReal.toReal_pos hy.1.ne' hy.2.ne)) a.coe_nonneg b.coe_nonneg
      (by rw [← NNReal.coe_add, hab, NNReal.coe_one])
    simp only [smul_eq_mul] at h_cvx
    calc ENNReal.ofReal (f (a * x.toReal + b * y.toReal))
      _ ≤ ENNReal.ofReal (a * f x.toReal + b * f y.toReal) := ENNReal.ofReal_le_ofReal h_cvx
      _ ≤ ENNReal.ofReal (a * f x.toReal) + ENNReal.ofReal (b * f y.toReal) :=
        ENNReal.ofReal_add_le
      _ = a • ENNReal.ofReal (f x.toReal) + b • ENNReal.ofReal (f y.toReal) := by
        rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def,
          ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  -- the inequality is a closed condition and `(0, ∞) × (0, ∞)` is dense
  have h_closed : IsClosed {p : ℝ≥0∞ × ℝ≥0∞ |
      ofRealFun f (a • p.1 + b • p.2) ≤ a • ofRealFun f p.1 + b • ofRealFun f p.2} := by
    simp only [ENNReal.smul_def, smul_eq_mul]
    refine isClosed_le ?_ ?_
    · exact h_cont.comp (((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp continuous_fst).add
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp continuous_snd))
    · exact Continuous.add
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (h_cont.comp continuous_fst))
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (h_cont.comp continuous_snd))
  have h_subset : Ioo (0 : ℝ≥0∞) ∞ ×ˢ Ioo (0 : ℝ≥0∞) ∞ ⊆ {p : ℝ≥0∞ × ℝ≥0∞ |
      ofRealFun f (a • p.1 + b • p.2) ≤ a • ofRealFun f p.1 + b • ofRealFun f p.2} :=
    fun p hp ↦ h_Ioo p.1 hp.1 p.2 hp.2
  have h_closure : closure (Ioo (0 : ℝ≥0∞) ∞ ×ˢ Ioo (0 : ℝ≥0∞) ∞) = univ := by
    rw [closure_prod_eq, closure_Ioo ENNReal.zero_ne_top, ← ENNReal.bot_eq_zero, Icc_bot_top,
      univ_prod_univ]
  have h := h_closed.closure_subset_iff.mpr h_subset
  rw [h_closure] at h
  exact h (mem_univ (x, y))

end OfRealFun

/-- Build a `DivFunction` from a function `f : ℝ → ℝ` which is convex on `Ioi 0` and satisfies
`f 1 = 0`. On `(0, ∞)` it is `ENNReal.ofReal ∘ f`, extended by its limits at `0` and `∞`. -/
noncomputable
def ofReal (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) : DivFunction where
  toFun := ofRealFun f
  one := by simp [ofRealFun, hf_one]
  convexOn' := convexOn_ofRealFun hf hf_one
  continuous' := continuous_ofRealFun hf hf_one

variable {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

section OfRealApply

@[simp]
lemma ofReal_apply_zero :
    ofReal f hf hf_one 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofReal]

lemma ofReal_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofReal f hf hf_one 0 = ENNReal.ofReal (f 0) := by
  rw [ofReal_apply_zero]
  exact rightLim_eq_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hf_cont)

@[simp]
lemma ofReal_apply_top :
    ofReal f hf hf_one ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofReal]

lemma ofReal_apply_top_of_tendsto_atTop (h : Tendsto f atTop atTop) :
    ofReal f hf hf_one ∞ = ∞ := by
  rw [ofReal_apply_top]
  refine Tendsto.limsup_eq ?_
  rwa [ENNReal.tendsto_ofReal_nhds_top]

lemma ofReal_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  simp [ofReal, ofRealFun_apply hx_zero hx_top]

lemma ofReal_apply_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  by_cases hx0 : x = 0
  · simp [hx0, ofReal_apply_zero_of_continuousWithinAt hf_cont]
  · exact ofReal_apply hx0 hx

lemma realFun_ofReal_apply (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) {x : ℝ} (hx : 0 < x) :
    (ofReal f hf hf_one).realFun x = f x := by
  rw [realFun, ofReal_apply (by simp [hx]) (by simp), ENNReal.toReal_ofReal hx.le,
    ENNReal.toReal_ofReal (hf_nonneg x hx)]

end OfRealApply

section DerivAtTop

/-- The `derivAtTop` of `ofReal f hf hf_one` is the slope at infinity `derivAtTop f` of `f`,
truncated at `0`. -/
lemma derivAtTop_ofReal : (ofReal f hf hf_one).derivAtTop = (_root_.derivAtTop f).toENNReal := by
  refine tendsto_nhds_unique (ofReal f hf hf_one).tendsto_div_nhdsLT_top ?_
  have h_lim : Tendsto (fun y : ℝ≥0∞ ↦ (((f y.toReal / y.toReal : ℝ) : EReal)).toENNReal)
      (𝓝[<] ∞) (𝓝 (_root_.derivAtTop f).toENNReal) :=
    (EReal.continuous_toENNReal.tendsto _).comp (hf.tendsto_derivAtTop.comp
      ENNReal.tendsto_toReal_atTop)
  refine h_lim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with y hy
  have hy_pos : 0 < y.toReal := ENNReal.toReal_pos hy.1.ne' hy.2.ne
  rw [EReal.real_coe_toENNReal, ofReal_apply hy.1.ne' hy.2.ne, ENNReal.ofReal_div_of_pos hy_pos,
    ENNReal.ofReal_toReal hy.2.ne]

lemma derivAtTop_ofReal_of_tendsto_nhds {y : ℝ}
    (h : Tendsto (fun x ↦ derivWithin f (Ioi x) x) atTop (𝓝 y)) :
    (ofReal f hf hf_one).derivAtTop = ENNReal.ofReal y := by
  rw [derivAtTop_ofReal, hf.derivAtTop_eq_of_tendsto_rightDeriv h, EReal.real_coe_toENNReal]

lemma derivAtTop_ofReal_of_tendsto_atTop
    (h : Tendsto (fun x ↦ derivWithin f (Ioi x) x) atTop atTop) :
    (ofReal f hf hf_one).derivAtTop = ∞ := by
  rw [derivAtTop_ofReal, hf.derivAtTop_eq_top_of_tendsto_rightDeriv h, EReal.toENNReal_top]

end DerivAtTop

section Integral

lemma lintegral_ofReal_eq_top_of_not_integrable [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_int : ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞ := by
  refine lintegral_eq_top_of_not_integrable_realFun ?_
  suffices ¬ IntegrableOn
      (fun x ↦ (ofReal f hf hf_one).realFun (μ.rnDeriv ν x).toReal)
      {x | μ.rnDeriv ν x ≠ 0} ν from
    fun h ↦ this h.integrableOn
  rw [← integrableOn_univ] at h_int
  have : (univ : Set α) = {x | μ.rnDeriv ν x ≠ 0} ∪ {x | μ.rnDeriv ν x = 0} := by
    ext x
    by_cases h : μ.rnDeriv ν x = 0 <;> simp [h]
  rw [this, integrableOn_union] at h_int
  have h_int_zero : IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) {x | μ.rnDeriv ν x = 0} ν := by
    refine (integrableOn_congr_fun ?_ ?_).mpr
      (integrableOn_const (C := f 0) (measure_ne_top _ _))
    · intro x hx
      simp only [mem_ofPred_eq] at hx
      simp [hx]
    · exact μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  simp only [ne_eq, h_int_zero, and_true] at h_int
  convert h_int using 1
  refine integrableOn_congr_fun_ae ((ae_restrict_iff' ?_).mpr ?_)
  · exact (μ.measurable_rnDeriv ν (measurableSet_singleton 0)).compl
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx_zero
  rw [DivFunction.realFun_ofReal_apply fun x hx ↦ hf_nonneg x hx.le]
  exact ENNReal.toReal_pos hx_zero hx_top

lemma lintegral_ofReal_of_continuous [SigmaFinite μ]
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
  refine lintegral_congr_ae ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  exact ofReal_apply_of_continuousWithinAt hf_cont hx

lemma lintegral_ofReal_eq_integral_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, f (μ.rnDeriv ν x).toReal ∂ν) := by
  rw [DivFunction.lintegral_ofReal_of_continuous hf_cont,
    ofReal_integral_eq_lintegral_ofReal h_int]
  refine ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma lintegral_ofReal_ne_top_iff_integrable_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν ≠ ∞
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [lintegral_ofReal_of_continuous h_cont, lintegral_ofReal_ne_top_iff_integrable]
  · exact (hf.measurable_comp_of_nonneg (μ.measurable_rnDeriv ν).ennreal_toReal
      fun _ ↦ ENNReal.toReal_nonneg).aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma lintegral_ofReal_eq_top_iff_not_integrable_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞
      ↔ ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [← lintegral_ofReal_ne_top_iff_integrable_of_continuous hf_nonneg h_cont, not_not]

end Integral

end OfReal

end DivFunction

end ProbabilityTheory
