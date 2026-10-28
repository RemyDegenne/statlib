/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.FDiv.DivFunction.Basic

/-!
# Derivative at infinity of a divergence function

## Main definitions

* `DivFunction.derivAtTop`: the limit of `f y / y` as `y → ∞`, an element of `ℝ≥0∞`. It is defined
  as a `limsup`, so that it is always defined.

## Main statements

* `DivFunction.tendsto_div_nhdsLT_top`: `f y / y` tends to `f.derivAtTop`. More generally, so does
  `f y / (y - a)` for every `a ≠ ∞` (`DivFunction.tendsto_div_sub_nhdsLT_top`).
* `DivFunction.le_add_derivAtTop`: for `y ≤ x`, `f x ≤ f y + f.derivAtTop * (x - y)`.
* `DivFunction.derivAtTop_add`, `DivFunction.derivAtTop_smul`, `DivFunction.derivAtTop_mono`:
  behavior under addition, scalar multiplication and pointwise order.

## Implementation details

The limit of `f y / y` exists because the slope `f y / (y - 1)` of `f` from the point `1`, where `f`
vanishes, is nondecreasing on `(1, ∞)` by convexity (`DivFunction.div_sub_one_le_div_sub_one`).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), where `derivAtTop` was defined as the limit
of the right derivative of `f`.
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.DivFunction

variable {α : Type*} {mα : MeasurableSpace α} {f g : DivFunction}

/-- The derivative at infinity of a divergence function: the limit of `f y / y` as `y → ∞`
(`tendsto_div_nhdsLT_top`). -/
noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := limsup (fun y ↦ f y / y) (𝓝[<] ∞)

/-- If `x` is the convex combination `u • y + v • z` of `y ≤ x ≤ z`, then `x - y = v * (z - y)`. -/
private lemma sub_eq_mul_sub {x y z : ℝ≥0∞} {u v : ℝ≥0} (hyx : y ≤ x) (hxz : x ≤ z) (hz : z ≠ ∞)
    (huv : u + v = 1) (hx : u • y + v • z = x) :
    x - y = v * (z - y) := by
  have hx_top : x ≠ ∞ := ne_top_of_le_ne_top hz hxz
  have hy_top : y ≠ ∞ := ne_top_of_le_ne_top hx_top hyx
  have hu : (u : ℝ) = 1 - v := by rw [eq_sub_iff_add_eq, ← NNReal.coe_add, huv, NNReal.coe_one]
  have hx_real : x.toReal = u * y.toReal + v * z.toReal := by
    rw [← hx, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hy_top)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hz),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.sub_ne_top hx_top)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.sub_ne_top hz)),
    ENNReal.toReal_sub_of_le hyx hx_top, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le (hyx.trans hxz) hz, ENNReal.coe_toReal, hx_real, hu]
  ring

/-- The slope of a divergence function from the point `1`, where it vanishes, is nondecreasing on
`(1, ∞)`. -/
lemma div_sub_one_le_div_sub_one {y z : ℝ≥0∞} (hy : 1 < y) (hyz : y ≤ z) (hz : z ≠ ∞) :
    f y / (y - 1) ≤ f z / (z - 1) := by
  obtain ⟨u, v, huv, hy_eq⟩ := ENNReal.exists_nnreal_smul_add_eq hz hy.le hyz
  have hfy : f y ≤ v * f z := by
    calc f y = f (u • 1 + v • z) := by rw [hy_eq]
    _ ≤ u • f 1 + v • f z := f.convexOn.2 (mem_univ _) (mem_univ _) zero_le zero_le huv
    _ = v * f z := by simp [ENNReal.smul_def]
  have h_sub : y - 1 = v * (z - 1) := sub_eq_mul_sub hy.le hyz hz huv hy_eq
  have hv : (v : ℝ≥0∞) ≠ 0 := by
    intro hv
    rw [hv, zero_mul, tsub_eq_zero_iff_le] at h_sub
    exact hy.not_ge h_sub
  calc f y / (y - 1) ≤ v * f z / (v * (z - 1)) := by rw [h_sub]; gcongr
  _ = f z / (z - 1) := ENNReal.mul_div_mul_left _ _ hv ENNReal.coe_ne_top

private lemma tendsto_sub_div_self {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto (fun z ↦ (z - a) / z) (𝓝[<] ∞) (𝓝 1) := by
  have h_inv : Tendsto (fun z : ℝ≥0∞ ↦ z⁻¹) (𝓝[<] ∞) (𝓝 0) := by
    simpa using (continuous_inv.tendsto ∞).mono_left nhdsWithin_le_nhds
  have h_lim : Tendsto (fun z ↦ 1 - a * z⁻¹) (𝓝[<] ∞) (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds (ENNReal.Tendsto.const_mul h_inv (Or.inr ha))
      (Or.inl ENNReal.one_ne_top)
  refine h_lim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with z hz
  rw [ENNReal.sub_div fun _ _ ↦ hz.1.ne', ENNReal.div_self hz.1.ne' hz.2.ne, div_eq_mul_inv]

/-- The common limit of `f y / (y - a)` for all `a ≠ ∞`. -/
private lemma exists_tendsto_div_sub (f : DivFunction) :
    ∃ S, ∀ a, a ≠ ∞ → Tendsto (fun y ↦ f y / (y - a)) (𝓝[<] ∞) (𝓝 S) := by
  have h_mono : MonotoneOn (fun y ↦ f y / (y - 1)) (Ioo 1 ∞) :=
    fun y hy z hz hyz ↦ f.div_sub_one_le_div_sub_one hy.1 hyz hz.2.ne
  have h_slope := h_mono.tendsto_nhdsWithin_Ioo_left ⟨2, ENNReal.one_lt_two, ENNReal.ofNat_lt_top⟩
    (OrderTop.bddAbove _)
  refine ⟨sSup ((fun y ↦ f y / (y - 1)) '' Ioo 1 ∞), fun a ha ↦ ?_⟩
  have h_ratio : Tendsto (fun y ↦ (y - 1) / y * (y / (y - a))) (𝓝[<] ∞) (𝓝 1) := by
    have h_inv : Tendsto (fun y ↦ ((y - a) / y)⁻¹) (𝓝[<] ∞) (𝓝 1) := by
      simpa [Function.comp_def] using (continuous_inv.tendsto 1).comp (tendsto_sub_div_self ha)
    have h_eq : (fun y ↦ ((y - a) / y)⁻¹) =ᶠ[𝓝[<] ∞] fun y ↦ y / (y - a) := by
      filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with y hy
      rw [ENNReal.inv_div (a := y - a) (b := y) (Or.inl hy.2.ne) (Or.inl hy.1.ne')]
    simpa using ENNReal.Tendsto.mul (tendsto_sub_div_self ENNReal.one_ne_top)
      (Or.inr ENNReal.one_ne_top) (h_inv.congr' h_eq) (Or.inr ENNReal.one_ne_top)
  refine (ENNReal.Tendsto.mul h_slope (Or.inr ENNReal.one_ne_top) h_ratio
    (Or.inl one_ne_zero)).congr' ?_ |>.mono_right (by rw [mul_one])
  filter_upwards [Ioo_mem_nhdsLT (max_lt ENNReal.one_lt_top ha.lt_top)] with y hy
  have hy1 : 1 < y := (le_max_left _ _).trans_lt hy.1
  have hya : a < y := (le_max_right _ _).trans_lt hy.1
  rw [ENNReal.div_mul_div_cancel (b := y) (zero_lt_one.trans hy1).ne' hy.2.ne,
    ENNReal.div_mul_div_cancel (b := y - 1) (tsub_pos_of_lt hy1).ne' (ENNReal.sub_ne_top hy.2.ne)]

/-- `f y / (y - a)` tends to `f.derivAtTop` as `y → ∞`, for every `a ≠ ∞`. -/
lemma tendsto_div_sub_nhdsLT_top {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto (fun y ↦ f y / (y - a)) (𝓝[<] ∞) (𝓝 f.derivAtTop) := by
  obtain ⟨S, hS⟩ := f.exists_tendsto_div_sub
  have h0 : derivAtTop f = S := by
    simpa [derivAtTop] using (hS 0 ENNReal.zero_ne_top).limsup_eq
  exact h0 ▸ hS a ha

/-- `f y / y` tends to `f.derivAtTop` as `y → ∞`. -/
lemma tendsto_div_nhdsLT_top : Tendsto (fun y ↦ f y / y) (𝓝[<] ∞) (𝓝 f.derivAtTop) := by
  simpa using f.tendsto_div_sub_nhdsLT_top ENNReal.zero_ne_top

lemma le_add_derivAtTop_of_ne_top {x y : ℝ≥0∞} (hyx : y ≤ x) (hx : x ≠ ∞) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  rcases hyx.eq_or_lt with rfl | hyx
  · simp
  have hy : y ≠ ∞ := ne_top_of_lt hyx
  -- write `x` as a convex combination of `y` and `z ∈ (x, ∞)`, and let `z → ∞`
  have h_le : ∀ z ∈ Ioo x ∞, f x ≤ f y + (x - y) * (f z / (z - y)) := by
    intro z hz
    obtain ⟨u, v, huv, hx_eq⟩ := ENNReal.exists_nnreal_smul_add_eq hz.2.ne hyx.le hz.1.le
    have h_sub := sub_eq_mul_sub hyx.le hz.1.le hz.2.ne huv hx_eq
    have hzy : z - y ≠ 0 := (tsub_pos_of_lt (hyx.trans hz.1)).ne'
    have hv : (v : ℝ≥0∞) = (x - y) / (z - y) := by
      rw [ENNReal.eq_div_iff hzy (ENNReal.sub_ne_top hz.2.ne), h_sub, mul_comm]
    calc f x = f (u • y + v • z) := by rw [hx_eq]
    _ ≤ u • f y + v • f z := f.convexOn.2 (mem_univ _) (mem_univ _) zero_le zero_le huv
    _ ≤ f y + v * f z := by
      rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
      gcongr
      exact mul_le_of_le_one_left' (ENNReal.coe_le_one_iff.mpr (le_self_add.trans_eq huv))
    _ = f y + (x - y) * (f z / (z - y)) := by
      rw [hv, div_eq_mul_inv, div_eq_mul_inv]
      ring
  have h_lim : Tendsto (fun z ↦ f y + (x - y) * (f z / (z - y))) (𝓝[<] ∞)
      (𝓝 (f y + (x - y) * f.derivAtTop)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (f.tendsto_div_sub_nhdsLT_top hy)
      (Or.inr (ENNReal.sub_ne_top hx)))
  rw [mul_comm]
  exact ge_of_tendsto h_lim
    (eventually_of_mem (Ioo_mem_nhdsLT (lt_top_iff_ne_top.mpr hx)) fun z hz ↦ h_le z hz)

/-- A divergence function lies below its asymptote of slope `f.derivAtTop` through any point. -/
lemma le_add_derivAtTop {x y : ℝ≥0∞} (hyx : y ≤ x) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  by_cases hx : x = ∞
  swap; · exact f.le_add_derivAtTop_of_ne_top hyx hx
  subst hx
  by_cases hy : y = ∞
  · simp [hy]
  by_cases hd : f.derivAtTop = 0
  · simp only [hd, zero_mul, add_zero]
    refine le_of_tendsto ((f.continuous.tendsto ∞).mono_left (nhdsWithin_le_nhds (s := Iio ∞))) ?_
    filter_upwards [Ioo_mem_nhdsLT (lt_top_iff_ne_top.mpr hy)] with z hz
    simpa [hd] using f.le_add_derivAtTop_of_ne_top hz.1.le hz.2.ne
  · rw [ENNReal.top_sub hy, ENNReal.mul_top hd]
    simp

lemma apply_add_le (x y : ℝ≥0∞) : f (x + y) ≤ f x + f.derivAtTop * y := by
  by_cases hx : x = ∞
  · simp [hx]
  simpa [ENNReal.add_sub_cancel_left hx] using f.le_add_derivAtTop (le_self_add : x ≤ x + y)

/-- For `1 ≤ y`, `f y ≤ f.derivAtTop * y`. -/
lemma apply_le_derivAtTop_mul {y : ℝ≥0∞} (hy : 1 ≤ y) : f y ≤ f.derivAtTop * y := by
  have h := f.apply_add_le 1 (y - 1)
  rw [add_tsub_cancel_of_le hy, apply_one, zero_add] at h
  exact h.trans (by gcongr; exact tsub_le_self)

/-- `derivAtTop` is monotone: if `f ≤ g` pointwise, then `f.derivAtTop ≤ g.derivAtTop`. -/
lemma derivAtTop_mono (hfg : ∀ x, f x ≤ g x) : f.derivAtTop ≤ g.derivAtTop :=
  le_of_tendsto_of_tendsto' (b := 𝓝[<] ∞) f.tendsto_div_nhdsLT_top g.tendsto_div_nhdsLT_top
    fun y ↦ ENNReal.div_le_div_right (hfg y) y

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := by
  simp [derivAtTop]

@[simp]
lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := by
  refine tendsto_nhds_unique (f + g).tendsto_div_nhdsLT_top ?_
  simp only [add_apply, ENNReal.add_div]
  exact f.tendsto_div_nhdsLT_top.add g.tendsto_div_nhdsLT_top

@[simp]
lemma derivAtTop_smul {c : ℝ≥0} : (c • f).derivAtTop = c * f.derivAtTop := by
  refine tendsto_nhds_unique (c • f).tendsto_div_nhdsLT_top ?_
  simp only [smul_apply, mul_div_assoc]
  exact ENNReal.Tendsto.const_mul f.tendsto_div_nhdsLT_top (Or.inr ENNReal.coe_ne_top)

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_zero : f 0 ≠ ∞) (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞ := by
  have h x : f (μ.rnDeriv ν x) ≤ f 0 + f.derivAtTop * μ.rnDeriv ν x := by
    simpa using f.apply_add_le 0 (μ.rnDeriv ν x)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono h)
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul _ (μ.measurable_rnDeriv ν)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hf_zero (measure_ne_top _ _),
    ENNReal.mul_ne_top hf_deriv (ne_top_of_le_ne_top (measure_ne_top μ _)
      Measure.lintegral_rnDeriv_le)⟩

end ProbabilityTheory.DivFunction
