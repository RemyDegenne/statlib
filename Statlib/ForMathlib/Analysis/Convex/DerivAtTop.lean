/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Statlib.ForMathlib.Convex
public import Statlib.ForMathlib.Topology.Order.MonotoneConvergence

/-!
# Slope at infinity of a real function

## Main definitions

* `derivAtTop f`: the limit at `+∞` of `f x / x`, for `f : ℝ → ℝ`, as an `EReal`. It is defined as a
  `limsup`, so that it is always defined.

## Main statements

* `ConvexOn.tendsto_derivAtTop`: for a function convex on `(a, ∞)`, `f x / x` tends to
  `derivAtTop f`.
* `ConvexOn.tendsto_rightDeriv_derivAtTop`: for such a function, the right derivative
  `derivWithin f (Ioi x) x` also tends to `derivAtTop f`. This is how `derivAtTop` is computed in
  practice (`ConvexOn.derivAtTop_eq_of_tendsto_rightDeriv`,
  `ConvexOn.derivAtTop_eq_top_of_tendsto_rightDeriv`).
* `ConvexOn.le_add_derivAtTop`: for a function convex on `[0, ∞)` and `0 ≤ y ≤ x`,
  `f x ≤ f y + derivAtTop f * (x - y)`.
* `derivAtTop_add`: additivity on convex functions.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), where `derivAtTop f` was defined as the limit
of the right derivative.
-/

@[expose] public section

open Filter Set Topology

variable {f g : ℝ → ℝ} {x y : ℝ}

/-- The slope at infinity of `f : ℝ → ℝ`: the limit of `f x / x` at `+∞`, as an `EReal`. It is
defined as a `limsup`, so that it is always defined. For a function convex on `(0, ∞)` the limit
exists (`ConvexOn.tendsto_derivAtTop`), and it is also the limit of the right derivative of `f`
(`ConvexOn.tendsto_rightDeriv_derivAtTop`). -/
noncomputable
def derivAtTop (f : ℝ → ℝ) : EReal := limsup (fun x ↦ ((f x / x : ℝ) : EReal)) atTop

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : derivAtTop f = derivAtTop g :=
  limsup_congr (h.mono fun x hx ↦ by rw [hx])

lemma derivAtTop_of_tendsto {y : EReal}
    (h : Tendsto (fun x ↦ ((f x / x : ℝ) : EReal)) atTop (𝓝 y)) :
    derivAtTop f = y :=
  h.limsup_eq

@[simp]
lemma derivAtTop_const (c : ℝ) : derivAtTop (fun _ ↦ c) = 0 := by
  refine derivAtTop_of_tendsto ?_
  rw [← EReal.coe_zero]
  exact (continuous_coe_real_ereal.tendsto 0).comp (tendsto_const_nhds.div_atTop tendsto_id)

@[simp]
lemma derivAtTop_zero : derivAtTop 0 = 0 := derivAtTop_const 0

/-- The slope at infinity of the affine function `x ↦ a * x + b` is `a`. -/
@[simp]
lemma derivAtTop_mul_add (a b : ℝ) : derivAtTop (fun x ↦ a * x + b) = a := by
  refine derivAtTop_of_tendsto (EReal.tendsto_coe.mpr ?_)
  have h : Tendsto (fun x : ℝ ↦ a + b / x) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with x hx
  rw [add_div, mul_div_cancel_right₀ _ hx]

namespace ConvexOn

variable {a : ℝ}

/-- For a function convex on `(a, ∞)`, `f x / x` and the right derivative of `f` tend to the same
limit at infinity. -/
private lemma exists_tendsto_div_and_rightDeriv (hf : ConvexOn ℝ (Ioi a) f) :
    ∃ D : EReal, Tendsto (fun x ↦ ((f x / x : ℝ) : EReal)) atTop (𝓝 D)
      ∧ Tendsto (fun x ↦ ((derivWithin f (Ioi x) x : ℝ) : EReal)) atTop (𝓝 D) := by
  have h_mem {x : ℝ} (hx : a < x) : x ∈ interior (Ioi a) := by simpa using hx
  have h_mono : MonotoneOn (fun x ↦ ((derivWithin f (Ioi x) x : ℝ) : EReal)) (Ioi a) :=
    EReal.coe_strictMono.monotone.comp_monotoneOn (by simpa using hf.monotoneOn_rightDeriv)
  -- a base point `b > max a 0`
  set b := max a 0 + 1 with hb_def
  have hab : a < b := by rw [hb_def]; linarith [le_max_left a 0]
  have hb0 : 0 < b := by rw [hb_def]; linarith [le_max_right a 0]
  obtain ⟨D, hD⟩ := (h_mono.mono (Ici_subset_Ioi.mpr hab)).exists_tendsto_atTop
  have h_le {x : ℝ} (hx : a < x) : ((derivWithin f (Ioi x) x : ℝ) : EReal) ≤ D :=
    ge_of_tendsto hD ((eventually_ge_atTop x).mono fun y hy ↦ h_mono hx (hx.trans_le hy) hy)
  refine ⟨D, tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩, hD⟩
  · -- lower bound, from the tangent line at a point `x₀` where the right derivative exceeds `c`
    obtain ⟨x₀, hx₀, hcx₀⟩ := ((eventually_gt_atTop b).and ((tendsto_order.1 hD).1 c hc)).exists
    set d := derivWithin f (Ioi x₀) x₀
    have h_lim : Tendsto (fun y ↦ (((f x₀ - d * x₀) / y + d : ℝ) : EReal)) atTop (𝓝 d) :=
      (continuous_coe_real_ereal.tendsto d).comp (by
        simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const d)
    filter_upwards [(tendsto_order.1 h_lim).1 c hcx₀, eventually_gt_atTop x₀] with y hy hyx₀
    refine hy.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    have hy0 : 0 < y := hb0.trans (hx₀.trans hyx₀)
    have h_tangent := hf.add_rightDeriv_mul_le (mem_Ioi.mpr ((hab.trans hx₀).trans hyx₀))
      (h_mem (hab.trans hx₀))
    rw [div_add' _ _ _ hy0.ne', div_le_div_iff_of_pos_right hy0]
    linarith
  · -- upper bound: for `y > b`, `f y ≤ f b + D * (y - b)` since the slope from `b` is at most `D`
    have hD_bot : D ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h_le hab)
    lift D to ℝ using ⟨hc.ne_top, hD_bot⟩
    have h_lim : Tendsto (fun y ↦ (((f b - D * b) / y + D : ℝ) : EReal)) atTop (𝓝 D) :=
      (continuous_coe_real_ereal.tendsto D).comp (by
        simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const D)
    filter_upwards [(tendsto_order.1 h_lim).2 c hc, eventually_gt_atTop b] with y hy hyb
    refine lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr ?_) hy
    have hy0 : 0 < y := hb0.trans hyb
    have hay : a < y := hab.trans hyb
    have h_slope : slope f b y ≤ D := by
      refine (hf.slope_le_leftDeriv_of_mem_interior (mem_Ioi.mpr hab) (h_mem hay) hyb).trans ?_
      refine (hf.leftDeriv_le_rightDeriv_of_mem_interior (h_mem hay)).trans ?_
      exact EReal.coe_le_coe_iff.mp (h_le hay)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyb)] at h_slope
    rw [div_add' _ _ _ hy0.ne', div_le_div_iff_of_pos_right hy0]
    linarith

/-- For a function convex on `(a, ∞)`, `f x / x` tends to `derivAtTop f`. -/
lemma tendsto_derivAtTop (hf : ConvexOn ℝ (Ioi a) f) :
    Tendsto (fun x ↦ ((f x / x : ℝ) : EReal)) atTop (𝓝 (derivAtTop f)) := by
  obtain ⟨D, hD, -⟩ := hf.exists_tendsto_div_and_rightDeriv
  rwa [derivAtTop_of_tendsto hD]

/-- For a function convex on `(a, ∞)`, the right derivative tends to `derivAtTop f`. -/
lemma tendsto_rightDeriv_derivAtTop (hf : ConvexOn ℝ (Ioi a) f) :
    Tendsto (fun x ↦ ((derivWithin f (Ioi x) x : ℝ) : EReal)) atTop (𝓝 (derivAtTop f)) := by
  obtain ⟨D, hD, hD'⟩ := hf.exists_tendsto_div_and_rightDeriv
  rwa [derivAtTop_of_tendsto hD]

lemma rightDeriv_le_derivAtTop (hf : ConvexOn ℝ (Ioi a) f) (hx : a < x) :
    ((derivWithin f (Ioi x) x : ℝ) : EReal) ≤ derivAtTop f := by
  have h_mono : MonotoneOn (fun x ↦ derivWithin f (Ioi x) x) (Ioi a) := by
    simpa using hf.monotoneOn_rightDeriv
  exact ge_of_tendsto hf.tendsto_rightDeriv_derivAtTop ((eventually_ge_atTop x).mono fun y hy ↦
    EReal.coe_le_coe_iff.mpr (h_mono hx (hx.trans_le hy) hy))

lemma derivAtTop_ne_bot (hf : ConvexOn ℝ (Ioi a) f) : derivAtTop f ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hf.rightDeriv_le_derivAtTop (lt_add_one a))

lemma derivAtTop_eq_of_tendsto_rightDeriv (hf : ConvexOn ℝ (Ioi a) f) {y : ℝ}
    (h : Tendsto (fun x ↦ derivWithin f (Ioi x) x) atTop (𝓝 y)) :
    derivAtTop f = y :=
  tendsto_nhds_unique hf.tendsto_rightDeriv_derivAtTop
    ((continuous_coe_real_ereal.tendsto y).comp h)

lemma derivAtTop_eq_top_of_tendsto_rightDeriv (hf : ConvexOn ℝ (Ioi a) f)
    (h : Tendsto (fun x ↦ derivWithin f (Ioi x) x) atTop atTop) :
    derivAtTop f = ⊤ :=
  tendsto_nhds_unique hf.tendsto_rightDeriv_derivAtTop (EReal.tendsto_coe_atTop.comp h)

/-- A function convex on `[0, ∞)` grows at most linearly, with slope `derivAtTop f`. -/
lemma le_add_derivAtTop (hf : ConvexOn ℝ (Ici 0) f) (h : derivAtTop f ≠ ⊤) (hy : 0 ≤ y)
    (hyx : y ≤ x) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  rcases hyx.eq_or_lt with rfl | hyx
  · simp
  have hf' : ConvexOn ℝ (Ioi 0) f := hf.subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hx : x ∈ interior (Ici (0 : ℝ)) := by simpa using hy.trans_lt hyx
  have h_slope : slope f y x ≤ (derivAtTop f).toReal := by
    refine (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans ?_
    refine (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans ?_
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal h hf'.derivAtTop_ne_bot]
    exact hf'.rightDeriv_le_derivAtTop (hy.trans_lt hyx)
  rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at h_slope
  linarith

end ConvexOn

lemma derivAtTop_add (hf : ConvexOn ℝ (Ioi 0) f) (hg : ConvexOn ℝ (Ioi 0) g) :
    derivAtTop (fun x ↦ f x + g x) = derivAtTop f + derivAtTop g := by
  refine derivAtTop_of_tendsto ?_
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (derivAtTop f, derivAtTop g) :=
    EReal.continuousAt_add (Or.inr hg.derivAtTop_ne_bot) (Or.inl hf.derivAtTop_ne_bot)
  exact (h_cont.tendsto.comp (hf.tendsto_derivAtTop.prodMk_nhds hg.tendsto_derivAtTop)).congr
    fun x ↦ by simp [add_div]
