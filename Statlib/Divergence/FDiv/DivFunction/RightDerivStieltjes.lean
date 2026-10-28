/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.FDiv.DivFunction.DerivAtTop
public import Statlib.ForMathlib.Analysis.Convex.DerivAtTop
public import Statlib.ForMathlib.MeasureTheory.Measure.ERealStieltjes

/-!
# The right derivative of a divergence function as a Stieltjes function

For a divergence function `f`, we define `f.rightDerivStieltjes`, the right derivative of `f` as a
monotone right-continuous function `ℝ → EReal` (an `ERealStieltjes` function). It is `⊥` below
`f.xmin`, `⊤` from `f.xmax` on, and it agrees with the right derivative of `f.realFun` in the
interior of the effective domain of `f`.

## Main definitions

* `DivFunction.rightDerivStieltjes f`: the right derivative of `f`, as an `ERealStieltjes`
  function.

## Main statements

* `rightDerivStieltjes_of_mem_interior`: in the interior of the effective domain,
  `f.rightDerivStieltjes x = derivWithin f.realFun (Ioi x) x`.
* `rightDerivStieltjes_eq_top_iff`: `f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x`.
* `rightDerivStieltjes_xmin_eq_bot_iff`: `f.rightDerivStieltjes` is `⊥` at `f.xmin` iff the right
  derivative of `f.realFun` tends to `-∞` there.
* `rightDerivStieltjes_add`, `rightDerivStieltjes_smul`: compatibility with the module structure.
* `tendsto_rightDerivStieltjes_atTop`: `f.rightDerivStieltjes` tends to `f.derivAtTop` at `+∞`.
  Since `f.derivAtTop` is defined as the limit of `f x / x`, this rests on the corresponding result
  for convex real functions, `ConvexOn.tendsto_rightDeriv_derivAtTop`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {f g : DivFunction}

section RightDeriv

lemma continuousWithinAt_derivWithin_realFun (f : DivFunction) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    ContinuousWithinAt (fun y ↦ derivWithin f.realFun (Ioi y) y) (Ici x) x := by
  refine f.convexOn_Ioo_realFun.continuousWithinAt_rightDeriv_of_mem_interior ?_
  rw [f.isOpen_toReal_Ioo.interior_eq]
  exact mem_toReal_Ioo_iff.mpr ⟨hx, hx'⟩

/-- Auxiliary monotone function: `⊥` up to `f.xmin`, `⊤` from `f.xmax` on, and the right
derivative of `f.realFun` in between. `f.rightDerivStieltjes` is its right-continuous
regularization. -/
noncomputable def rightDerivAux (f : DivFunction) : ℝ → EReal := fun x ↦
  if x ≤ f.xmin.toReal then ⊥
  else if f.xmax ≤ ENNReal.ofReal x then ⊤
  else ((derivWithin f.realFun (Ioi x) x : ℝ) : EReal)

lemma monotone_rightDerivAux (f : DivFunction) : Monotone f.rightDerivAux := by
  intro x y hxy
  by_cases hx1 : x ≤ f.xmin.toReal
  · simp [rightDerivAux, hx1]
  have hy1 : ¬ y ≤ f.xmin.toReal := fun h ↦ hx1 (hxy.trans h)
  by_cases hy2 : f.xmax ≤ ENNReal.ofReal y
  · simp [rightDerivAux, hy1, hy2]
  have hx2 : ¬ f.xmax ≤ ENNReal.ofReal x := fun h ↦ hy2 (h.trans (ENNReal.ofReal_le_ofReal hxy))
  simp only [rightDerivAux, hx1, hy1, hx2, hy2, ↓reduceIte, EReal.coe_le_coe_iff]
  exact f.derivWithin_realFun_mono hxy
    ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mpr (not_le.mp hx1)) (not_le.mp hy2)

/-- The right derivative of `f`, as a monotone right-continuous function `ℝ → EReal`: it is `⊥`
below `f.xmin`, `⊤` from `f.xmax` on, and in between it is the right limit of the right derivative
of `f.realFun` (which is that right derivative itself, except possibly at `f.xmin` where the
right derivative of `f.realFun` can be `-∞`). -/
protected noncomputable def rightDerivStieltjes (f : DivFunction) : ERealStieltjes :=
  f.monotone_rightDerivAux.erealStieltjes

lemma rightDerivStieltjes_apply (f : DivFunction) (x : ℝ) :
    f.rightDerivStieltjes x = Function.rightLim f.rightDerivAux x := rfl

lemma rightDerivStieltjes_of_lt_xmin {x : ℝ} (hx : x < f.xmin.toReal) :
    f.rightDerivStieltjes x = ⊥ := by
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr tendsto_const_nhds)
  filter_upwards [Ioo_mem_nhdsGT hx] with y hy
  simp [rightDerivAux, hy.2.le]

lemma rightDerivStieltjes_of_ge_xmax {x : ℝ} (hx : f.xmax ≤ ENNReal.ofReal x) :
    f.rightDerivStieltjes x = ⊤ := by
  have hx1 : f.xmin.toReal < x := by
    rw [← ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top]
    exact xmin_lt_xmax.trans_le hx
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr tendsto_const_nhds)
  filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
  simp [rightDerivAux, not_le.mpr (hx1.trans hy), hx.trans (ENNReal.ofReal_le_ofReal hy.le)]

lemma rightDerivStieltjes_of_neg {x : ℝ} (hx : x < 0) :
    f.rightDerivStieltjes x = ⊥ :=
  rightDerivStieltjes_of_lt_xmin (hx.trans_le ENNReal.toReal_nonneg)

lemma eventually_mem_toReal_Ioo {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    ∀ᶠ y in 𝓝[>] x, y ∈ ENNReal.toReal '' Ioo f.xmin f.xmax := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
    ((ENNReal.continuous_ofReal.tendsto x).eventually (gt_mem_nhds hx2))] with y (hy : x < y) hy2
  exact mem_toReal_Ioo_iff.mpr
    ⟨(ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mpr (hx1.trans_lt hy), hy2⟩

lemma rightDerivAux_eventuallyEq {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    f.rightDerivAux =ᶠ[𝓝[>] x] fun y ↦ ((derivWithin f.realFun (Ioi y) y : ℝ) : EReal) := by
  filter_upwards [f.eventually_mem_toReal_Ioo hx1 hx2] with y hy
  obtain ⟨hy1, hy2⟩ := mem_toReal_Ioo_iff.mp hy
  simp [rightDerivAux, not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hy1),
    not_le.mpr hy2]

lemma tendsto_derivWithin_realFun_nhdsGT {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    Tendsto (fun y ↦ ((derivWithin f.realFun (Ioi y) y : ℝ) : EReal)) (𝓝[>] x)
      (𝓝 (f.rightDerivStieltjes x)) := by
  rw [rightDerivStieltjes_apply]
  exact (tendsto_congr' (rightDerivAux_eventuallyEq hx1 hx2)).mp
    (f.monotone_rightDerivAux.tendsto_rightLim x)

lemma rightDerivStieltjes_eq_rightLim {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x
      = Function.rightLim (fun y ↦ ((derivWithin f.realFun (Ioi y) y : ℝ) : EReal)) x :=
  (rightLim_eq_of_tendsto (f.tendsto_derivWithin_realFun_nhdsGT hx1 hx2)).symm

lemma rightDerivStieltjes_of_mem_interior {x : ℝ} (hx : f.xmin < ENNReal.ofReal x)
    (hx' : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x = derivWithin f.realFun (Ioi x) x := by
  rw [rightDerivStieltjes_eq_rightLim ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hx).le hx']
  exact (continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
    (f.continuousWithinAt_derivWithin_realFun hx hx')).rightLim_eq

lemma rightDerivStieltjes_ne_top_of_lt_xmax {x : ℝ} (hx : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x ≠ ⊤ := by
  by_cases hx1 : x < f.xmin.toReal
  · simp [rightDerivStieltjes_of_lt_xmin hx1]
  push Not at hx1
  obtain ⟨y, hy, hxy⟩ := ((f.eventually_mem_toReal_Ioo hx1 hx).and self_mem_nhdsWithin).exists
  obtain ⟨hy1, hy2⟩ := mem_toReal_Ioo_iff.mp hy
  rw [rightDerivStieltjes_apply]
  refine ne_top_of_le_ne_top ?_ (f.monotone_rightDerivAux.rightLim_le hxy)
  simp [rightDerivAux, not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hy1),
    not_le.mpr hy2]

lemma rightDerivStieltjes_eq_top_iff {x : ℝ} :
    f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x :=
  ⟨fun h ↦ not_lt.mp fun hx ↦ rightDerivStieltjes_ne_top_of_lt_xmax hx h,
    rightDerivStieltjes_of_ge_xmax⟩

lemma rightDerivStieltjes_ne_bot_of_xmin_lt {x : ℝ} (hx : f.xmin.toReal < x) :
    f.rightDerivStieltjes x ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (f.monotone_rightDerivAux.le_rightLim le_rfl)
  simp only [rightDerivAux, not_le.mpr hx, ↓reduceIte]
  split_ifs <;> simp

/-- `f.rightDerivStieltjes` is `⊥` at `f.xmin` iff the right derivative of `f` tends to `-∞` at
`f.xmin`. -/
lemma rightDerivStieltjes_xmin_eq_bot_iff :
    f.rightDerivStieltjes f.xmin.toReal = ⊥
      ↔ Tendsto (fun y ↦ derivWithin f.realFun (Ioi y) y) (𝓝[>] f.xmin.toReal) atBot := by
  have h := f.tendsto_derivWithin_realFun_nhdsGT le_rfl
    (by rw [ENNReal.ofReal_toReal xmin_ne_top]; exact xmin_lt_xmax)
  rw [← EReal.tendsto_coe_nhds_bot_iff]
  exact ⟨fun h_eq ↦ h_eq ▸ h, fun h_bot ↦ tendsto_nhds_unique h h_bot⟩

@[simp]
lemma rightDerivStieltjes_one : f.rightDerivStieltjes 1 = f.rightDeriv 1 := by
  rw [rightDerivStieltjes_of_mem_interior (by simpa using xmin_lt_one) (by simpa using one_lt_xmax),
    rightDeriv_def, ENNReal.toReal_one]

lemma rightDerivStieltjes_one_nonneg : 0 ≤ f.rightDerivStieltjes 1 := by
  rw [rightDerivStieltjes_one]
  exact EReal.coe_nonneg.mpr f.rightDeriv_one_nonneg

@[simp]
lemma toReal_max_xmin : (max f.xmin g.xmin).toReal = max f.xmin.toReal g.xmin.toReal :=
  ENNReal.toReal_max xmin_ne_top xmin_ne_top

lemma realFun_add_eventuallyEq {x : ℝ} (hxf : x ∈ ENNReal.toReal '' Ioo f.xmin f.xmax)
    (hxg : x ∈ ENNReal.toReal '' Ioo g.xmin g.xmax) :
    (f + g).realFun =ᶠ[𝓝 x] fun y ↦ f.realFun y + g.realFun y := by
  filter_upwards [(f.isOpen_toReal_Ioo.inter g.isOpen_toReal_Ioo).mem_nhds ⟨hxf, hxg⟩]
    with y ⟨hyf, hyg⟩
  simp only [realFun, add_apply]
  rw [ENNReal.toReal_add (lt_top_of_mem_Ioo (mem_toReal_Ioo_iff.mp hyf)).ne
    (lt_top_of_mem_Ioo (mem_toReal_Ioo_iff.mp hyg)).ne]

lemma derivWithin_realFun_add {x : ℝ} (hxf : x ∈ ENNReal.toReal '' Ioo f.xmin f.xmax)
    (hxg : x ∈ ENNReal.toReal '' Ioo g.xmin g.xmax) :
    derivWithin (f + g).realFun (Ioi x) x
      = derivWithin f.realFun (Ioi x) x + derivWithin g.realFun (Ioi x) x := by
  rw [(realFun_add_eventuallyEq hxf hxg).derivWithin_eq_of_nhds]
  exact derivWithin_fun_add (f.differentiableWithinAt_realFun (mem_toReal_Ioo_iff.mp hxf))
    (g.differentiableWithinAt_realFun (mem_toReal_Ioo_iff.mp hxg))

lemma rightDerivStieltjes_add :
    (f + g).rightDerivStieltjes = f.rightDerivStieltjes + g.rightDerivStieltjes := by
  ext x
  by_cases hf_top : f.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_left hf_top, rightDerivStieltjes_eq_top_iff, xmax_add]
    exact min_le_of_left_le (rightDerivStieltjes_eq_top_iff.mp hf_top)
  by_cases hg_top : g.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_right hg_top, rightDerivStieltjes_eq_top_iff, xmax_add]
    exact min_le_of_right_le (rightDerivStieltjes_eq_top_iff.mp hg_top)
  rw [ERealStieltjes.add_apply_of_ne_top hf_top hg_top]
  have hxf_lt : ENNReal.ofReal x < f.xmax :=
    not_le.mp fun h ↦ hf_top (rightDerivStieltjes_of_ge_xmax h)
  have hxg_lt : ENNReal.ofReal x < g.xmax :=
    not_le.mp fun h ↦ hg_top (rightDerivStieltjes_of_ge_xmax h)
  have hx_lt : ENNReal.ofReal x < (f + g).xmax := by
    rw [xmax_add]
    exact lt_min hxf_lt hxg_lt
  by_cases hxf : x < f.xmin.toReal
  · rw [rightDerivStieltjes_of_lt_xmin hxf, EReal.bot_add, rightDerivStieltjes_of_lt_xmin]
    rw [xmin_add, toReal_max_xmin]
    exact hxf.trans_le (le_max_left _ _)
  by_cases hxg : x < g.xmin.toReal
  · rw [rightDerivStieltjes_of_lt_xmin hxg, EReal.add_bot, rightDerivStieltjes_of_lt_xmin]
    rw [xmin_add, toReal_max_xmin]
    exact hxg.trans_le (le_max_right _ _)
  push Not at hxf hxg
  have hxfg : (f + g).xmin.toReal ≤ x := by
    rw [xmin_add, toReal_max_xmin]
    exact max_le hxf hxg
  have h_add : Tendsto
      (fun y ↦ ((derivWithin f.realFun (Ioi y) y : ℝ) : EReal)
        + ((derivWithin g.realFun (Ioi y) y : ℝ) : EReal))
      (𝓝[>] x) (𝓝 (f.rightDerivStieltjes x + g.rightDerivStieltjes x)) :=
    (EReal.continuousAt_add (Or.inl hf_top) (Or.inr hg_top)).tendsto.comp
      ((f.tendsto_derivWithin_realFun_nhdsGT hxf hxf_lt).prodMk_nhds
        (g.tendsto_derivWithin_realFun_nhdsGT hxg hxg_lt))
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr h_add)
  filter_upwards [rightDerivAux_eventuallyEq hxfg hx_lt, f.eventually_mem_toReal_Ioo hxf hxf_lt,
    g.eventually_mem_toReal_Ioo hxg hxg_lt] with y hy hyf hyg
  simp only [hy, derivWithin_realFun_add hyf hyg, EReal.coe_add]

lemma rightDerivStieltjes_eq_bot_iff_of_xmin_eq (hxmin : f.xmin = g.xmin)
    (h : Tendsto (fun y ↦ derivWithin f.realFun (Ioi y) y) (𝓝[>] f.xmin.toReal) atBot
      ↔ Tendsto (fun y ↦ derivWithin g.realFun (Ioi y) y) (𝓝[>] g.xmin.toReal) atBot) (x : ℝ) :
    f.rightDerivStieltjes x = ⊥ ↔ g.rightDerivStieltjes x = ⊥ := by
  rcases lt_trichotomy x f.xmin.toReal with hx | rfl | hx
  · simp [rightDerivStieltjes_of_lt_xmin hx, rightDerivStieltjes_of_lt_xmin (hxmin ▸ hx)]
  · rw [rightDerivStieltjes_xmin_eq_bot_iff, h, ← rightDerivStieltjes_xmin_eq_bot_iff, hxmin]
  · simp [rightDerivStieltjes_ne_bot_of_xmin_lt hx,
      rightDerivStieltjes_ne_bot_of_xmin_lt (hxmin ▸ hx : g.xmin.toReal < x)]

lemma rightDerivAux_smul {c : ℝ≥0} (hc : c ≠ 0) :
    (c • f).rightDerivAux = fun x ↦ ((c : ℝ) : EReal) * f.rightDerivAux x := by
  ext x
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  simp only [rightDerivAux, xmin_smul hc, xmax_smul hc, realFun_smul, derivWithin_const_mul_field]
  split_ifs
  · rw [EReal.coe_mul_bot_of_pos hc']
  · rw [EReal.coe_mul_top_of_pos hc']
  · rw [EReal.coe_mul]

lemma rightDerivStieltjes_smul {c : ℝ≥0} (hc : c ≠ 0) :
    (c • f).rightDerivStieltjes = c • f.rightDerivStieltjes := by
  ext x
  rw [ERealStieltjes.smul_apply, rightDerivStieltjes_apply, rightDerivStieltjes_apply,
    rightDerivAux_smul hc, EReal.coe_nnreal_eq_coe_real]
  exact rightLim_eq_of_tendsto
    (((EReal.continuous_coe_mul _).tendsto _).comp (f.monotone_rightDerivAux.tendsto_rightLim x))

end RightDeriv

section DerivAtTop

/-! ### Limit of `f.rightDerivStieltjes` at `+∞` -/

/-- If the effective domain of `f` is bounded, then `f.derivAtTop = ∞`. -/
lemma derivAtTop_eq_top_of_xmax_ne_top (h : f.xmax ≠ ∞) : f.derivAtTop = ∞ := by
  have : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ENNReal.zero_lt_top⟩
  refine tendsto_nhds_unique f.tendsto_div_nhdsLT_top (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT h.lt_top] with y hy
  rw [eq_top_of_xmax_lt hy.1, ENNReal.top_div_of_ne_top hy.2.ne]

lemma convexOn_Ioi_realFun_of_xmax_eq_top (h : f.xmax = ∞) :
    ConvexOn ℝ (Ioi f.xmin.toReal) f.realFun := by
  have h_cvx := f.convexOn_Ioo_realFun
  rwa [h, ENNReal.toReal_image_Ioo_top xmin_ne_top] at h_cvx

/-- If the effective domain of `f` is unbounded, then `f.derivAtTop` is the slope at infinity of
`f.realFun`. -/
lemma derivAtTop_eq_toENNReal_derivAtTop_realFun (h : f.xmax = ∞) :
    f.derivAtTop = (_root_.derivAtTop f.realFun).toENNReal := by
  have : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ENNReal.zero_lt_top⟩
  refine tendsto_nhds_unique f.tendsto_div_nhdsLT_top ?_
  have h_lim : Tendsto (fun y : ℝ≥0∞ ↦ (((f.realFun y.toReal / y.toReal : ℝ) : EReal)).toENNReal)
      (𝓝[<] ∞) (𝓝 (_root_.derivAtTop f.realFun).toENNReal) :=
    (EReal.continuous_toENNReal.tendsto _).comp
      ((f.convexOn_Ioi_realFun_of_xmax_eq_top h).tendsto_derivAtTop.comp
        ENNReal.tendsto_toReal_atTop)
  refine h_lim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (max_lt xmin_lt_top ENNReal.one_lt_top)] with y hy
  have hy_top : y ≠ ∞ := hy.2.ne
  have hy_pos : 0 < y.toReal :=
    ENNReal.toReal_pos ((zero_lt_one.trans_le (le_max_right _ _)).trans hy.1).ne' hy_top
  have hfy : f y ≠ ∞ := (lt_top_of_mem_Ioo ⟨(le_max_left _ _).trans_lt hy.1, h ▸ hy.2⟩).ne
  rw [EReal.real_coe_toENNReal, realFun_toReal f hy_top, ENNReal.ofReal_div_of_pos hy_pos,
    ENNReal.ofReal_toReal hfy, ENNReal.ofReal_toReal hy_top]

lemma tendsto_rightDerivStieltjes_atTop :
    Tendsto f.rightDerivStieltjes atTop (𝓝 f.derivAtTop) := by
  rcases eq_or_ne f.xmax ∞ with h | h
  · -- `f.realFun` is convex on `(f.xmin, ∞)`: its right derivative tends to `f.derivAtTop`
    have h_cvx := f.convexOn_Ioi_realFun_of_xmax_eq_top h
    have h_nonneg : 0 ≤ _root_.derivAtTop f.realFun :=
      ge_of_tendsto h_cvx.tendsto_derivAtTop ((eventually_gt_atTop 0).mono fun x hx ↦
        EReal.coe_nonneg.mpr (div_nonneg (f.realFun_nonneg x) hx.le))
    rw [derivAtTop_eq_toENNReal_derivAtTop_realFun h, EReal.coe_toENNReal h_nonneg]
    refine h_cvx.tendsto_rightDeriv_derivAtTop.congr' ?_
    filter_upwards [eventually_gt_atTop f.xmin.toReal] with x hx
    rw [rightDerivStieltjes_of_mem_interior ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mpr hx)
      (h ▸ ENNReal.ofReal_lt_top)]
  · -- `f.rightDerivStieltjes` is eventually `⊤`, and `f.derivAtTop = ∞`
    rw [derivAtTop_eq_top_of_xmax_ne_top h, EReal.coe_ennreal_top]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop f.xmax.toReal] with x hx
    refine (rightDerivStieltjes_of_ge_xmax ?_).symm
    rw [← ENNReal.ofReal_toReal h]
    exact ENNReal.ofReal_le_ofReal hx

lemma rightDerivStieltjes_le_derivAtTop (x : ℝ) : f.rightDerivStieltjes x ≤ f.derivAtTop :=
  f.rightDerivStieltjes.mono.ge_of_tendsto tendsto_rightDerivStieltjes_atTop x

lemma derivWithin_realFun_le_toReal_derivAtTop (h : f.derivAtTop ≠ ∞) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    derivWithin f.realFun (Ioi x) x ≤ f.derivAtTop.toReal := by
  have h1 := f.rightDerivStieltjes_le_derivAtTop x
  rwa [rightDerivStieltjes_of_mem_interior hx hx', ← EReal.coe_ennreal_toReal h,
    EReal.coe_le_coe_iff] at h1

end DerivAtTop

end DivFunction

end ProbabilityTheory
