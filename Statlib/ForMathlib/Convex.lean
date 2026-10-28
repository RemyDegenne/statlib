/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Statlib.ForMathlib.EReal

/-! # Convexity lemmas
-/

@[expose] public section

open Set ENNReal NNReal

lemma ConcaveOn.le_add_deriv_mul {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hfd : DifferentiableAt ℝ f y) :
    f x ≤ f y + deriv f y * (x - y) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h_ccv := hfc.deriv_le_slope hx hy hxy hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
    have : 0 < (y - x) := sub_pos.mpr hxy
    field_simp at h_ccv
    linarith
  · simp
  · have h_ccv := hfc.slope_le_deriv hy hx hyx hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
    have : 0 < (x - y) := sub_pos.mpr hyx
    field_simp at h_ccv
    linarith

lemma ConvexOn.add_deriv_mul_le {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hfd : DifferentiableAt ℝ f y) :
    f y + deriv f y * (x - y) ≤ f x := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h_cvx := hfc.slope_le_deriv hx hy hxy hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_cvx
    have : 0 < (y - x) := sub_pos.mpr hxy
    field_simp at h_cvx
    linarith
  · simp
  · have h_cvx := hfc.deriv_le_slope hy hx hyx hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_cvx
    have : 0 < (x - y) := sub_pos.mpr hyx
    field_simp at h_cvx
    linarith

/-- If `f` is convex on `(0, ∞)` with `f 1 = 0`, then `max f 0` is nonincreasing on `(0, 1]`. -/
lemma ConvexOn.antitoneOn_ofReal_comp {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    AntitoneOn (fun x ↦ ENNReal.ofReal (f x)) (Ioc 0 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hy.2 with rfl | hy1
  · simp [hf_one]
  by_cases hfy : f y ≤ 0
  · simp [ENNReal.ofReal_of_nonpos hfy]
  refine ENNReal.ofReal_le_ofReal ?_
  refine hf.le_left_of_right_le'' hx.1 (mem_Ioi.mpr one_pos) hxy hy1 ?_
  rw [hf_one]
  exact (not_le.mp hfy).le

/-- If `f` is convex on `(0, ∞)` with `f 1 = 0`, then `max f 0` is nondecreasing on `[1, ∞)`. -/
lemma ConvexOn.monotoneOn_ofReal_comp {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    MonotoneOn (fun x ↦ ENNReal.ofReal (f x)) (Ici 1) := by
  intro x hx y _ hxy
  rcases eq_or_lt_of_le (mem_Ici.mp hx) with rfl | hx1
  · simp [hf_one]
  by_cases hfx : f x ≤ 0
  · simp [ENNReal.ofReal_of_nonpos hfx]
  refine ENNReal.ofReal_le_ofReal ?_
  refine hf.le_right_of_left_le'' (mem_Ioi.mpr one_pos)
    (mem_Ioi.mpr (zero_lt_one.trans (hx1.trans_le hxy))) hx1 hxy ?_
  rw [hf_one]
  exact (not_le.mp hfx).le

/-- A convex function lies above its tangent line with slope the right derivative, at any interior
point of its domain. -/
lemma ConvexOn.add_rightDeriv_mul_le {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ interior S) :
    f y + derivWithin f (Ioi y) y * (x - y) ≤ f x := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := (hfc.slope_le_leftDeriv_of_mem_interior hx hy hxy).trans
      (hfc.leftDeriv_le_rightDeriv_of_mem_interior hy)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h := hfc.rightDeriv_le_slope_of_mem_interior hy hx hyx
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hyx)] at h
    linarith

/-- The right derivative of a convex function is right-continuous at the interior points of its
domain. This is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds). -/
lemma ConvexOn.continuousWithinAt_rightDeriv_of_mem_interior {S : Set ℝ} {f : ℝ → ℝ} {w : ℝ}
    (hfc : ConvexOn ℝ S f) (hw : w ∈ interior S) :
    ContinuousWithinAt (fun x ↦ derivWithin f (Ioi x) x) (Ici w) w := by
  set r := fun x ↦ derivWithin f (Ioi x) x with hr
  have h_mono : MonotoneOn r (interior S) := hfc.monotoneOn_rightDeriv
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  obtain ⟨a, b, hwab, habs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hw)
  have h_int : Ioo a b ⊆ interior S := isOpen_Ioo.subset_interior_iff.mpr habs
  have h_mem : ∀ z ∈ Ioo w b, z ∈ interior S := fun z hz ↦ h_int ⟨hwab.1.trans hz.1, hz.2⟩
  have h_bdd : BddBelow (r '' Ioo w b) := by
    refine ⟨r w, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h_mono hw (h_mem z hz) hz.1.le
  -- `r` is monotone, so it tends to the infimum of its values on `(w, b)`, which is `r w`
  have h_lim := (h_mono.mono h_mem).tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hwab.2) h_bdd
  convert h_lim
  refine le_antisymm (le_csInf ((nonempty_Ioo.mpr hwab.2).image _) ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact h_mono hw (h_mem z hz) hz.1.le
  · -- the infimum is below every slope `slope f w y`, hence below `r w`
    rw [hr]
    beta_reduce
    rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hw]
    refine le_csInf ?_ ?_
    · obtain ⟨z, hwz, hzb⟩ := exists_between hwab.2
      exact ⟨_, z, ⟨habs ⟨hwab.1.trans hwz, hzb⟩, hwz⟩, rfl⟩
    rintro _ ⟨y, ⟨hys, hwy⟩, rfl⟩
    have h_cont : ContinuousWithinAt f (Ioi w) w :=
      (hfc.differentiableWithinAt_Ioi_of_mem_interior hw).continuousWithinAt
    have slope_lim : Filter.Tendsto (slope f y) (nhdsWithin w (Ioi w)) (nhds (slope f y w)) :=
      ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 hwy.ne)).smul
        (h_cont.sub continuousWithinAt_const) |>.tendsto
    rw [slope_comm] at slope_lim
    refine le_of_tendsto_of_tendsto tendsto_const_nhds slope_lim ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hwy hwab.2)] with z hz
    have hz' : z ∈ Ioo w b := ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
    calc sInf (r '' Ioo w b) ≤ r z := csInf_le h_bdd ⟨z, hz', rfl⟩
    _ ≤ slope f z y := hfc.rightDeriv_le_slope_of_mem_interior (h_mem z hz') hys
        (hz.2.trans_le (min_le_left _ _))
    _ = slope f y z := slope_comm _ _ _

/-- A convex subset of `ℝ` with empty interior has at most one point. -/
lemma Convex.subsingleton_of_interior_eq_empty {S : Set ℝ} (hS : Convex ℝ S)
    (h : interior S = ∅) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra h_ne
  wlog h_lt : x < y generalizing x y
  · exact this hy hx (Ne.symm h_ne) ((not_lt.mp h_lt).lt_of_ne (Ne.symm h_ne))
  have h_sub : Ioo x y ⊆ interior S := by
    rw [← interior_Icc]
    exact interior_mono (hS.ordConnected.out hx hy)
  rw [h, subset_empty_iff, Ioo_eq_empty_iff] at h_sub
  exact h_sub h_lt

/-- A convex function on a subset of `ℝ` is bounded below on it by an affine function. -/
lemma ConvexOn.exists_affine_le {S : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ S f) :
    ∃ c c', ∀ x ∈ S, c * x + c' ≤ f x := by
  rcases (interior S).eq_empty_or_nonempty with h | ⟨y, hy⟩
  · rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp
    refine ⟨0, f y, fun x hx ↦ ?_⟩
    simp [hf.1.subsingleton_of_interior_eq_empty h hx hy]
  · refine ⟨derivWithin f (Ioi y) y, f y - derivWithin f (Ioi y) y * y, fun x hx ↦ ?_⟩
    calc derivWithin f (Ioi y) y * x + (f y - derivWithin f (Ioi y) y * y)
    _ = f y + derivWithin f (Ioi y) y * (x - y) := by ring
    _ ≤ f x := hf.add_rightDeriv_mul_le hx hy

lemma StrictConvexOn.add_deriv_mul_lt {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hfd : DifferentiableAt ℝ f y) :
    f y + deriv f y * (x - y) < f x := by
  rcases lt_trichotomy x y with hxy' | rfl | hyx
  · have h_sccv := hfc.slope_lt_deriv hx hy hxy' hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_sccv
    have : 0 < (y - x) := sub_pos.mpr hxy'
    field_simp at h_sccv
    linarith
  · exfalso
    exact hxy rfl
  · have h_sccv := hfc.deriv_lt_slope hy hx hyx hfd
    simp only [slope, vsub_eq_sub, smul_eq_mul] at h_sccv
    have : 0 < (x - y) := sub_pos.mpr hyx
    field_simp at h_sccv
    linarith

lemma strictConvexOn_inv_Ioi : StrictConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ioi (0 : ℝ))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  have A : (y⁻¹ - x⁻¹) / (y - x) = -1 / (x * y) := by field [ne_of_gt hx, ne_of_gt hy]
  have B : (z⁻¹ - y⁻¹) / (z - y) = -1 / (y * z) := by field [ne_of_gt hy, ne_of_gt hz]
  rw [A, B]
  field_simp
  linarith

lemma strictConvexOn_inv : StrictConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b a₀ b₀ hab
  simp only [smul_eq_mul]
  have aₜ : a ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have bₜ : b ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  by_cases h : x ≠ 0 ∧ x ≠ ⊤ ∧ y ≠ 0 ∧ y ≠ ⊤
  · obtain ⟨x₀, xₜ, y₀, yₜ⟩ := h
    suffices (a * x + b * y)⁻¹.toReal < (a * x⁻¹ + b * y⁻¹).toReal by
      refine (toNNReal_lt_toNNReal ?_ ?_).mp this
      · refine inv_ne_top.mpr ?_
        suffices 0 < a * x + b * y from this.ne'
        exact Right.add_pos' (mul_pos a₀.ne' x₀) (mul_pos b₀.ne' y₀)
      · refine add_ne_top.mpr ⟨?_, ?_⟩
        · exact mul_ne_top aₜ <| inv_ne_top.mpr x₀
        · exact mul_ne_top bₜ <| inv_ne_top.mpr y₀
    rw [toReal_inv, toReal_add, toReal_add, toReal_mul, toReal_mul,
      toReal_mul, toReal_mul, toReal_inv, toReal_inv]
    · obtain ⟨_, strc_conv⟩ := strictConvexOn_inv_Ioi
      refine strc_conv (toReal_pos x₀ xₜ) (toReal_pos y₀ yₜ) ?_
        (toReal_pos a₀.ne' aₜ) (toReal_pos b₀.ne.symm bₜ) ?_
      · by_contra h
        have : x = y := (toReal_eq_toReal_iff' xₜ yₜ).mp h
        contradiction
      · rw [← toReal_add aₜ bₜ]
        exact (toReal_eq_one_iff (a + b)).mpr hab
    · exact mul_ne_top aₜ <| inv_ne_top.mpr x₀
    · exact mul_ne_top bₜ <| inv_ne_top.mpr y₀
    · exact mul_ne_top aₜ <| xₜ
    · exact mul_ne_top bₜ <| yₜ
  · simp only [not_and_or] at h
    rcases h with x₀ | xₜ | y₀ | yₜ
    · push Not at x₀
      simp only [x₀, mul_zero, zero_add, ENNReal.inv_zero, ENNReal.mul_top a₀.ne', top_add,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨b₀, pos_of_ne_zero ?_⟩
      rw [← x₀]
      exact hxy.symm
    · push Not at xₜ
      simp only [xₜ, ENNReal.mul_top a₀.ne', top_add, inv_top, mul_zero, zero_add,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨b₀, ?_⟩
      rw [xₜ] at hxy
      exact hxy.symm
    · push Not at y₀
      simp only [y₀, mul_zero, add_zero, ENNReal.inv_zero, ENNReal.mul_top b₀.ne', add_top,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨a₀, pos_of_ne_zero ?_⟩
      rw [y₀] at hxy
      exact hxy
    · push Not at yₜ
      simp only [yₜ, ENNReal.mul_top b₀.ne', add_top, inv_top, mul_zero, add_zero,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨a₀, ?_⟩
      rw [yₜ] at hxy
      exact hxy

lemma convexOn_inv_Ioi : ConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := strictConvexOn_inv_Ioi.convexOn

lemma convexOn_inv : ConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := strictConvexOn_inv.convexOn

lemma ConcaveOn_log' : ConcaveOn ℝ≥0∞ univ log := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b a₀ b₀ hab
  simp only [smul_eq_mul]
  have aₜ : a ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have bₜ : b ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have smul_log : ∀ (x y : ℝ≥0∞), x • y.log = x * y.log := fun _ _ ↦ rfl
  simp only [smul_log]
  by_cases h : x ≠ 0 ∧ x ≠ ⊤ ∧ y ≠ 0 ∧ y ≠ ⊤
  · obtain ⟨x₀, xₜ, y₀, yₜ⟩ := h
    suffices (a * x.log + b * y.log).toReal ≤ ((a * x + b * y).log).toReal by
      refine EReal.le_of_toReal_le ?_ ?_ ?_ ?_ this
      · simp only [ne_eq, log_eq_top_iff, add_eq_top, not_or]
        exact ⟨mul_ne_top aₜ xₜ, mul_ne_top bₜ yₜ⟩
      · refine EReal.add_ne_top ?_ ?_
        all_goals
          rw [EReal.mul_ne_top]
          simp_all
      · aesop
      · rw [EReal.add_ne_bot_iff, EReal.mul_ne_bot]
        refine ⟨?_, ?_⟩
        · simp_all
        · simp_all [EReal.mul_ne_bot]
    rw [EReal.toReal_add, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_log, EReal.toReal_log,
      EReal.toReal_log, toReal_add, toReal_mul, toReal_mul]
    · simp only [EReal.toReal_coe_ennreal]
      obtain ⟨_, conv⟩ := strictConcaveOn_log_Ioi.concaveOn
      simp only [smul_eq_mul] at conv
      refine conv (toReal_pos x₀ xₜ) (toReal_pos y₀ yₜ) toReal_nonneg toReal_nonneg ?_
      rw [← toReal_add aₜ bₜ]
      exact (toReal_eq_one_iff (a + b)).mpr hab
    · exact mul_ne_top aₜ xₜ
    · exact mul_ne_top bₜ yₜ
    · aesop
    · refine add_ne_top.mpr ⟨?_, ?_⟩
      · exact mul_ne_top aₜ xₜ
      · exact mul_ne_top bₜ yₜ
    · exact y₀
    · exact yₜ
    · exact x₀
    · exact xₜ
    · refine (EReal.mul_ne_top _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_bot _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_top _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_bot _ _).mpr ?_
      aesop
  · simp only [not_and_or] at h
    rcases h with x₀ | xₜ | y₀ | yₜ
    · push Not at x₀
      by_cases a_eq₀ : a = 0
      · simp_all
      · push Not at a_eq₀
        replace a₀ : 0 < a := pos_of_ne_zero a_eq₀
        rw [x₀, log_zero, EReal.mul_bot_of_pos <| EReal.coe_ennreal_pos.mpr a₀]
        simp
    · push Not at xₜ
      by_cases a_eq₀ : a = 0
      · simp_all
      · push Not at a_eq₀
        replace a₀ : 0 < a := pos_of_ne_zero a_eq₀
        rw [xₜ, log_top, EReal.mul_top_of_pos <| EReal.coe_ennreal_pos.mpr a₀]
        rw [ENNReal.mul_top a₀.ne']
        simp
    · push Not at y₀
      by_cases b_eq₀ : b = 0
      · simp_all
      · push Not at b_eq₀
        replace b₀ : 0 < b := pos_of_ne_zero b_eq₀
        rw [y₀, log_zero, EReal.mul_bot_of_pos <| EReal.coe_ennreal_pos.mpr b₀]
        simp
    · push Not at yₜ
      by_cases b_eq₀ : b = 0
      · simp_all
      · push Not at b_eq₀
        replace b₀ : 0 < b := pos_of_ne_zero b_eq₀
        rw [yₜ, log_top, EReal.mul_top_of_pos <| EReal.coe_ennreal_pos.mpr b₀]
        rw [ENNReal.mul_top b₀.ne']
        simp

lemma ConcaveOn_log : ConcaveOn ℝ≥0 univ log := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b a₀ b₀ hab
  obtain ⟨_, conv⟩ := ConcaveOn_log'
  exact conv hx hy zero_le zero_le <| (toNNReal_eq_one_iff _).mp hab
