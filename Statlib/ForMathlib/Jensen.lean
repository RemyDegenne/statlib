/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Probability.ConditionalProbability
public import Statlib.ForMathlib.Convex
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-! # Convexity results
-/

@[expose] public section

open Function Set ENNReal

open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ≥0∞} {t : Set α}
  {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞}

/-- The derivative of the function `Inv.inv` on `EReal`. -/
protected noncomputable
def Inv.deriv (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊤
  else if x = ∞ then 0
  else ((deriv Inv.inv x.toReal : ℝ) : EReal)

@[simp]
lemma deriv_inv_ne_bot (x : ℝ≥0∞) : Inv.deriv x ≠ ⊥ := by
  unfold Inv.deriv
  split_ifs <;> simp

lemma deriv_inv_ne_top {x : ℝ≥0∞} (hx : x ≠ 0) : Inv.deriv x ≠ ⊤ := by
  unfold Inv.deriv
  simp only [hx, ↓reduceIte, deriv_inv', EReal.coe_neg, ne_eq]
  split_ifs <;> simp

lemma Inv.le_add_deriv_mul {x y : ℝ≥0∞} (hx_top : x ≠ ⊤) (hy_zero : y ≠ 0) :
    y⁻¹ + Inv.deriv y * (x - y) ≤ x⁻¹ := by
  by_cases hy_top : y = ⊤
  · simp only [hy_top, inv_top, EReal.coe_ennreal_zero, Inv.deriv, top_ne_zero, ↓reduceIte,
    EReal.coe_ennreal_top, EReal.sub_top, zero_mul, add_zero]
    positivity
  · push Not at hy_top
    by_cases hx_zero: x = 0
    · simp [hx_zero]
    have h_cvx := convexOn_inv_Ioi.add_deriv_mul_le (x := x.toReal) (y := y.toReal) ?_ ?_ ?_
    rotate_left
    · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx_zero, Ne.lt_top hx_top⟩
    · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    · exact differentiableAt_inv <| toReal_ne_zero.mpr ⟨hy_zero, hy_top⟩
    simp only [← toReal_inv] at h_cvx
    simp only [Inv.deriv, hy_zero, ↓reduceIte, hy_top]
    rw [← EReal.coe_ennreal_toReal hx_top, ← EReal.coe_ennreal_toReal hy_top,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hx_zero,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hy_zero]
    norm_cast

theorem Inv.map_lintegral_le [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) : (∫⁻ x, f x ∂μ)⁻¹ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
  by_cases h0 : ∫⁻ x, f x ∂μ = 0
  · simp only [h0, ENNReal.inv_zero]
    rw [lintegral_eq_zero_iff' hf] at h0
    have : ∀ᵐ x ∂μ, (f x)⁻¹ = ⊤ := by
      filter_upwards [h0] with x hx
      rw [hx]
      simp
    rw [lintegral_congr_ae this]
    simp
  by_cases h_int_top : ∫⁻ x, f x ∂μ = ∞
  · simp [h_int_top]
  by_cases htop_inv : ∫⁻ x, (f x)⁻¹ ∂μ = ∞
  · simp [htop_inv]
  let y := ∫⁻ x, f x ∂μ
  have h_eint : EIntegrable (fun x ↦ (f x : EReal) - y) μ := by
    refine EIntegrable.sub_const ?_ (by simp [y]) (by simp [y, h_int_top])
    exact eintegrable_of_nonneg (fun _ ↦ by positivity)
  calc
  _ = (∫ᵉ x, f x ∂μ).toENNReal⁻¹ := by
    rw [lintegral_eq_eintegral _]
  _ = (∫ᵉ x, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
    rw [eintegral_add]
    · have : ∫ᵉ x, Inv.deriv y * ((f x) - y) ∂μ = 0 := by
        rw [eintegral_const_mul (by simp) (deriv_inv_ne_top h0) h_eint, eintegral_sub]
        rotate_left
        · exact eintegrable_of_nonneg (fun x ↦ by positivity)
        · fun_prop
        · exact eintegrable_const
        · fun_prop
        · simp [eintegral_eq_lintegral, h_int_top]
        · simp
        simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one, mul_eq_zero, y]
        right
        rw [eintegral_eq_lintegral, EReal.sub_self (by simp [h_int_top]) (by simp)]
      rw [this]
      simp [eintegral_const, ← lintegral_eq_eintegral, y]
    · fun_prop
    · fun_prop
    · exact eintegrable_const
    · exact h_eint.const_mul (by simp) (deriv_inv_ne_top h0)
    · simp
    · simp [y, h0]
  _ ≤ (∫ᵉ x, (Inv.inv (α := ℝ≥0∞) (f x)) ∂μ).toENNReal := by
    refine EReal.toENNReal_le_toENNReal ?_
    refine eintegral_mono_ae ?_
    filter_upwards [hf_top] with x hx
    exact Inv.le_add_deriv_mul hx h0
  _ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
    rw [← lintegral_eq_eintegral _]

lemma AEMeasurable.cond {μ : Measure α} (hf : AEMeasurable f (μ.restrict t)) :
    AEMeasurable f μ[|t] := by
  simp [ProbabilityTheory.cond, hf.smul_measure (μ t)⁻¹]

theorem Inv.map_set_lintegral_le (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤) (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    μ t * (∫⁻ x in t, f x ∂μ)⁻¹ ≤ (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  have : IsProbabilityMeasure μ[|t] := cond_isProbabilityMeasure_of_finite hμ_t₀ hμ_t₁
  replace hf : AEMeasurable f μ[|t] := hf.cond
  replace ht_top : ∀ᵐ x ∂μ[|t], f x ≠ ⊤ := by
    unfold ProbabilityTheory.cond
    rw [← μ.restrict_smul, ae_restrict_iff' ht]
    change ((μ t)⁻¹ • μ) {x | x ∈ t → f x ≠ ⊤}ᶜ = 0
    rw [Measure.smul_apply]
    exact smul_eq_zero_of_right (μ t)⁻¹ ht_top
  calc
  _ = (∫⁻ x, f x ∂μ[|t])⁻¹ := by
    simp only [lintegral_smul_measure, smul_eq_mul, ProbabilityTheory.cond]
    rw [ENNReal.mul_inv, inv_inv]
    · left
      simp [hμ_t₁]
    · left
      simp [hμ_t₀]
  _ ≤ ∫⁻ x, (f x)⁻¹ ∂μ[|t] := Inv.map_lintegral_le hf ht_top
  _ = (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
    simp [ProbabilityTheory.cond]

lemma Inv.lt_add_deriv_mul {x y : ℝ≥0∞} (hx_top : x ≠ ⊤) (hy_zero : y ≠ 0) (hxy : x ≠ y) :
    y⁻¹ + Inv.deriv y * (x - y) < x⁻¹ := by
  by_cases hy_top : y = ⊤
  · simp [hy_top, Inv.deriv, hx_top]
  · push Not at hy_top
    by_cases hx_zero: x = 0
    · simp_all only [ne_eq, zero_ne_top, not_false_eq_true, Inv.deriv, ↓reduceIte, deriv_inv',
      EReal.coe_neg, EReal.coe_ennreal_zero, zero_sub, mul_neg, neg_mul, neg_neg, ENNReal.inv_zero,
      EReal.coe_ennreal_top]
      refine EReal.add_lt_top ?_ ?_
      · simp [hy_zero]
      · refine (EReal.mul_ne_top ↑(y.toReal ^ 2)⁻¹ ↑y).mpr ⟨?_, ?_, ?_, ?_⟩ <;> simp [hy_top]
    have h_cvx := strictConvexOn_inv_Ioi.add_deriv_mul_lt (x := x.toReal) (y := y.toReal)
      ?_ ?_ ?_ ?_
    rotate_left
    · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx_zero, Ne.lt_top hx_top⟩
    · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    · by_contra! h
      exact hxy <| (toReal_eq_toReal_iff' hx_top hy_top).mp h
    · exact differentiableAt_inv <| toReal_ne_zero.mpr ⟨hy_zero, hy_top⟩
    simp only [← toReal_inv] at h_cvx
    simp only [Inv.deriv, hy_zero, ↓reduceIte, hy_top]
    rw [← EReal.coe_ennreal_toReal hx_top, ← EReal.coe_ennreal_toReal hy_top,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hx_zero,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hy_zero]
    norm_cast

set_option backward.isDefEq.respectTransparency false in
theorem Inv.ae_eq_const_or_map_lintegral_lt' [IsProbabilityMeasure μ] (hf : Measurable f)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ (∫⁻ x, f x ∂μ)⁻¹ < ∫⁻ x, (f x)⁻¹ ∂μ := by
  by_cases hf_const : f =ᵐ[μ] fun _ ↦ (∫⁻ x, f x ∂μ)
  · exact .inl hf_const
  right
  have h_int_ne_zero : ∫⁻ x, f x ∂μ ≠ 0 := by
    by_contra! h
    rw [h] at hf_const
    rw [lintegral_eq_zero_iff hf] at h
    exact hf_const h
  by_cases h_int_top : ∫⁻ x, f x ∂μ = ∞
  · simp only [h_int_top, inv_top, gt_iff_lt]
    by_contra! h
    simp only [nonpos_iff_eq_zero, ← Pi.inv_apply, lintegral_eq_zero_iff hf.inv] at h
    refine absurd h ?_
    rw [Filter.EventuallyEq]
    simp only [Pi.inv_apply, Pi.ofNat_apply, ENNReal.inv_eq_zero, Filter.not_eventually]
    exact hf_top.frequently
  by_cases h_int_inv_top : ∫⁻ x, (f x)⁻¹ ∂μ = ∞
  · simp [h_int_inv_top, pos_iff_ne_zero, h_int_ne_zero]
  have h_left_eq_add : (∫⁻ x, f x ∂μ)⁻¹
      = ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}, (∫⁻ y, f y ∂μ)⁻¹ ∂μ
        + ∫⁻ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (∫⁻ y, f y ∂μ)⁻¹ ∂μ := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, ne_eq]
    change _ = _ * μ {x | f x = ∫⁻ y, f y ∂μ} + _ * μ {x | f x = ∫⁻ y, f y ∂μ}ᶜ
    rw [← mul_add, measure_add_measure_compl, measure_univ, mul_one]
    exact measurableSet_eq_fun hf measurable_const
  have h_right_eq_add : ∫⁻ x, (f x)⁻¹ ∂μ
      = ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}, (f x)⁻¹ ∂μ
        + ∫⁻ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x)⁻¹ ∂μ := by
    change _ = _ + ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}ᶜ, (f x)⁻¹ ∂μ
    rw [lintegral_add_compl]
    exact measurableSet_eq_fun hf measurable_const
  rw [h_left_eq_add, h_right_eq_add]
  refine ENNReal.add_lt_add_of_le_of_lt ?_ ?_ ?_
  · simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, ne_eq]
    exact ENNReal.mul_ne_top (by simpa) (by simp)
  · refine le_of_eq ?_
    refine setLIntegral_congr_fun ?_ fun x hx ↦ ?_
    · exact measurableSet_eq_fun hf measurable_const
    simp only [mem_ofPred_eq] at hx
    rw [hx]
  · have h_cvx_lt x (hx : f x ≠ ∞) := Inv.lt_add_deriv_mul (y := ∫⁻ x, f x ∂μ) hx h_int_ne_zero
    rw [lintegral_eq_eintegral, lintegral_eq_eintegral (μ := μ.restrict {y | f y ≠ ∫⁻ z, f z ∂μ})]
    refine EReal.toENNReal_lt_toENNReal ?_ ?_
    · rw [eintegral_eq_lintegral]
      exact EReal.coe_ennreal_nonneg _
    have transform_eint_deriv : ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ},
        (f x)⁻¹ - Inv.deriv (∫⁻ z, f z ∂μ) * (f x - (∫⁻ z, f z ∂μ)) ∂μ =
        ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ
        - Inv.deriv (∫⁻ z, f z ∂μ) * ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ := by
      have h_eint : EIntegrable (fun x ↦ (f x : EReal) - ∫⁻ z, f z ∂μ)
          (μ.restrict {y | f y ≠ ∫⁻ z, f z ∂μ}) := by
        refine EIntegrable.sub_const ?_ (by simp) (by simp [h_int_top])
        exact eintegrable_of_nonneg fun _ ↦ by positivity
      rw [eintegral_sub]
      rotate_left
      · exact eintegrable_of_nonneg fun _ ↦ by positivity
      · fun_prop
      · exact h_eint.const_mul (by simp) (deriv_inv_ne_top h_int_ne_zero)
      · fun_prop
      · left
        rw [eintegral_eq_lintegral, ne_eq, EReal.coe_ennreal_eq_top_iff]
        refine ne_top_of_le_ne_top h_int_inv_top ?_
        exact setLIntegral_le_lintegral _ _
      · simp [eintegral_eq_lintegral]
      congr
      rw [eintegral_const_mul (by simp) _ h_eint]
      exact deriv_inv_ne_top h_int_ne_zero
    have eint_sub_eq_zero : ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ = 0 := by
      calc
      _ = ∫ᵉ x, (f x - ∫⁻ z, f z ∂μ) ∂μ := by
        nth_rw 2 [← eintegral_add_compl (A := {y | f y = ∫⁻ z, f z ∂μ})]
        swap; · exact measurableSet_eq_fun hf measurable_const
        suffices h_zero : ∫ᵉ x in {y | f y = ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ = 0 by
          rw [h_zero, zero_add]
          congr
        suffices ∀ x ∈ {y | f y = ∫⁻ z, f z ∂μ}, (f x : EReal) - ∫⁻ z, f z ∂μ = 0 by
          rw [eintegral_congr_ae (ae_restrict_of_forall_mem ?_ this)]
          · simp
          · exact measurableSet_eq_fun hf measurable_const
        intro x hx
        rw [hx, EReal.sub_self (by simp [h_int_top]) (by simp)]
      _ = 0 := by
        rw [eintegral_sub]
        · rw [eintegral_eq_lintegral]
          simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
          rw [EReal.sub_self (by simp [h_int_top]) (by simp)]
        · exact eintegrable_of_nonneg fun x ↦ by positivity
        · fun_prop
        · exact eintegrable_const
        · fun_prop
        · simp [h_int_top]
        · simp
    calc ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((∫⁻ y, f y ∂μ)⁻¹ : ℝ≥0∞) ∂μ
    _ < ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ},
        (f x)⁻¹ - Inv.deriv (∫⁻ z, f z ∂μ) * (f x - ∫⁻ z, f z ∂μ) ∂μ := by
      refine eintegral_strict_mono_ae ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [ne_eq, Measure.restrict_eq_zero]
        have : μ {x | f x = ∫⁻ x, f x ∂μ}ᶜ ≠ 0 := hf_const
        simpa [Set.compl_def]
      · fun_prop
      · fun_prop
      · rw [ae_restrict_iff']
        swap; · exact (measurableSet_eq_fun hf measurable_const).compl
        filter_upwards [hf_top] with x hx hx_ne
        specialize h_cvx_lt x hx hx_ne
        rwa [EReal.lt_sub_iff_add_lt (by simp [h_int_ne_zero]) (by simp)]
      · simp [h_int_ne_zero, lt_top_iff_ne_top, EReal.mul_ne_top]
      · rw [transform_eint_deriv, ne_eq, EReal.sub_eq_bot, not_or]
        refine ⟨?_, ?_⟩
        · suffices 0 ≤ ∫ᵉ x in {y | f y ≠ ∫⁻ (z : α), f z ∂μ}, ↑(f x)⁻¹ ∂μ from
            (lt_of_le_of_lt' this (by trivial)).ne'
          refine eintegral_nonneg fun x ↦ ?_
          positivity
        · rw [← ne_eq, EReal.mul_ne_top]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp
          · simp [eint_sub_eq_zero]
          · left
            exact deriv_inv_ne_top h_int_ne_zero
          · simp [eint_sub_eq_zero]
    _ = ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ
        - Inv.deriv (∫⁻ z, f z ∂μ) * ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ :=
      transform_eint_deriv
    _ = ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ :=
      suffices ∫ᵉ x in {y | f y ≠ ∫⁻ (z : α), f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ = 0 by simp [this]
      eint_sub_eq_zero

theorem Inv.ae_eq_const_or_map_lintegral_lt [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ (∫⁻ x, f x ∂μ)⁻¹ < ∫⁻ x, (f x)⁻¹ ∂μ := by
  have hf_top' : ∀ᵐ x ∂μ, hf.mk f x ≠ ∞ := by
    filter_upwards [hf_top, hf.ae_eq_mk] with x hx_ne hx_eq using by rwa [← hx_eq]
  have h := Inv.ae_eq_const_or_map_lintegral_lt' hf.measurable_mk (μ := μ) hf_top'
  cases h with
  | inl h =>
    left
    filter_upwards [hf.ae_eq_mk, h] with x hx_eq hx_const
    rw [hx_eq, hx_const]
    congr 1
    exact lintegral_congr_ae hf.ae_eq_mk.symm
  | inr h =>
    right
    rw [lintegral_congr_ae hf.ae_eq_mk]
    refine h.trans_eq ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk] with x hx_eq
    rw [hx_eq]

theorem Inv.ae_eq_const_or_map_set_lintegral_lt (ht : MeasurableSet t)
    (hf : AEMeasurable f (μ.restrict t)) (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤)
    (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    f =ᵐ[μ.restrict t] const α ((μ t)⁻¹ * ∫⁻ x in t, f x ∂μ) ∨
      μ t * (∫⁻ x in t, f x ∂μ)⁻¹ < (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  have : IsProbabilityMeasure μ[|t] := cond_isProbabilityMeasure_of_finite hμ_t₀ hμ_t₁
  replace hf : AEMeasurable f μ[|t] := hf.cond
  replace ht_top : ∀ᵐ x ∂μ[|t], f x ≠ ⊤ := by
    unfold ProbabilityTheory.cond
    rw [← μ.restrict_smul, ae_restrict_iff' ht]
    change ((μ t)⁻¹ • μ) {x | x ∈ t → f x ≠ ⊤}ᶜ = 0
    rw [Measure.smul_apply]
    exact smul_eq_zero_of_right (μ t)⁻¹ ht_top
  rcases Inv.ae_eq_const_or_map_lintegral_lt hf ht_top with h | h
  · left
    unfold Filter.EventuallyEq at h ⊢
    rw [ae_restrict_iff' ht]
    simp only [const_apply] at h ⊢
    change μ {x | x ∈ t → f x = ((μ t)⁻¹ * ∫⁻ x in t, f x ∂μ)}ᶜ = 0
    replace h : μ[|t] {x | f x = ∫⁻ x, f x ∂μ[|t]}ᶜ = 0 := h
    simp_all only [ne_eq, ProbabilityTheory.cond, ENNReal.inv_eq_zero, not_false_eq_true,
      aemeasurable_smul_measure_iff, lintegral_smul_measure, smul_eq_mul, Measure.smul_apply,
      Measure.restrict_apply', mul_eq_zero, false_or]
    rw [← h]
    congr
    simp only [compl_def, mem_ofPred_eq, Classical.not_imp]
    ext x
    constructor
    · rintro ⟨hxt, hx⟩
      refine ⟨hx, hxt⟩
    · rintro ⟨hx, hxt⟩
      refine ⟨hxt, hx⟩
  · right
    calc
    _ = (∫⁻ x, f x ∂μ[|t])⁻¹ := by
      simp only [lintegral_smul_measure, smul_eq_mul, ProbabilityTheory.cond]
      rw [ENNReal.mul_inv, inv_inv]
      · left
        simp [hμ_t₁]
      · left
        simp [hμ_t₀]
    _ < ∫⁻ x, (f x)⁻¹ ∂μ[|t] := h
    _ = (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
      simp [ProbabilityTheory.cond]
