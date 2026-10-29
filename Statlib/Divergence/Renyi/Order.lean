/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Variational

/-!
# The Rényi divergence as a function of its order

We prove that `a ↦ Rₐ(μ, ν)` is monotone on `[0, ∞)`, for finite measures with `μ ≠ 0`, and that
`R₀(μ, ν)` is the limit of `Rₐ(μ, ν)` as `a → 0⁺`. The limits at the order `1` and the continuity
in the order are in `Statlib.Divergence.Renyi.Order.Limits`.

The main tool is the log-convexity of `a ↦ ∫ (∂μ/∂ν) ^ a ∂ν`, a consequence of Hölder's
inequality (`integral_rpow_rnDeriv_le_rpow_mul_rpow`). For probability measures,
`Rₐ(μ, ν) = log (∫ (∂μ/∂ν) ^ a ∂ν) / (a - 1)` for `a ∈ (0, 1) ∪ (1, ∞)` (when finite), and
log-convexity together with `∫ ∂μ/∂ν ∂ν ≤ 1` (with equality when `μ ≪ ν`) gives the comparisons
between positive orders different from `1`. The order `1` (Kullback-Leibler divergence) is handled
with the variational formula for `a < 1` and with the limit of `(a - 1)⁻¹ * log ∫ (∂μ/∂ν) ^ a ∂ν`
as `a → 1⁻` for `a > 1`. The order `0` is handled by the limit `Rₐ(μ, ν) → R₀(μ, ν)` as `a → 0⁺`,
which follows from `∫ (∂μ/∂ν) ^ a ∂ν → ν {x | 0 < (∂μ/∂ν) x}` (dominated convergence).

## Main statements

* `tendsto_renyiDiv_nhdsGT_zero`: for finite measures, `Rₐ(μ, ν) → R₀(μ, ν)` as `a → 0⁺`.
* `renyiDiv_le_renyiDiv_of_le`: for finite measures with `μ ≠ 0`, `a ↦ Rₐ(μ, ν)` is monotone on
  `[0, ∞)`.
* `monotoneOn_renyiDiv`: the same statement with `MonotoneOn`.
* `iSup_Ioo_mul_renyiDiv_eq_iSup_Icc`:
  `⨆ a ∈ (0, 1), (1 - a) * Rₐ(μ, ν) = ⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν)`.

## Implementation notes

The statements are proved for probability measures, then extended to finite measures with
`renyiDiv_eq_renyiDiv_inv_smul`. Monotonicity requires `μ ≠ 0`: `Rₐ(0, ν)` is `∞` for `a < 1` and
`0` for `a > 1`.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), Theorems 3 and 7.
-/

@[expose] public section

open MeasureTheory Filter Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a b : ℝ}

section Probability

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-! ### Comparisons between positive orders -/

/-- Monotonicity of the Rényi divergence on `(0, 1)`. -/
private lemma renyiDiv_le_renyiDiv_of_lt_one (ha_pos : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  have ha1 : a < 1 := hab.trans_lt hb
  have hb_pos : 0 < b := ha_pos.trans_le hab
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one hb_pos.le hb).mpr h_ms]
    exact le_top
  have ha_top : renyiDiv a μ ν ≠ ∞ :=
    fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_pos.le ha1).mp h)
  have hb_top : renyiDiv b μ ν ≠ ∞ :=
    fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one hb_pos.le hb).mp h)
  rw [← ENNReal.ofReal_toReal ha_top, ← ENNReal.ofReal_toReal hb_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha_pos ha1.ne ha_top,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure hb_pos hb.ne hb_top, ← div_eq_inv_mul,
    ← div_eq_inv_mul]
  have hIa := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha_pos ha_top
  have hIb := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top hb_pos hb_top
  set Ia := ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν with hIa_def
  set Ib := ∫ x, ((∂μ/∂ν) x).toReal ^ b ∂ν with hIb_def
  set θ := (1 - b) / (1 - a) with hθ
  have h1a : 0 < 1 - a := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) h1a.le
  have hθ1 : θ ≤ 1 := (div_le_one h1a).mpr (by linarith)
  -- Hölder: `Ib ≤ Ia ^ θ * I₁ ^ (1 - θ) ≤ Ia ^ θ`
  have h_holder := integral_rpow_rnDeriv_le_rpow_mul_rpow (c := b) ha_pos.le zero_le_one hθ0 hθ1
      (by rw [hθ]; field_simp; ring) (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha1)
      (by simpa using Measure.integrable_toReal_rnDeriv (μ := μ) (ν := ν))
  have hI1 : ∫ x, ((∂μ/∂ν) x).toReal ^ (1 : ℝ) ∂ν ≤ 1 := by
    simp [Measure.integral_toReal_rnDeriv']
  have h_le : Ib ≤ Ia ^ θ := by
    refine h_holder.trans ?_
    refine mul_le_of_le_one_right (by positivity) ?_
    exact Real.rpow_le_one integral_rpow_rnDeriv_nonneg hI1 (by linarith)
  have h_log : Real.log Ib ≤ θ * Real.log Ia := by
    rw [← Real.log_rpow hIa]
    exact Real.log_le_log hIb h_le
  have h_eq : Real.log Ia / (a - 1) = θ * Real.log Ia / (b - 1) := by
    rw [hθ]
    have : b - 1 ≠ 0 := by linarith
    have : a - 1 ≠ 0 := by linarith
    have : 1 - a ≠ 0 := by linarith
    field_simp
    ring
  rw [h_eq]
  exact div_le_div_of_nonpos_of_le (by linarith) h_log

/-- For `a < 1 < b`, `Rₐ(μ, ν) ≤ R_b(μ, ν)`. -/
private lemma renyiDiv_le_renyiDiv_of_lt_one_of_one_lt (ha_pos : 0 < a) (ha : a < 1) (hb : 1 < b) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  have hb_pos : 0 < b := by linarith
  by_cases hb_top : renyiDiv b μ ν = ∞
  · rw [hb_top]; exact le_top
  obtain ⟨hb_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt hb).mp hb_top
  have ha_top : renyiDiv a μ ν ≠ ∞ := fun h ↦ hb_top (renyiDiv_of_mutuallySingular hb_pos.le
    ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_pos.le ha).mp h))
  rw [← ENNReal.ofReal_toReal ha_top, ← ENNReal.ofReal_toReal hb_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha_pos ha.ne ha_top,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure hb_pos hb.ne' hb_top, ← div_eq_inv_mul,
    ← div_eq_inv_mul]
  have hIa := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha_pos ha_top
  have hIb := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top hb_pos hb_top
  set Ia := ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν with hIa_def
  set Ib := ∫ x, ((∂μ/∂ν) x).toReal ^ b ∂ν with hIb_def
  have hba : 0 < b - a := by linarith
  set θ := (b - 1) / (b - a) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hba.le
  have hθ1 : θ ≤ 1 := (div_le_one hba).mpr (by linarith)
  -- Hölder: `1 = I₁ ≤ Ia ^ θ * Ib ^ (1 - θ)`
  have h_holder := integral_rpow_rnDeriv_le_rpow_mul_rpow (c := 1) ha_pos.le hb_pos.le hθ0 hθ1
      (by rw [hθ]; field_simp; ring) (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha) hb_int
  have hI1 : ∫ x, ((∂μ/∂ν) x).toReal ^ (1 : ℝ) ∂ν = 1 := by
    simp [Measure.integral_toReal_rnDeriv h_ac]
  rw [hI1] at h_holder
  have h_log : 0 ≤ θ * Real.log Ia + (1 - θ) * Real.log Ib := by
    rw [← Real.log_rpow hIa, ← Real.log_rpow hIb, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_nonneg h_holder
  have h_log' : 0 ≤ (b - 1) * Real.log Ia + (1 - a) * Real.log Ib := by
    calc 0 ≤ (b - a) * (θ * Real.log Ia + (1 - θ) * Real.log Ib) := mul_nonneg hba.le h_log
      _ = (b - 1) * Real.log Ia + (1 - a) * Real.log Ib := by rw [hθ]; field_simp; ring
  have h_eq : Real.log Ia / (a - 1) = - Real.log Ia / (1 - a) := by
    rw [← neg_sub, div_neg, neg_div]
  rw [h_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- Monotonicity of the Rényi divergence on `(1, ∞)`. -/
private lemma renyiDiv_le_renyiDiv_of_one_lt (ha : 1 < a) (hab : a ≤ b) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  have hb : 1 < b := ha.trans_le hab
  by_cases hb_top : renyiDiv b μ ν = ∞
  · rw [hb_top]; exact le_top
  obtain ⟨hb_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt hb).mp hb_top
  have hb1 : 0 < b - 1 := by linarith
  set θ := (b - a) / (b - 1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hb1.le
  have hθ1 : θ ≤ 1 := (div_le_one hb1).mpr (by linarith)
  have hc : a = θ * 1 + (1 - θ) * b := by rw [hθ]; field_simp; ring
  have ha_int := integrable_rpow_rnDeriv_of_le (by linarith) hab hb_int
  have ha_top : renyiDiv a μ ν ≠ ∞ := (renyiDiv_ne_top_iff_of_one_lt ha).mpr ⟨ha_int, h_ac⟩
  rw [← ENNReal.ofReal_toReal ha_top, ← ENNReal.ofReal_toReal hb_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure (by linarith) ha.ne' ha_top,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure (by linarith) hb.ne' hb_top, ← div_eq_inv_mul,
    ← div_eq_inv_mul]
  have hIa := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith) ha_top
  have hIb := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith) hb_top
  set Ia := ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν with hIa_def
  set Ib := ∫ x, ((∂μ/∂ν) x).toReal ^ b ∂ν with hIb_def
  have h_holder := integral_rpow_rnDeriv_le_rpow_mul_rpow (c := a) zero_le_one (by linarith)
    hθ0 hθ1 hc
    (by simpa using Measure.integrable_toReal_rnDeriv (μ := μ) (ν := ν)) hb_int
  have hI1 : ∫ x, ((∂μ/∂ν) x).toReal ^ (1 : ℝ) ∂ν = 1 := by
    simp [Measure.integral_toReal_rnDeriv h_ac]
  rw [hI1, Real.one_rpow, one_mul] at h_holder
  have h_log : Real.log Ia ≤ (1 - θ) * Real.log Ib := by
    rw [← Real.log_rpow hIb]
    exact Real.log_le_log hIa h_holder
  have h1θ : 1 - θ = (a - 1) / (b - 1) := by rw [hθ]; field_simp; ring
  rw [h1θ] at h_log
  rw [div_le_div_iff₀ (by linarith) hb1]
  calc Real.log Ia * (b - 1) ≤ (a - 1) / (b - 1) * Real.log Ib * (b - 1) := by gcongr
    _ = Real.log Ib * (a - 1) := by field_simp

/-- For `a ∈ (0, 1)`, `Rₐ(μ, ν) ≤ KL(μ, ν)`, by the variational formula. -/
private lemma renyiDiv_le_renyiDiv_one (ha_pos : 0 < a) (ha : a < 1) :
    renyiDiv a μ ν ≤ renyiDiv 1 μ ν := by
  rw [renyiDiv_one_of_isProbabilityMeasure]
  have h_le : ENNReal.ofReal (1 - a) * renyiDiv a μ ν ≤ ENNReal.ofReal (1 - a) * klDiv μ ν :=
    (mul_renyiDiv_le_mul_klDiv_add_mul_klDiv μ ν μ ha_pos ha).trans_eq (by simp [klDiv_self])
  exact (ENNReal.mul_le_mul_iff_right (by simpa using ha) ENNReal.ofReal_ne_top).mp h_le

/-- For `b > 1`, `KL(μ, ν) ≤ R_b(μ, ν)`. -/
private lemma renyiDiv_one_le_renyiDiv (hb : 1 < b) : renyiDiv 1 μ ν ≤ renyiDiv b μ ν := by
  by_cases hb_top : renyiDiv b μ ν = ∞
  · rw [hb_top]; exact le_top
  obtain ⟨hb_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt hb).mp hb_top
  have h_llr : Integrable (llr μ ν) μ := integrable_llr_of_integrable_rpow_rnDeriv hb h_ac hb_int
  rw [renyiDiv_one_of_isProbabilityMeasure, ← ENNReal.ofReal_toReal (klDiv_ne_top h_ac h_llr),
    ← ENNReal.ofReal_toReal hb_top, toReal_klDiv_of_measure_eq h_ac (by simp)]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_of_tendsto (tendsto_mul_log_integral_rpow_rnDeriv h_ac h_llr) ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with a ha
  have ha_le := renyiDiv_le_renyiDiv_of_lt_one_of_one_lt (μ := μ) (ν := ν) ha.1 ha.2 hb
  have ha_top : renyiDiv a μ ν ≠ ∞ := ne_top_of_le_ne_top hb_top ha_le
  rw [← toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha.1 ha.2.ne ha_top]
  exact ENNReal.toReal_mono hb_top ha_le

/-! ### The order `0` -/

/-- For probability measures, `Rₐ(μ, ν) → R₀(μ, ν)` as `a → 0⁺`. -/
private lemma tendsto_renyiDiv_nhdsGT_zero_of_isProbabilityMeasure :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[>] 0) (𝓝 (renyiDiv 0 μ ν)) := by
  have h_mem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one le_rfl zero_lt_one).mpr h_ms]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h_mem] with a ha
    exact ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha.1.le ha.2).mpr h_ms).symm
  set p := ν {x | 0 < (∂μ/∂ν) x} with hp
  have hs : MeasurableSet {x | 0 < (∂μ/∂ν) x} :=
    measurableSet_lt measurable_const (μ.measurable_rnDeriv ν)
  have hp_zero : p ≠ 0 := by
    intro hp0
    rw [hp] at hp0
    refine h_ms ((Measure.rnDeriv_eq_zero μ ν).mp ?_)
    rw [Filter.EventuallyEq, ae_iff]
    simpa [pos_iff_ne_zero] using hp0
  have hp_top : p ≠ ∞ := measure_ne_top _ _
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have h_zero : renyiDiv 0 μ ν = ENNReal.ofReal (-Real.log p.toReal) := by
    rw [renyiDiv_zero, measure_univ, div_one, ← hp, ENNReal.log_pos_real hp_zero hp_top,
      ← EReal.coe_neg, EReal.real_coe_toENNReal]
  -- `∫ (∂μ/∂ν) ^ a ∂ν → ν {0 < ∂μ/∂ν}` by dominated convergence
  have h_int_tendsto : Tendsto (fun a : ℝ ↦ ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) (𝓝[>] 0)
      (𝓝 p.toReal) := by
    have hp_eq : p.toReal = ∫ x, {x | 0 < (∂μ/∂ν) x}.indicator 1 x ∂ν := by
      rw [integral_indicator_one hs, measureReal_def]
    rw [hp_eq]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ 1 + ((∂μ/∂ν) x).toReal ^ (1 : ℝ)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun a ↦
        ((μ.measurable_rnDeriv ν).ennreal_toReal.pow_const _).aestronglyMeasurable
    · filter_upwards [h_mem] with a ha
      refine Eventually.of_forall fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_add_rpow ENNReal.toReal_nonneg ha.1.le ha.2.le
    · exact (integrable_const _).add (by simpa using Measure.integrable_toReal_rnDeriv)
    · filter_upwards [μ.rnDeriv_lt_top ν] with x hx
      by_cases hx0 : 0 < (∂μ/∂ν) x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < (∂μ/∂ν) x} from hx0)]
        have h_pos : 0 < ((∂μ/∂ν) x).toReal := ENNReal.toReal_pos hx0.ne' hx.ne
        have h := (Real.continuousAt_const_rpow (b := 0) h_pos.ne').tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using h
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < (∂μ/∂ν) x} from hx0)]
        have hx0' : (∂μ/∂ν) x = 0 := by simpa using hx0
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with a ha
        simp [hx0', Real.zero_rpow (ne_of_gt (Set.mem_Ioi.mp ha))]
  have h_log : Tendsto (fun a : ℝ ↦ Real.log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) / (a - 1))
      (𝓝[>] 0) (𝓝 (-Real.log p.toReal)) := by
    have h1 : Tendsto (fun a : ℝ ↦ a - 1) (𝓝[>] 0) (𝓝 (-1)) := by
      have := ((continuous_sub_right (1 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have h2 := ((Real.continuousAt_log hp_pos.ne').tendsto.comp h_int_tendsto).div h1
      (by norm_num)
    rw [div_neg, div_one] at h2
    exact h2
  rw [h_zero]
  refine (ENNReal.tendsto_ofReal h_log).congr' ?_
  filter_upwards [h_mem] with a ha
  have ha_top : renyiDiv a μ ν ≠ ∞ :=
    fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha.1.le ha.2).mp h)
  rw [← ENNReal.ofReal_toReal ha_top,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha.1 ha.2.ne ha_top,
    div_eq_inv_mul]

/-- For probability measures, `a ↦ Rₐ(μ, ν)` is monotone on `(0, ∞)`. -/
private lemma renyiDiv_le_renyiDiv_of_pos_of_isProbabilityMeasure (ha_pos : 0 < a) (hab : a ≤ b) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  rcases lt_trichotomy a 1 with ha1 | rfl | ha1
  · rcases lt_trichotomy b 1 with hb | rfl | hb
    · exact renyiDiv_le_renyiDiv_of_lt_one ha_pos hab.le hb
    · exact renyiDiv_le_renyiDiv_one ha_pos ha1
    · exact renyiDiv_le_renyiDiv_of_lt_one_of_one_lt ha_pos ha1 hb
  · exact renyiDiv_one_le_renyiDiv hab
  · exact renyiDiv_le_renyiDiv_of_one_lt ha1 hab.le

/-- For probability measures, `a ↦ Rₐ(μ, ν)` is monotone on `[0, ∞)`. -/
private lemma renyiDiv_le_renyiDiv_of_le_of_isProbabilityMeasure (ha : 0 ≤ a) (hab : a ≤ b) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · rcases hab.eq_or_lt with rfl | hb
    · exact le_rfl
    -- `R₀(μ, ν)` is the limit of `Rₐ(μ, ν) ≤ R_b(μ, ν)` as `a → 0⁺`
    refine le_of_tendsto tendsto_renyiDiv_nhdsGT_zero_of_isProbabilityMeasure ?_
    filter_upwards [Ioo_mem_nhdsGT hb] with a ha
    exact renyiDiv_le_renyiDiv_of_pos_of_isProbabilityMeasure ha.1 ha.2.le
  exact renyiDiv_le_renyiDiv_of_pos_of_isProbabilityMeasure ha_pos hab

end Probability

/-- For finite measures, `Rₐ(μ, ν) → R₀(μ, ν)` as `a → 0⁺`. -/
theorem tendsto_renyiDiv_nhdsGT_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[>] 0) (𝓝 (renyiDiv 0 μ ν)) := by
  have h_mem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [renyiDiv_zero_measure_left le_rfl zero_ne_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h_mem] with a ha
    rw [renyiDiv_zero_measure_left ha.1.le ha.2.ne]
    simp [ha.2]
  rcases eq_zero_or_neZero ν with rfl | hν
  · rw [renyiDiv_zero_measure_right le_rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h_mem] with a ha
    rw [renyiDiv_zero_measure_right ha.1.le]
  rw [renyiDiv_eq_renyiDiv_inv_smul le_rfl]
  refine tendsto_renyiDiv_nhdsGT_zero_of_isProbabilityMeasure.congr' ?_
  filter_upwards [h_mem] with a ha
  exact (renyiDiv_eq_renyiDiv_inv_smul ha.1.le).symm

/-- For finite measures with `μ ≠ 0`, `a ↦ Rₐ(μ, ν)` is monotone on `[0, ∞)`. -/
@[gcongr]
theorem renyiDiv_le_renyiDiv_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ]
    (ha : 0 ≤ a) (hab : a ≤ b) :
    renyiDiv a μ ν ≤ renyiDiv b μ ν := by
  rcases eq_zero_or_neZero ν with rfl | hν
  · rw [renyiDiv_zero_measure_right (ha.trans hab)]
    exact le_top
  rw [renyiDiv_eq_renyiDiv_inv_smul ha, renyiDiv_eq_renyiDiv_inv_smul (ha.trans hab)]
  exact renyiDiv_le_renyiDiv_of_le_of_isProbabilityMeasure ha hab

/-- For finite measures with `μ ≠ 0`, `a ↦ Rₐ(μ, ν)` is monotone on `[0, ∞)`. -/
theorem monotoneOn_renyiDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] :
    MonotoneOn (fun a ↦ renyiDiv a μ ν) (Ici 0) :=
  fun _ ha _ _ hab ↦ renyiDiv_le_renyiDiv_of_le ha hab

/-- The supremum of `(1 - a) * Rₐ(μ, ν)` over `a ∈ [0, 1]` is the supremum over `a ∈ (0, 1)`: the
term for `a = 1` is `0` and the term for `a = 0` is a limit of terms with `a ∈ (0, 1)`. -/
lemma iSup_Ioo_mul_renyiDiv_eq_iSup_Icc [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⨆ a ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν
      = ⨆ a ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν := by
  set f : ℝ → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (1 - a) * renyiDiv a μ ν
  have h_le : ∀ a ∈ Ioo (0 : ℝ) 1, f a ≤ ⨆ a ∈ Ioo (0 : ℝ) 1, f a :=
    fun a ha ↦ le_iSup₂ (f := fun a (_ : a ∈ Ioo (0 : ℝ) 1) ↦ f a) a ha
  refine le_antisymm (biSup_mono fun _ h ↦ Ioo_subset_Icc_self h) (iSup₂_le fun a ha ↦ ?_)
  rcases ha.1.eq_or_lt with rfl | ha0
  · have h_tendsto : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := by
      refine ENNReal.Tendsto.mul ?_ (by simp) tendsto_renyiDiv_nhdsGT_zero (by simp)
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
    refine le_of_tendsto h_tendsto ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with a ha using h_le a ha
  rcases ha.2.eq_or_lt with rfl | ha1
  · simp
  · exact h_le a ⟨ha0, ha1⟩

end ProbabilityTheory
