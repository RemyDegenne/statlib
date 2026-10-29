/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.Binary

/-!
# Best constant in an inequality between two f-divergences

Let `f, g` be two divergence functions. For all measures `μ, ν`, the ratio
`D_f(μ, ν) / D_g(μ, ν)` is at most the supremum of `f t / g t` over `t ∈ (0, 1) ∪ (1, ∞)`. If `g`
is differentiable at `1` (where its derivative is then `0`, since `1` is a minimum) and the
measurable space is not trivial, then this is the best constant: the supremum of
`D_f(μ, ν) / D_g(μ, ν)` over probability measures `μ, ν` is the supremum of `f t / g t` over
`t ∈ (0, 1) ∪ (1, ∞)` (Sason and Verdú).

For the lower bound, we use the Bernoulli distributions `μ = Ber(x, y, t ε)` and
`ν = Ber(x, y, ε)`, for which `D_f(μ, ν) = ε f(t) + (1 - ε) f((1 - t ε) / (1 - ε))`, and let
`ε → 0`: `D_g(μ, ν) / ε` tends to `g t`, while `D_f(μ, ν) / ε ≥ f t`.

## Main statements

* `fDiv_div_fDiv_le_iSup_div`: `D_f(μ, ν) / D_g(μ, ν) ≤ ⨆ t ∉ {0, 1, ∞}, f t / g t`.
* `iSup_fDiv_div_fDiv_eq_iSup_div`: the theorem of Sason and Verdú.

## Implementation notes

Sason and Verdú assume that both `f` and `g` are differentiable at `1` and that `g > 0` on
`(0, 1) ∪ (1, ∞)`. Differentiability of `f` is not needed: since `f ≥ 0`, `D_f(μ, ν) / ε ≥ f t`.
The positivity of `g` is not needed with the conventions `a / 0 = ∞` for `a ≠ 0` and `0 / 0 = 0`
of `ℝ≥0∞`. Differentiability of `g` cannot be dropped: for `f t = (t - 1)⁺` and `g t = |t - 1|`,
the supremum of `f t / g t` is `1` but `D_f(μ, ν) / D_g(μ, ν) = 1 / 2` for all probability
measures `μ ≠ ν`.

## References

* I. Sason, S. Verdú, *f-divergence inequalities*, IEEE Transactions on Information Theory
  62(11) (2016), Theorem 1.
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {f g : DivFunction}

/-- If `F` vanishes with its derivative at `1`, then `(1 - ε) / ε * F ((1 - r ε) / (1 - ε))` tends
to `0` as `ε → 0+`. -/
private lemma tendsto_div_mul_apply_div_nhdsGT_zero {F : ℝ → ℝ} (hF : HasDerivAt F 0 1)
    (hF1 : F 1 = 0) {r : ℝ} (hr : r ≠ 1) :
    Tendsto (fun ε ↦ (1 - ε) / ε * F ((1 - r * ε) / (1 - ε))) (𝓝[>] 0) (𝓝 0) := by
  have h_mem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr hr.symm
  have hs_sub (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
      (1 - r * ε) / (1 - ε) - 1 = ε * (1 - r) / (1 - ε) := by
    have : 1 - ε ≠ 0 := by linarith [hε.2]
    field_simp
    ring
  -- `(1 - r ε) / (1 - ε)` tends to `1` and is not equal to `1`
  have h_s : Tendsto (fun ε ↦ (1 - r * ε) / (1 - ε)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h_cont : ContinuousAt (fun ε : ℝ ↦ (1 - r * ε) / (1 - ε)) 0 :=
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
          (continuousAt_const.sub continuousAt_id) (by norm_num)
      simpa using h_cont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [h_mem] with ε hε
      rw [mem_compl_singleton_iff, ← sub_ne_zero, hs_sub ε hε]
      have : 1 - ε ≠ 0 := by linarith [hε.2]
      exact div_ne_zero (mul_ne_zero hε.1.ne' h1r) this
  -- the slope of `F` at `1` tends to `0`
  have h_slope : Tendsto (fun y ↦ F y / (y - 1)) (𝓝[≠] 1) (𝓝 0) :=
    (hasDerivAt_iff_tendsto_slope.mp hF).congr fun y ↦ by rw [slope_def_field, hF1, sub_zero]
  have h := (h_slope.comp h_s).const_mul (1 - r)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [h_mem] with ε hε
  have h1ε : 1 - ε ≠ 0 := by linarith [hε.2]
  simp only [Function.comp_apply]
  rw [hs_sub ε hε]
  field_simp

/-- For all measures `μ, ν`, the ratio `D_f(μ, ν) / D_g(μ, ν)` is at most the supremum of
`f t / g t` over `t ∈ (0, 1) ∪ (1, ∞)`. -/
lemma fDiv_div_fDiv_le_iSup_div (μ ν : Measure 𝓧) :
    fDiv f μ ν / fDiv g μ ν ≤ ⨆ (t : ℝ≥0∞) (_ : t ≠ 0) (_ : t ≠ ∞) (_ : t ≠ 1), f t / g t := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  rcases eq_or_ne c ∞ with rfl | hc_top
  · exact le_top
  have hc0 : c ≠ 0 := (zero_le.trans_lt hc).ne'
  -- `f ≤ c * g`, since `c` is larger than all the ratios `f t / g t`
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.coe_toNNReal hc_top]
  refine fDiv_le_mul_fDiv_of_le (fun x hx0 hx_top ↦ ?_) μ ν
  rcases eq_or_ne x 1 with rfl | hx1
  · simp
  rw [ENNReal.coe_toNNReal hc_top, ← ENNReal.div_le_iff_le_mul (Or.inr hc_top) (Or.inr hc0)]
  exact hc.le.trans' <| le_iSup_of_le x <| le_iSup_of_le hx0 <| le_iSup_of_le hx_top <|
    le_iSup_of_le hx1 le_rfl

/-- **Sason–Verdú**: if `g` is differentiable at `1`, then on a measurable space with a
measurable set `E` such that `E` and `Eᶜ` are nonempty, the supremum of `D_f(μ, ν) / D_g(μ, ν)`
over probability measures `μ, ν` is the supremum of `f t / g t` over `t ∈ (0, 1) ∪ (1, ∞)`. -/
theorem iSup_fDiv_div_fDiv_eq_iSup_div {E : Set 𝓧} (hE : MeasurableSet E)
    (hE_nonempty : E.Nonempty) (hE_compl : Eᶜ.Nonempty) (hg : DifferentiableAt ℝ g.realFun 1) :
    ⨆ (μ : Measure 𝓧) (ν : Measure 𝓧) (_ : IsProbabilityMeasure μ) (_ : IsProbabilityMeasure ν),
        fDiv f μ ν / fDiv g μ ν
      = ⨆ (t : ℝ≥0∞) (_ : t ≠ 0) (_ : t ≠ ∞) (_ : t ≠ 1), f t / g t := by
  refine le_antisymm (iSup₂_le fun μ ν ↦ iSup₂_le fun _ _ ↦ fDiv_div_fDiv_le_iSup_div μ ν) ?_
  obtain ⟨x, hx⟩ := hE_nonempty
  obtain ⟨y, hy⟩ := hE_compl
  set L := ⨆ (μ : Measure 𝓧) (ν : Measure 𝓧) (_ : IsProbabilityMeasure μ)
    (_ : IsProbabilityMeasure ν), fDiv f μ ν / fDiv g μ ν
  refine iSup_le fun t ↦ iSup_le fun ht0 ↦ iSup_le fun ht_top ↦ iSup_le fun ht1 ↦ ?_
  -- the cases `0 / 0` and `∞ / ∞` are trivial
  by_cases h_zero : f t = 0 ∧ g t = 0
  · simp [h_zero.1, h_zero.2]
  by_cases h_top : g t = ∞ ∧ f t = ∞
  · simp [h_top.1, h_top.2]
  rw [not_and_or] at h_zero h_top
  set r := t.toReal
  have hr : 0 < r := ENNReal.toReal_pos ht0 ht_top
  have ht : t = ENNReal.ofReal r := (ENNReal.ofReal_toReal ht_top).symm
  have hr1 : r ≠ 1 := fun h ↦ ht1 (by rw [ht, h, ENNReal.ofReal_one])
  have h_mem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (min 1 r⁻¹) :=
    Ioo_mem_nhdsGT (lt_min zero_lt_one (inv_pos.mpr hr))
  -- for small `ε`, the ratio of the f-divergences between `Ber(x, y, r ε)` and `Ber(x, y, ε)`
  -- is at most `L`
  have h_le {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (min 1 r⁻¹)) :
      (f t + ENNReal.ofReal ((1 - ε) / ε) * f (ENNReal.ofReal ((1 - r * ε) / (1 - ε))))
        / (g t + ENNReal.ofReal ((1 - ε) / ε) * g (ENNReal.ofReal ((1 - r * ε) / (1 - ε))))
        ≤ L := by
    have hε0 : 0 < ε := hε.1
    have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
    have hrε : r * ε < 1 :=
      calc r * ε < r * r⁻¹ := by gcongr; exact hε.2.trans_le (min_le_right _ _)
      _ = 1 := mul_inv_cancel₀ hr.ne'
    set p : I := ⟨r * ε, by positivity, hrε.le⟩
    set q : I := ⟨ε, hε0.le, hε1.le⟩
    have hq0 : q ≠ 0 := coe_ne_zero.mp hε0.ne'
    have hq1 : q ≠ 1 := coe_ne_one.mp hε1.ne
    have h_eq (φ : DivFunction) : fDiv φ Ber(x, y, p) Ber(x, y, q)
        = ENNReal.ofReal ε
          * (φ t + ENNReal.ofReal ((1 - ε) / ε) * φ (ENNReal.ofReal ((1 - r * ε) / (1 - ε)))) := by
      have h_div : (p : ℝ) / q = r := mul_div_cancel_right₀ r hε0.ne'
      have h_mul : ENNReal.ofReal ε * ENNReal.ofReal ((1 - ε) / ε) = ENNReal.ofReal (1 - ε) := by
        rw [← ENNReal.ofReal_mul hε0.le]
        congr 1
        field_simp
      rw [fDiv_bernoulliMeasure_of_mem_of_notMem hE hx hy,
        fDiv_bernoulliMeasure_of_ne_zero_of_ne_one (by decide) p hq0 hq1, h_div, mul_add,
        ← mul_assoc, h_mul, ← ht]
    calc _ = fDiv f Ber(x, y, p) Ber(x, y, q) / fDiv g Ber(x, y, p) Ber(x, y, q) := by
          rw [h_eq f, h_eq g, ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.mpr hε0).ne'
            ENNReal.ofReal_ne_top]
      _ ≤ L := le_iSup_of_le Ber(x, y, p) <| le_iSup_of_le Ber(x, y, q) <|
          le_iSup_of_le inferInstance <| le_iSup_of_le inferInstance le_rfl
  -- the g-divergence divided by `ε` tends to `g t`
  have h_lim : Tendsto (fun ε ↦ g t
          + ENNReal.ofReal ((1 - ε) / ε) * g (ENNReal.ofReal ((1 - r * ε) / (1 - ε))))
        (𝓝[>] 0) (𝓝 (g t)) := by
    have h_s : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ((1 - r * ε) / (1 - ε))) (𝓝[>] 0) (𝓝 1) := by
      have h_cont : ContinuousAt (fun ε : ℝ ↦ (1 - r * ε) / (1 - ε)) 0 :=
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
          (continuousAt_const.sub continuousAt_id) (by norm_num)
      simpa using ENNReal.tendsto_ofReal (h_cont.tendsto.mono_left nhdsWithin_le_nhds)
    -- the derivative of `g.realFun` at its minimum `1` is `0`
    have hg' : HasDerivAt g.realFun 0 1 := by
      simpa [((g.isMinOn_realFun_one univ).isLocalMin univ_mem).deriv_eq_zero] using hg.hasDerivAt
    have h := ENNReal.tendsto_ofReal (tendsto_div_mul_apply_div_nhdsGT_zero hg' g.realFun_one hr1)
    rw [ENNReal.ofReal_zero] at h
    have h' : Tendsto (fun ε ↦ ENNReal.ofReal ((1 - ε) / ε)
        * g (ENNReal.ofReal ((1 - r * ε) / (1 - ε)))) (𝓝[>] 0) (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [h_mem, h_s.eventually g.eventually_ne_top_nhds_one] with ε hε hε_fin
      have h1ε : 0 ≤ 1 - ε := by linarith [hε.2.trans_le (min_le_left _ _)]
      rw [ENNReal.ofReal_mul (div_nonneg h1ε hε.1.le), DivFunction.realFun,
        ENNReal.ofReal_toReal hε_fin]
    simpa using tendsto_const_nhds.add h'
  -- since `f ≥ 0`, the ratio is at least `f t / (g t + ...)`, which tends to `f t / g t`
  refine le_of_tendsto (ENNReal.Tendsto.div tendsto_const_nhds h_zero h_lim h_top) ?_
  filter_upwards [h_mem] with ε hε using (ENNReal.div_le_div_right le_self_add _).trans (h_le hε)

end ProbabilityTheory
