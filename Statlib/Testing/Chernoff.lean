/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Chernoff.Prod
public import Statlib.ForMathlib.Probability.StrongLaw
public import Statlib.Testing.ChangeMeasure
public import Statlib.Testing.RenyiChangeMeasure
public import Statlib.Testing.Sequential.Basic

/-!
# Testing lower bounds from the Chernoff divergence

The Chernoff divergence gives lower bounds on the errors of tests, both for a fixed number of
samples and asymptotically.

For probability measures `μ`, `ν` and `a > 0`, a test between `μ` and `ν`, that is an event `s`,
satisfies `μ(s) + ν(sᶜ) ≥ 2⁻¹ * exp (- C_{1+a}(μ, ν) - log 4 / a)`, where `C_b` is the Chernoff
divergence of order `b`. This follows from the change of measure inequality with three measures
`exp_neg_max_renyiDiv_le_add_measureReal`, optimized over the intermediate measure.
For a test with `n` samples, that is an event `s` on `𝓧^n`, applying that bound to the product
measures at order `1 + a / √n` and using the subadditivity of the Chernoff divergence on powers
gives `μ^⊗n(s) + ν^⊗n(sᶜ) ≥ 2⁻¹ * exp (-n C_{1 + a/√n}(μ, ν) - log 4 / a * √n)`.

Let `μ^ℕ = Measure.infinitePi (fun _ : ℕ ↦ μ)`. For events `E m` that depend only on the first
`m + 1` observations (they are measurable with respect to `Filtration.piLE m`), the errors
`μ^ℕ (E m)` and `ν^ℕ (E m)ᶜ` of the corresponding tests cannot both decrease exponentially faster
than `exp (-(m + 1) C₁(μ, ν))`:
`limsup (m + 1)⁻¹ * log (1 / (γ * μ^ℕ (E m) + (1 - γ) * ν^ℕ (E m)ᶜ)) ≤ C₁(μ, ν)`.
The proof uses a change of measure to `ξ^ℕ` for a probability measure `ξ` and the law of large
numbers for the log-likelihood ratios `llr ξ μ (ω i)` and `llr ξ ν (ω i)` under `ξ^ℕ`
(`tendsto_measureReal_lt_sum_comp_eval`).

## Main statements

* `exp_neg_chernoffDiv_le_add_measureReal`:
  `2⁻¹ * exp (- C_{1+a}(μ, ν) - log 4 / a) ≤ μ(s) + ν(sᶜ)`.
* `exp_neg_mul_chernoffDiv_le_add_measureReal_pi`: the bound for `n` samples, for a finite index
  type `ι` in place of `Fin n` (so that `n = |ι|`).
* `measureReal_sub_le_measureReal_mul_exp_piLE`: change of measure for events determined by the
  first `m + 1` observations.
* `eventually_exp_neg_mul_le_add_measureReal`: **the Chernoff divergence bounds the error exponent
  of tests**. For every `c > C₁(μ, ν)`, eventually
  `exp (-(m + 1) * c) ≤ γ * μ^ℕ (E m) + (1 - γ) * ν^ℕ (E m)ᶜ`.

## References

* H. Chernoff, *A measure of asymptotic efficiency for tests of a hypothesis based on the sum of
  observations*, Annals of Mathematical Statistics 23(4) (1952).
-/

@[expose] public section

open MeasureTheory Filtration InformationTheory Filter Real

open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### Tests with a fixed number of samples -/

section FixedSamples

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- Lower bound on the sum of the errors `μ s + ν sᶜ` of a test between two probability measures
in terms of their Chernoff divergence of order `1 + a`:
`2⁻¹ * exp (- C_{1+a}(μ, ν) - log 4 / a) ≤ μ s + ν sᶜ`. -/
lemma exp_neg_chernoffDiv_le_add_measureReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set α) (ha : 0 < a) (h : chernoffDiv (1 + a) μ ν ≠ ∞) :
    2⁻¹ * exp (-(chernoffDiv (1 + a) μ ν).toReal - log 4 / a) ≤ μ.real s + ν.real sᶜ := by
  -- the bound holds for every `x > C_{1+a}(μ, ν)` in place of `C_{1+a}(μ, ν)`, by
  -- `exp_neg_max_renyiDiv_le_add_measureReal` for a measure `ξ` almost attaining the infimum
  have h_gt (x : ℝ) (hx : (chernoffDiv (1 + a) μ ν).toReal < x) :
      2⁻¹ * exp (-x - log 4 / a) ≤ μ.real s + ν.real sᶜ := by
    obtain ⟨ξ, hξ, h_lt⟩ : ∃ ξ : Measure α, ∃ _ : IsProbabilityMeasure ξ,
        max (renyiDiv (1 + a) ξ μ) (renyiDiv (1 + a) ξ ν) < ENNReal.ofReal x := by
      simpa only [chernoffDiv, iInf_lt_iff] using (ENNReal.lt_ofReal_iff_toReal_lt h).mpr hx
    rw [max_lt_iff] at h_lt
    refine le_trans ?_ (exp_neg_max_renyiDiv_le_add_measureReal s ha h_lt.1.ne_top h_lt.2.ne_top)
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg.trans hx.le
    gcongr
    exact max_le (ENNReal.toReal_le_of_le_ofReal hx0 h_lt.1.le)
      (ENNReal.toReal_le_of_le_ofReal hx0 h_lt.2.le)
  exact le_of_tendsto (f := fun x ↦ 2⁻¹ * exp (-x - log 4 / a))
    (x := 𝓝[>] (chernoffDiv (1 + a) μ ν).toReal)
    (Continuous.continuousWithinAt (by fun_prop)).tendsto (eventually_nhdsWithin_of_forall h_gt)

/-- Lower bound on the sum of the errors of a test between powers of probability measures in terms
of the Chernoff divergence of order `1 + a / √n`, where `n = |ι|`:
`2⁻¹ * exp (-n C_{1 + a/√n}(μ, ν) - log 4 / a * √n) ≤ μ^⊗ι(s) + ν^⊗ι(sᶜ)`. -/
theorem exp_neg_mul_chernoffDiv_le_add_measureReal_pi [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ι : Type*} [Fintype ι] (s : Set (ι → α)) (ha : 0 < a)
    (h : chernoffDiv (1 + a / √(Fintype.card ι)) μ ν ≠ ∞) :
    2⁻¹ * exp (-(Fintype.card ι * (chernoffDiv (1 + a / √(Fintype.card ι)) μ ν).toReal)
        - log 4 / a * √(Fintype.card ι))
      ≤ (Measure.pi fun _ : ι ↦ μ).real s + (Measure.pi fun _ : ι ↦ ν).real sᶜ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- for `n = 0`, the left-hand side is `2⁻¹` and the right-hand side is at least `1`
    have h_eq : (Measure.pi fun _ : ι ↦ ν) = Measure.pi fun _ : ι ↦ μ := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    have h_one : 1 ≤ (Measure.pi fun _ : ι ↦ μ).real s + (Measure.pi fun _ : ι ↦ μ).real sᶜ := by
      rw [← ENNReal.toReal_one, ← measure_univ (μ := Measure.pi fun _ : ι ↦ μ), measureReal_def,
        measureReal_def, ← ENNReal.toReal_add (by finiteness) (by finiteness)]
      exact ENNReal.toReal_mono (by finiteness) (measure_univ_le_add_compl s)
    simp only [Fintype.card_eq_zero, Nat.cast_zero, sqrt_zero, zero_mul, neg_zero, mul_zero,
      sub_zero, exp_zero, mul_one, h_eq]
    linarith
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set b := a / √n with hb_def
  have hb : 0 < b := div_pos ha (sqrt_pos.2 hn)
  have hC := chernoffDiv_pi_const_le (a := 1 + b) (by linarith) (ι := ι) (μ := μ) (ν := ν)
  have hC_ne : chernoffDiv (1 + b) (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : ι ↦ ν) ≠ ∞ :=
    (hC.trans_lt (ENNReal.mul_lt_top (by simp) h.lt_top)).ne
  refine le_trans ?_ (exp_neg_chernoffDiv_le_add_measureReal s hb hC_ne)
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)
  have h1 : (chernoffDiv (1 + b) (Measure.pi fun _ : ι ↦ μ)
      (Measure.pi fun _ : ι ↦ ν)).toReal ≤ n * (chernoffDiv (1 + b) μ ν).toReal := by
    simpa [ENNReal.toReal_mul, hn_def] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) h) hC
  have h2 : log 4 / b = log 4 / a * √n := by
    rw [hb_def, div_div_eq_mul_div, div_mul_eq_mul_div]
  linarith

end FixedSamples

/-! ### Error exponent -/

section ErrorExponent

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν ξ : Measure 𝓧}

section ChangeMeasure

/-- **Change of measure** for events determined by the first `m + 1` observations:
`ξ^ℕ E - ξ^ℕ {t < ∑ i ≤ m, llr ξ μ (ω i)} ≤ μ^ℕ E * exp t`. -/
lemma measureReal_sub_le_measureReal_mul_exp_piLE [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure μ] (hξμ : ξ ≪ μ) (m : ℕ) {E : Set (ℕ → 𝓧)}
    (hE : MeasurableSet[piLE (X := fun _ : ℕ ↦ 𝓧) m] E) (t : ℝ) :
    (Measure.infinitePi fun _ : ℕ ↦ ξ).real E
        - (Measure.infinitePi fun _ : ℕ ↦ ξ).real
          {ω | t < ∑ i ∈ Finset.Iic m, llr ξ μ (ω i)}
      ≤ (Measure.infinitePi fun _ : ℕ ↦ μ).real E * exp t := by
  set hm := (piLE (X := fun _ : ℕ ↦ 𝓧)).le m
  set P := Measure.infinitePi fun _ : ℕ ↦ ξ
  set Q := Measure.infinitePi fun _ : ℕ ↦ μ
  have h := @measureReal_sub_le_measureReal_mul_exp _ (piLE (X := fun _ : ℕ ↦ 𝓧) m) (P.trim hm)
    (Q.trim hm) _ _ (absolutelyContinuous_trim_piLE_infinitePi hξμ m) E t (measure_ne_top _ _)
  have h_set : MeasurableSet[piLE (X := fun _ : ℕ ↦ 𝓧) m] {ω | t < llr (P.trim hm) (Q.trim hm) ω} :=
    measurableSet_lt measurable_const (@measurable_llr _ (piLE (X := fun _ : ℕ ↦ 𝓧) m) _ _)
  have h_eq : (P.trim hm) {ω | t < llr (P.trim hm) (Q.trim hm) ω}
      = P {ω | t < ∑ i ∈ Finset.Iic m, llr ξ μ (ω i)} := by
    rw [trim_measurableSet_eq hm h_set]
    refine measure_congr ?_
    filter_upwards [llr_trim_piLE_infinitePi_ae_eq hξμ m] with ω hω
    rw [hω]
  simp only [measureReal_def] at h ⊢
  rwa [trim_measurableSet_eq hm hE, trim_measurableSet_eq hm hE, h_eq] at h

end ChangeMeasure

/-- **The Chernoff divergence bounds the error exponent of tests**. Let `μ, ν` be probability
measures, `γ ∈ (0, 1)` and let `E m` be events determined by the first `m + 1` observations. For
every `c > C₁(μ, ν)`, eventually `exp (-(m + 1) * c) ≤ γ * μ^ℕ (E m) + (1 - γ) * ν^ℕ (E m)ᶜ`. That
is, `limsup (m + 1)⁻¹ * log (1 / (γ * μ^ℕ (E m) + (1 - γ) * ν^ℕ (E m)ᶜ)) ≤ C₁(μ, ν)`. -/
theorem eventually_exp_neg_mul_le_add_measureReal [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {E : ℕ → Set (ℕ → 𝓧)}
    (hE : ∀ m, MeasurableSet[piLE (X := fun _ : ℕ ↦ 𝓧) m] (E m)) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) {c : ℝ} (hc : chernoffDiv 1 μ ν < ENNReal.ofReal c) :
    ∀ᶠ m : ℕ in atTop, exp (-(m + 1) * c)
      ≤ γ * (Measure.infinitePi fun _ : ℕ ↦ μ).real (E m)
        + (1 - γ) * (Measure.infinitePi fun _ : ℕ ↦ ν).real (E m)ᶜ := by
  -- choose `ξ` with `max (KL(ξ, μ)) (KL(ξ, ν)) < c`
  rw [chernoffDiv_one] at hc
  obtain ⟨ξ, hc⟩ := iInf_lt_iff.mp hc
  obtain ⟨hξ, hc⟩ := iInf_lt_iff.mp hc
  have hμ_top : klDiv ξ μ ≠ ∞ := (hc.trans_le' (le_max_left _ _)).ne_top
  have hν_top : klDiv ξ ν ≠ ∞ := (hc.trans_le' (le_max_right _ _)).ne_top
  obtain ⟨hξμ, h_int_μ⟩ := klDiv_ne_top_iff.mp hμ_top
  obtain ⟨hξν, h_int_ν⟩ := klDiv_ne_top_iff.mp hν_top
  have hM : max (klDiv ξ μ).toReal (klDiv ξ ν).toReal < c := by
    have hc_pos : 0 < c := ENNReal.ofReal_pos.mp (zero_le.trans_lt hc)
    rw [← ENNReal.toReal_max hμ_top hν_top]
    exact (ENNReal.toReal_lt_toReal (max_ne_top hμ_top hν_top) ENNReal.ofReal_ne_top).mpr hc
      |>.trans_eq (ENNReal.toReal_ofReal hc_pos.le)
  set K₁ := (klDiv ξ μ).toReal
  set K₂ := (klDiv ξ ν).toReal
  set M := max K₁ K₂
  set β := (c - M) / 2
  have hβ : 0 < β := by simp only [β]; linarith
  set P := Measure.infinitePi fun _ : ℕ ↦ ξ
  set δ := min γ (1 - γ)
  have hδ : 0 < δ := lt_min hγ0 (by linarith)
  -- the deviation probabilities of the log-likelihood ratios tend to `0`
  have h_dev₁ := tendsto_measureReal_lt_sum_comp_eval h_int_μ hβ
  have h_dev₂ := tendsto_measureReal_lt_sum_comp_eval h_int_ν hβ
  rw [← toReal_klDiv_of_measure_eq hξμ (by simp)] at h_dev₁
  rw [← toReal_klDiv_of_measure_eq hξν (by simp)] at h_dev₂
  have h_dev := h_dev₁.add h_dev₂
  rw [add_zero] at h_dev
  -- the factor `exp (-(m + 1) * β)` tends to `0`
  have h_exp : Tendsto (fun m : ℕ ↦ exp (-(m + 1) * β)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    refine Tendsto.atBot_mul_const hβ ?_
    exact tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  filter_upwards [h_dev.eventually (gt_mem_nhds (half_pos hδ)),
    h_exp.eventually (gt_mem_nhds (half_pos hδ))] with m h_small h_exp_small
  set p := P.real {ω | (m + 1) * (K₁ + β) < ∑ i ∈ Finset.Iic m, llr ξ μ (ω i)}
  set q := P.real {ω | (m + 1) * (K₂ + β) < ∑ i ∈ Finset.Iic m, llr ξ ν (ω i)}
  set C := (m + 1) * (M + β)
  -- change of measure from `ξ^ℕ` to `μ^ℕ` and to `ν^ℕ`
  have h1 : P.real (E m) - p ≤ (Measure.infinitePi fun _ : ℕ ↦ μ).real (E m) * exp C :=
    (measureReal_sub_le_measureReal_mul_exp_piLE hξμ m (hE m) _).trans
      (by gcongr; simp only [C]; gcongr; exact le_max_left _ _)
  have h2 : P.real (E m)ᶜ - q ≤ (Measure.infinitePi fun _ : ℕ ↦ ν).real (E m)ᶜ * exp C :=
    (measureReal_sub_le_measureReal_mul_exp_piLE hξν m (hE m).compl _).trans
      (by gcongr; simp only [C]; gcongr; exact le_max_right _ _)
  have h_compl : P.real (E m) + P.real (E m)ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl ((piLE (X := fun _ : ℕ ↦ 𝓧)).le m _ (hE m)),
      probReal_univ]
  -- combine the two changes of measure
  have h_main : δ / 2 ≤ (γ * (Measure.infinitePi fun _ : ℕ ↦ μ).real (E m)
      + (1 - γ) * (Measure.infinitePi fun _ : ℕ ↦ ν).real (E m)ᶜ) * exp C := by
    have hp : 0 ≤ p := measureReal_nonneg
    have hq : 0 ≤ q := measureReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ0.le,
      mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hγ1.le),
      mul_nonneg (sub_nonneg.mpr (min_le_left γ (1 - γ))) (measureReal_nonneg (μ := P) (s := E m)),
      mul_nonneg (sub_nonneg.mpr (min_le_right γ (1 - γ)))
        (measureReal_nonneg (μ := P) (s := (E m)ᶜ))]
  -- `exp (-(m + 1) * c) = exp (-C) * exp (-(m + 1) * β)`
  have h_split : exp (-(m + 1) * c) = exp (-C) * exp (-(m + 1) * β) := by
    rw [← exp_add]
    congr 1
    simp only [C, β]
    ring
  calc exp (-(m + 1) * c) ≤ exp (-C) * (δ / 2) := by rw [h_split]; gcongr
  _ ≤ exp (-C) * ((γ * (Measure.infinitePi fun _ : ℕ ↦ μ).real (E m)
      + (1 - γ) * (Measure.infinitePi fun _ : ℕ ↦ ν).real (E m)ᶜ) * exp C) := by gcongr
  _ = _ := by rw [mul_comm, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]

end ErrorExponent

end ProbabilityTheory
