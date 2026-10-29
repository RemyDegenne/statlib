/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Prod
public import Statlib.Testing.BinaryRenyi
public import Statlib.Testing.Fano
public import Statlib.Testing.SampleComplexity

/-!
# Bounds on the sample complexity of simple binary hypothesis testing

Let `n(μ, ν, α, δ)` be the sample complexity of simple binary hypothesis testing between `μ` and
`ν` with prior `(α, 1 - α)` at risk level `δ` (`binaryPriorSampleComplexity`): the smallest `n` such
that the Bayes binary risk between the product measures `μ^⊗n` and `ν^⊗n` is at most `δ`. We prove
two lower bounds and an upper bound.

* From the binary Fano inequality and the subadditivity of the Jensen-Shannon divergence on
  products, `n(μ, ν, α, δ) ≥ (h₂(α) - h₂(δ)) / JS_α(μ, ν)` for `δ ≤ 1/2`, where `h₂` is the binary
  entropy.
* From the Rényi lower bound on the Bayes risk and the tensorization of the Rényi divergence,
  `n(μ, ν, α, δ) ≥ log (α / (2 δ)) / R_{1/2}(μ, ν)` for `α ≤ 1/2`.
* From the Rényi upper bound on the Bayes risk
  `B_α(μ^⊗n, ν^⊗n) ≤ α ^ a (1 - α) ^ (1 - a) exp (-n (1 - a) Rₐ(μ, ν))`, for every `a ∈ (0, 1)` and
  `δ ≠ 0`, `n(μ, ν, α, δ) ≤ (a log (α / δ) + (1 - a) log ((1 - α) / δ)) / ((1 - a) Rₐ(μ, ν)) + 1`.

Each bound is first proved for a fixed number of samples `n`: if the Bayes binary risk of `μ^⊗n`
and `ν^⊗n` is at most `δ` then `x ≤ n * D` (lower bounds), or conversely (upper bound). The bounds
on the sample complexity follow from `div_le_binaryPriorSampleComplexity_of_forall` and
`binaryPriorSampleComplexity_le_div_add_one_of_forall`.

## Main statements

* `ofReal_binEntropy_sub_binEntropy_le_mul_jensenShannon`,
  `ofReal_binEntropy_sub_binEntropy_div_jensenShannon_le_binaryPriorSampleComplexity`: the
  Jensen-Shannon lower bound.
* `ofReal_log_div_two_mul_le_mul_renyiDiv`,
  `ofReal_log_div_two_mul_div_renyiDiv_le_binaryPriorSampleComplexity`: the Rényi lower bound.
* `bayesBinaryRisk_pi_le_of_ofReal_le_mul_renyiDiv`,
  `binaryPriorSampleComplexity_le_ofReal_div_mul_renyiDiv_add_one`: the Rényi upper bound.
* `binaryPriorSampleComplexity_le_of_iInf_le`: `n(μ, ν, ρ, δ) ≤ n` if the infimum over `a ∈ (0, 1)`
  of the bounds `ρ({false}) ^ a ρ({true}) ^ (1 - a) exp (-n (1 - a) Rₐ(μ, ν))` on the Bayes binary
  risk is at most `δ`, for any prior `ρ`.

## Implementation notes

The sample complexity takes values in `ℕ∞` and is cast to `ℝ≥0∞`. The bounds are stated as
`x / D ≤ n(μ, ν, α, δ)` and `n(μ, ν, α, δ) ≤ x / D + 1` in `ℝ≥0∞`, which remain meaningful when the
divergence `D` is `0` or `∞`. The real numbers `x` may be negative and appear through
`ENNReal.ofReal`; the risk level `δ` appears in them through `ENNReal.toReal`.

## References

* A. Pensia, V. Jog, P.-L. Loh, *The sample complexity of simple binary hypothesis testing*, COLT
  2024.
-/

@[expose] public section

open MeasureTheory Real InformationTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {α : ℝ≥0} {a : ℝ} {δ : ℝ≥0∞} {n : ℕ}

/-! ### Lower bound from the Jensen-Shannon divergence -/

/-- **Jensen-Shannon lower bound on the number of samples**: if the Bayes binary risk between
`μ^⊗n` and `ν^⊗n` for the prior `(α, 1 - α)` is at most `δ ≤ 1/2`, then
`h₂(α) - h₂(δ) ≤ n JS_α(μ, ν)`. -/
theorem ofReal_binEntropy_sub_binEntropy_le_mul_jensenShannon (hα : α ≤ 1) (hδ : δ ≤ 2⁻¹)
    (h : bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν)
      (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) ≤ δ) :
    ENNReal.ofReal (binEntropy α - binEntropy δ.toReal) ≤ n * jensenShannon α μ ν := by
  have h_fano := ofReal_binEntropy_sub_binEntropy_bayesBinaryRisk_le_jensenShannon
    (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) hα
  have h_js := jensenShannon_pi_const_le hα (ι := Fin n) μ ν
  rw [Fintype.card_fin] at h_js
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h_fano.trans h_js)
  have hδ_top : δ ≠ ∞ := ne_top_of_le_ne_top (by simp) hδ
  have hδ_half : δ.toReal ≤ 2⁻¹ := by simpa using ENNReal.toReal_mono (by simp) hδ
  gcongr
  exact binEntropy_strictMonoOn.monotoneOn ⟨ENNReal.toReal_nonneg,
      (ENNReal.toReal_mono hδ_top h).trans hδ_half⟩
    ⟨ENNReal.toReal_nonneg, hδ_half⟩ (ENNReal.toReal_mono hδ_top h)

variable (μ ν) in
/-- **Jensen-Shannon lower bound on the sample complexity** of simple binary hypothesis testing:
for `δ ≤ 1/2`, `n(μ, ν, α, δ) ≥ (h₂(α) - h₂(δ)) / JS_α(μ, ν)`. -/
theorem ofReal_binEntropy_sub_binEntropy_div_jensenShannon_le_binaryPriorSampleComplexity
    (hα : α ≤ 1) (hδ : δ ≤ 2⁻¹) :
    ENNReal.ofReal (binEntropy α - binEntropy δ.toReal) / jensenShannon α μ ν
      ≤ binaryPriorSampleComplexity μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) δ :=
  div_le_binaryPriorSampleComplexity_of_forall fun _ h ↦
    ofReal_binEntropy_sub_binEntropy_le_mul_jensenShannon hα hδ h

/-! ### Lower bound from the Rényi divergence -/

/-- **Rényi lower bound on the number of samples**: for `α ≤ 1/2`, if the Bayes binary risk
between `μ^⊗n` and `ν^⊗n` for the prior `(α, 1 - α)` is at most `δ`, then
`log (α / (2 δ)) ≤ n R_{1/2}(μ, ν)`. -/
theorem ofReal_log_div_two_mul_le_mul_renyiDiv (hα : α ≤ 2⁻¹)
    (h : bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν)
      (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) ≤ δ) :
    ENNReal.ofReal (log (α / (2 * δ.toReal))) ≤ n * renyiDiv 2⁻¹ μ ν := by
  rcases eq_or_ne α 0 with rfl | hα0
  · simp
  have hα1 : α < 1 := hα.trans_lt (by norm_num)
  rw [← Fintype.card_fin n, ← renyiDiv_pi_const (by norm_num)]
  by_cases hδ_top : δ = ∞
  · simp [hδ_top]
  set B := bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν)
    (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) with hB
  rcases eq_or_ne B 0 with hB0 | hB0
  · -- the Bayes risk vanishes: the product measures are mutually singular
    have h_ms := (bayesBinaryRisk_eq_zero_iff_mutuallySingular (by simpa using hα0)
      (by simpa [tsub_eq_zero_iff_le, not_le] using hα1)).1 hB0
    rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).2 h_ms]
    exact le_top
  have hB_pos : 0 < B.toReal := ENNReal.toReal_pos hB0 (ne_top_of_le_ne_top hδ_top h)
  have hBδ : B.toReal ≤ δ.toReal := ENNReal.toReal_mono hδ_top h
  have hα0' : (0 : ℝ) < α := by exact_mod_cast pos_iff_ne_zero.2 hα0
  have h_renyi := ofReal_log_div_bayesBinaryRisk_le_renyiDiv_add
    (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) hα
  rw [← hB] at h_renyi
  calc ENNReal.ofReal (log (α / (2 * δ.toReal)))
  _ ≤ ENNReal.ofReal (log (α / B.toReal) - log 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hδ_pos : 0 < δ.toReal := hB_pos.trans_le hBδ
    rw [Real.log_div hα0'.ne' (by positivity), Real.log_mul two_ne_zero hδ_pos.ne',
      Real.log_div hα0'.ne' hB_pos.ne']
    linarith [Real.log_le_log hB_pos hBδ]
  _ = ENNReal.ofReal (log (α / B.toReal)) - ENNReal.ofReal (log 2) :=
    ENNReal.ofReal_sub _ (Real.log_nonneg one_le_two)
  _ ≤ _ := tsub_le_iff_right.2 h_renyi

variable (μ ν δ) in
/-- **Rényi lower bound on the sample complexity** of simple binary hypothesis testing: for
`α ≤ 1/2`, `n(μ, ν, α, δ) ≥ log (α / (2 δ)) / R_{1/2}(μ, ν)`. -/
theorem ofReal_log_div_two_mul_div_renyiDiv_le_binaryPriorSampleComplexity (hα : α ≤ 2⁻¹) :
    ENNReal.ofReal (log (α / (2 * δ.toReal))) / renyiDiv 2⁻¹ μ ν
      ≤ binaryPriorSampleComplexity μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) δ :=
  div_le_binaryPriorSampleComplexity_of_forall fun _ h ↦ ofReal_log_div_two_mul_le_mul_renyiDiv hα h

/-! ### Upper bound from the Rényi divergence -/

variable (μ ν) in
/-- For `a ∈ (0, 1)`, the Bayes binary risk between `μ^⊗n` and `ν^⊗n` is at most
`ρ({false}) ^ a * ρ({true}) ^ (1 - a) * exp (-(1 - a) * (n * Rₐ(μ, ν)))`. -/
theorem bayesBinaryRisk_pi_le_mul_exp_renyiDiv (ρ : Measure Bool) [IsFiniteMeasure ρ] (ha0 : 0 < a)
    (ha1 : a < 1) (n : ℕ) :
    bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) ρ
      ≤ ρ {false} ^ a * ρ {true} ^ (1 - a)
        * EReal.exp (-(((1 - a : ℝ) : EReal) * ((n * renyiDiv a μ ν : ℝ≥0∞) : EReal))) := by
  refine (bayesBinaryRisk_le_mul_exp_renyiDiv_of_isProbabilityMeasure _ _ ρ ha0 ha1).trans_eq ?_
  rw [renyiDiv_pi_const ha0.le, Fintype.card_fin]

/-- **Rényi upper bound on the number of samples**: for `a ∈ (0, 1)` and `δ ≠ 0`, if
`a log (α / δ) + (1 - a) log ((1 - α) / δ) ≤ n (1 - a) Rₐ(μ, ν)`, then the Bayes binary risk between
`μ^⊗n` and `ν^⊗n` for the prior `(α, 1 - α)` is at most `δ`. -/
theorem bayesBinaryRisk_pi_le_of_ofReal_le_mul_renyiDiv (ha0 : 0 < a) (ha1 : a < 1) (hδ : δ ≠ 0)
    (h : ENNReal.ofReal (a * log (α / δ.toReal) + (1 - a) * log ((1 - α) / δ.toReal))
      ≤ n * (ENNReal.ofReal (1 - a) * renyiDiv a μ ν)) :
    bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν)
      (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) ≤ δ := by
  refine (bayesBinaryRisk_pi_le_mul_exp_renyiDiv μ ν _ ha0 ha1 n).trans ?_
  rw [Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true]
  rcases eq_or_ne δ ∞ with rfl | hδ_top
  · exact le_top
  -- if the prior is a Dirac mass, the bound vanishes
  rcases eq_or_ne α 0 with rfl | hα0
  · simp [ENNReal.zero_rpow_of_pos ha0]
  rcases le_or_gt 1 α with hα1 | hα1
  · simp [tsub_eq_zero_of_le hα1, ENNReal.zero_rpow_of_pos (sub_pos.2 ha1)]
  -- if `n Rₐ(μ, ν) = ∞`, the bound vanishes
  set D := (n : ℝ≥0∞) * renyiDiv a μ ν with hD
  rcases eq_or_ne D ∞ with hD_top | hD_top
  · rw [hD_top, EReal.coe_ennreal_top, EReal.mul_top_of_pos (by exact_mod_cast sub_pos.2 ha1),
      EReal.neg_top, EReal.exp_bot, mul_zero]
    exact zero_le
  -- otherwise, write the bound as `ENNReal.ofReal` of a real number and compare the logarithms
  have hδ_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ hδ_top
  have hα0' : (0 : ℝ) < α := by exact_mod_cast pos_iff_ne_zero.2 hα0
  have hα1' : (0 : ℝ) < 1 - α := sub_pos.2 (by exact_mod_cast hα1)
  have h_exp : EReal.exp (-(((1 - a : ℝ) : EReal) * (D : EReal)))
      = ENNReal.ofReal (exp (-((1 - a) * D.toReal))) := by
    rw [← EReal.coe_ennreal_toReal hD_top, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
  have h_α : ((α : ℝ≥0∞)) ^ a = ENNReal.ofReal ((α : ℝ) ^ a) := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg α.coe_nonneg ha0.le]
  have h_α' : (((1 - α : ℝ≥0) : ℝ≥0∞)) ^ (1 - a) = ENNReal.ofReal ((1 - (α : ℝ)) ^ (1 - a)) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub hα1.le, NNReal.coe_one,
      ENNReal.ofReal_rpow_of_nonneg hα1'.le (by linarith)]
  rw [h_exp, h_α, h_α', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_iff_le_toReal hδ_top]
  have h_eq : (α : ℝ) ^ a * (1 - (α : ℝ)) ^ (1 - a) * exp (-((1 - a) * D.toReal))
      = exp (a * log α + (1 - a) * log (1 - α) - (1 - a) * D.toReal) := by
    rw [rpow_def_of_pos hα0', rpow_def_of_pos hα1', ← exp_add, ← exp_add]
    ring_nf
  rw [h_eq, ← exp_log hδ_pos, exp_le_exp]
  rw [mul_left_comm, ← hD, ← ENNReal.ofReal_toReal hD_top, ← ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) ENNReal.toReal_nonneg),
    Real.log_div hα0'.ne' hδ_pos.ne', Real.log_div hα1'.ne' hδ_pos.ne'] at h
  linarith

variable (μ ν α) in
/-- **Rényi upper bound on the sample complexity** of simple binary hypothesis testing: for
`a ∈ (0, 1)` and `δ ≠ 0`,
`n(μ, ν, α, δ) ≤ (a log (α / δ) + (1 - a) log ((1 - α) / δ)) / ((1 - a) Rₐ(μ, ν)) + 1`. -/
theorem binaryPriorSampleComplexity_le_ofReal_div_mul_renyiDiv_add_one (ha0 : 0 < a) (ha1 : a < 1)
    (hδ : δ ≠ 0) :
    binaryPriorSampleComplexity μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞)) δ
      ≤ ENNReal.ofReal (a * log (α / δ.toReal) + (1 - a) * log ((1 - α) / δ.toReal))
        / (ENNReal.ofReal (1 - a) * renyiDiv a μ ν) + 1 :=
  binaryPriorSampleComplexity_le_div_add_one_of_forall fun _ h ↦
    bayesBinaryRisk_pi_le_of_ofReal_le_mul_renyiDiv ha0 ha1 hδ h

/-- If the infimum over `a ∈ (0, 1)` of
`ρ({false}) ^ a * ρ({true}) ^ (1 - a) * exp (-(1 - a) * (n * Rₐ(μ, ν)))` is at most `δ`, then the
sample complexity of simple binary hypothesis testing with prior `ρ` is at most `n`. -/
theorem binaryPriorSampleComplexity_le_of_iInf_le (ρ : Measure Bool) [IsFiniteMeasure ρ]
    (h : ⨅ a ∈ Set.Ioo (0 : ℝ) 1, ρ {false} ^ a * ρ {true} ^ (1 - a)
        * EReal.exp (-(((1 - a : ℝ) : EReal) * ((n * renyiDiv a μ ν : ℝ≥0∞) : EReal))) ≤ δ) :
    binaryPriorSampleComplexity μ ν ρ δ ≤ n :=
  binaryPriorSampleComplexity_le
    ((le_iInf₂ fun _ ha ↦ bayesBinaryRisk_pi_le_mul_exp_renyiDiv μ ν ρ ha.1 ha.2 n).trans h)

end ProbabilityTheory
