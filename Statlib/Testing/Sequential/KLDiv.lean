/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Statlib.Testing.Sequential.Basic
public import Statlib.Testing.Sequential.Wald

/-!
# Kullback-Leibler divergence of i.i.d. sequences observed up to a stopping time

Let `μ^ℕ = Measure.infinitePi (fun _ : ℕ ↦ μ)` and let `τ` be a stopping time for the filtration
`Filtration.piLE` of the first coordinates, with values in `ℕ`. The observations available at time
`τ` are `ω 0, …, ω (τ ω)`, and `μ_τ` is the restriction of `μ^ℕ` to the σ-algebra of the
stopping time.

## Main statements

* `klDiv_trim_stoppingTime`: `KL(μ_τ, ν_τ) = μ^ℕ[τ + 1] * KL(μ, ν)`, with the expectation computed
  in `ℝ≥0∞` (both sides may be infinite).

Note that with the filtration `Filtration.piLE`, the number of observations at time `τ` is
`τ + 1`.
-/
@[expose] public section

open MeasureTheory Filtration InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {τ : (ℕ → 𝓧) → ℕ}

/-- The first observation `ω 0` is available at any stopping time `τ`, hence
`KL(μ, ν) ≤ KL(μ_τ, ν_τ)`. -/
lemma klDiv_le_klDiv_trim_stoppingTime (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ))) :
    klDiv μ ν ≤ klDiv ((Measure.infinitePi fun _ : ℕ ↦ μ).trim hτ.measurableSpace_le)
      ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hτ.measurableSpace_le) := by
  set hm := hτ.measurableSpace_le
  -- `ω 0` is measurable at time `0`, hence with respect to the σ-algebra of `τ`
  have h_meas : Measurable[hτ.measurableSpace] fun ω : ℕ → 𝓧 ↦ ω 0 := by
    have h_le := (isStoppingTime_const (piLE (X := fun _ : ℕ ↦ 𝓧)) 0).measurableSpace_mono hτ
      fun ω ↦ by simp
    rw [IsStoppingTime.measurableSpace_const] at h_le
    exact (measurable_piLE_apply le_rfl).mono h_le le_rfl
  -- the law of `ω 0` under the restriction of `ρ^ℕ` to the σ-algebra of `τ` is `ρ`
  have h_map (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] :
      @Measure.map _ _ hτ.measurableSpace _ (fun ω ↦ ω 0)
        ((Measure.infinitePi fun _ : ℕ ↦ ρ).trim hm) = ρ := by
    ext s hs
    rw [@Measure.map_apply _ _ hτ.measurableSpace _ _ _ h_meas _ hs,
      trim_measurableSet_eq _ (h_meas hs), ← Measure.map_apply (measurable_pi_apply 0) hs,
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ ρ) 0).map_eq]
  calc klDiv μ ν
  _ = klDiv (@Measure.map _ _ hτ.measurableSpace _ (fun ω ↦ ω 0)
        ((Measure.infinitePi fun _ : ℕ ↦ μ).trim hm))
      (@Measure.map _ _ hτ.measurableSpace _ (fun ω ↦ ω 0)
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hm)) := by
    rw [h_map, h_map]
  _ ≤ _ := klDiv_map_le _ _ h_meas

/-- `KL(μ_τ, ν_τ) = μ^ℕ[τ + 1] * KL(μ, ν)` for an integrable stopping time `τ`. -/
private lemma klDiv_trim_stoppingTime_of_integrable [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω ↦ (τ ω : ℝ)) (Measure.infinitePi fun _ ↦ μ)) :
    klDiv ((Measure.infinitePi fun _ : ℕ ↦ μ).trim hτ.measurableSpace_le)
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hτ.measurableSpace_le)
      = (∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂(Measure.infinitePi fun _ : ℕ ↦ μ)) * klDiv μ ν := by
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  set Q := Measure.infinitePi fun _ : ℕ ↦ ν
  set hm := hτ.measurableSpace_le
  by_cases h_top : klDiv μ ν = ∞
  · -- both sides are infinite
    have h_ne : ∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂P ≠ 0 :=
      (lt_of_lt_of_le (by simp) (lintegral_mono fun ω ↦ le_add_self)).ne'
    rw [h_top, ENNReal.mul_top h_ne, ← top_le_iff, ← h_top]
    exact klDiv_le_klDiv_trim_stoppingTime μ ν hτ
  obtain ⟨hμν, h_int⟩ := klDiv_ne_top_iff.mp h_top
  have h_llr := llr_trim_stoppingTime_infinitePi_ae_eq hμν hτ
  have h_meas : StronglyMeasurable[hτ.measurableSpace] (llr (P.trim hm) (Q.trim hm)) :=
    (@measurable_llr _ hτ.measurableSpace _ _).stronglyMeasurable
  have h_int_trim : Integrable (llr (P.trim hm) (Q.trim hm)) (P.trim hm) :=
    ((integrable_sum_comp_stoppingTime h_int hτ hτ_int).congr h_llr.symm).trim hm h_meas
  rw [klDiv_of_ac_of_integrable (absolutelyContinuous_trim_stoppingTime_infinitePi hμν hτ)
      h_int_trim, klDiv_of_ac_of_integrable hμν h_int, ← integral_trim hm h_meas,
    integral_congr_ae h_llr, integral_sum_comp_stoppingTime h_int hτ hτ_int]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [ENNReal.ofReal_mul (integral_nonneg fun ω ↦ by positivity),
    ofReal_integral_natCast_add_one_eq_lintegral hτ_int]

/-- **Kullback-Leibler divergence at a stopping time**: for a stopping time `τ` with values in `ℕ`,
`KL(μ_τ, ν_τ) = μ^ℕ[τ + 1] * KL(μ, ν)`, where `μ_τ` and `ν_τ` are the restrictions of `μ^ℕ` and
`ν^ℕ` to the σ-algebra of `τ` and `τ + 1` is the number of observations. The expectation
`μ^ℕ[τ + 1]` is a Lebesgue integral, which is infinite if `τ` is not integrable. -/
theorem klDiv_trim_stoppingTime [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ))) :
    klDiv ((Measure.infinitePi fun _ : ℕ ↦ μ).trim hτ.measurableSpace_le)
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hτ.measurableSpace_le)
      = (∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂(Measure.infinitePi fun _ : ℕ ↦ μ)) * klDiv μ ν := by
  by_cases h0 : klDiv μ ν = 0
  · obtain rfl := klDiv_eq_zero_iff.mp h0
    rw [klDiv_self, klDiv_self, mul_zero]
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  by_cases hτ_int : Integrable (fun ω ↦ (τ ω : ℝ)) P
  · exact klDiv_trim_stoppingTime_of_integrable hτ hτ_int
  -- if `τ` is not integrable, then `μ^ℕ[τ + 1] = ∞`
  have hτ_meas := measurable_of_isStoppingTime (τ := τ) hτ
  have h_top : ∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂P = ∞ := by
    refine eq_top_mono (lintegral_mono fun ω ↦ le_self_add) ?_
    by_contra h
    exact hτ_int (by simpa using (integrable_toReal_iff (f := fun ω ↦ (τ ω : ℝ≥0∞))
      (by fun_prop) (ae_of_all _ fun _ ↦ by simp)).mpr h)
  -- the stopping times `min τ n` are bounded, hence integrable
  have h_le (n : ℕ) : (∫⁻ ω, ((min (τ ω) n : ℕ) + 1 : ℝ≥0∞) ∂P) * klDiv μ ν
      ≤ klDiv (P.trim hτ.measurableSpace_le)
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hτ.measurableSpace_le) := by
    have hτn : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧))
        (fun ω ↦ ((min (τ ω) n : ℕ) : WithTop ℕ)) := by
      convert hτ.min_const n using 2
    have hτn_int : Integrable (fun ω ↦ ((min (τ ω) n : ℕ) : ℝ)) P :=
      (integrable_const (n : ℝ)).mono' (by fun_prop)
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact_mod_cast min_le_right _ _)
    rw [← klDiv_trim_stoppingTime_of_integrable hτn hτn_int]
    exact klDiv_trim_mono _ _ (hτn.measurableSpace_mono hτ fun ω ↦ by simp) hτ.measurableSpace_le
  -- monotone convergence
  have h_sup : ⨆ n : ℕ, ∫⁻ ω, ((min (τ ω) n : ℕ) + 1 : ℝ≥0∞) ∂P = ∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂P := by
    rw [← lintegral_iSup (fun n ↦ by fun_prop) fun n m hnm ω ↦ by gcongr]
    congr with ω
    rw [← ENNReal.iSup_add]
    congr 1
    exact le_antisymm (iSup_le fun n ↦ by simp) (le_iSup_of_le (τ ω) (by simp))
  refine le_antisymm ?_ ?_
  · rw [h_top, ENNReal.top_mul h0]
    exact le_top
  · rw [← h_sup, ENNReal.iSup_mul]
    exact iSup_le h_le

end ProbabilityTheory
