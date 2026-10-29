/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ConditionalProbability
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Kullback-Leibler divergence of rescaled and restricted measures

## Main statements

* `klDiv_smul_left_eq_top_iff`, `klDiv_smul_right_eq_top_iff`: for `c ∉ {0, ∞}`, rescaling one of
  the measures by `c` does not change whether the divergence is infinite.
* `klDiv_smul_left_eq_ofReal`: formula for `klDiv (c • μ) ν` in terms of `klDiv μ ν`.
* `klDiv_smul_right_eq_smul_left'`, `klDiv_smul_same'`: versions of Mathlib's
  `klDiv_smul_right_eq_smul_left` and `klDiv_smul_same` for `c : ℝ≥0∞`.
* `klDiv_smul_smul_eq_add`: for probability measures `μ`, `ν` and `ρ`,
  `KL(a • μ, c • ν) = KL(a • ρ, c • ρ) + a * KL(μ, ν)`.
* `klDiv_inv_smul_le_of_le`: an inequality between Kullback-Leibler divergences of measures with
  the same masses also holds for the normalized measures.
* `mul_log_le_setIntegral_llr`: for an event `s`,
  `μ(s) log (μ(s) / ν(s)) ≤ ∫ x in s, llr μ ν x ∂μ`.
* `klDiv_restrict_eq_add`: `KL(μ|s, ν|s) = KL(μ(s) • ρ, ν(s) • ρ) + μ(s) KL(μ[|s], ν[|s])`, in
  which `μ[|s]` is the measure `μ` conditioned on `s`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory

open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma klDiv_smul_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv (c • μ) ν = ∞ ↔ klDiv μ ν = ∞ := by
  rw [klDiv_eq_top_iff, klDiv_eq_top_iff]
  have h_ac : c • μ ≪ ν ↔ μ ≪ ν :=
    ⟨fun h ↦ (Measure.absolutelyContinuous_smul hc).trans h, fun h ↦ h.smul_left c⟩
  rw [h_ac]
  refine imp_congr_right fun hμν ↦ not_congr ?_
  rw [integrable_smul_measure hc hc_top, integrable_congr (llr_smul_left hμν c hc hc_top),
    integrable_add_iff_integrable_left' (integrable_const _)]

lemma klDiv_smul_left_eq_ofReal [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : klDiv μ ν ≠ ∞)
    {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ) ν = ENNReal.ofReal (c.toReal * (klDiv μ ν).toReal
      + (1 - c.toReal) * (ν .univ).toReal + c.toReal * log c.toReal * (μ .univ).toReal) := by
  by_cases hc : c = 0
  · simp [hc, klDiv_zero_left]
  have h' : klDiv (c • μ) ν ≠ ∞ := by rwa [ne_eq, klDiv_smul_left_eq_top_iff hc hc_top]
  rw [klDiv_ne_top_iff] at h
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def] at h' ⊢
  rw [← ENNReal.ofReal_toReal h', toReal_klDiv_smul_left h.1 h.2 c, ENNReal.coe_toReal,
    measureReal_def, measureReal_def]

lemma klDiv_smul_right_eq_smul_left' [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν := by
  lift c to ℝ≥0 using hc_top
  have hc' : c ≠ 0 := by simpa using hc
  rw [← ENNReal.smul_def, ← ENNReal.coe_inv hc', ← ENNReal.smul_def]
  exact klDiv_smul_right_eq_smul_left hc'

lemma klDiv_smul_right_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv μ (c • ν) = ∞ ↔ klDiv μ ν = ∞ := by
  rw [klDiv_smul_right_eq_smul_left' hc hc_top, ENNReal.mul_eq_top,
    klDiv_smul_left_eq_top_iff (ENNReal.inv_ne_zero.mpr hc_top) (ENNReal.inv_ne_top.mpr hc)]
  simp [hc, hc_top]

lemma klDiv_smul_same' [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ) (c • ν) = c * klDiv μ ν := by
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def, ← ENNReal.smul_def]
  exact klDiv_smul_same c

/-- The Kullback-Leibler divergence between rescaled probability measures:
`KL(a • μ, c • ν) = KL(a • ρ, c • ρ) + a * KL(μ, ν)` for any probability measure `ρ`. The first
term depends only on `a` and `c`. -/
lemma klDiv_smul_smul_eq_add {β : Type*} {mβ : MeasurableSpace β} (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ρ : Measure β) [IsProbabilityMeasure ρ]
    {a c : ℝ≥0∞} (ha : a ≠ ∞) (hc : c ≠ ∞) :
    klDiv (a • μ) (c • ν) = klDiv (a • ρ) (c • ρ) + a * klDiv μ ν := by
  have := μ.smul_finite ha
  have := ν.smul_finite hc
  have := ρ.smul_finite ha
  have := ρ.smul_finite hc
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [klDiv_zero_left]
  rcases eq_or_ne c 0 with rfl | hc0
  · have : NeZero (a • μ) := ⟨by simp [ha0, IsProbabilityMeasure.ne_zero]⟩
    have : NeZero (a • ρ) := ⟨by simp [ha0, IsProbabilityMeasure.ne_zero]⟩
    simp [klDiv_zero_right]
  rw [klDiv_smul_right_eq_smul_left' hc0 hc, klDiv_smul_right_eq_smul_left' hc0 hc, smul_smul,
    smul_smul]
  set k := c⁻¹ * a with hk_def
  have hk : k ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) ha
  have hk0 : k ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hc) ha0
  have hck : c * k = a := by
    rw [hk_def, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hc, one_mul]
  by_cases h_top : klDiv μ ν = ∞
  · rw [(klDiv_smul_left_eq_top_iff hk0 hk).mpr h_top, h_top, ENNReal.mul_top hc0,
      ENNReal.mul_top ha0, add_top]
  rw [klDiv_smul_left_eq_ofReal h_top hk, klDiv_smul_left_eq_ofReal (by simp [klDiv_self]) hk]
  simp only [klDiv_self, measure_univ, ENNReal.toReal_one, ENNReal.toReal_zero, mul_zero,
    zero_add, mul_one]
  have hY : 0 ≤ 1 - k.toReal + k.toReal * Real.log k.toReal := by
    have h := klFun_nonneg (ENNReal.toReal_nonneg (a := k))
    rw [klFun] at h
    linarith
  have hkK : k * klDiv μ ν = ENNReal.ofReal (k.toReal * (klDiv μ ν).toReal) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hk,
      ENNReal.ofReal_toReal h_top]
  have h_eq : ENNReal.ofReal (k.toReal * (klDiv μ ν).toReal + (1 - k.toReal)
        + k.toReal * Real.log k.toReal)
      = ENNReal.ofReal (1 - k.toReal + k.toReal * Real.log k.toReal) + k * klDiv μ ν := by
    rw [hkK, ← ENNReal.ofReal_add hY (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    congr 1
    ring
  rw [h_eq, mul_add, ← mul_assoc, hck]

lemma klDiv_smul_left_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ₁) ν₁ ≤ klDiv (c • μ₂) ν₂ := by
  by_cases h2 : klDiv μ₂ ν₂ = ∞
  · by_cases hc : c = 0
    · simp [hc, klDiv_zero_left, h_eq_ν]
    · rw [(klDiv_smul_left_eq_top_iff hc hc_top).mpr h2]
      exact le_top
  have h1 : klDiv μ₁ ν₁ ≠ ∞ := ne_top_of_le_ne_top h2 h_le
  rw [klDiv_smul_left_eq_ofReal h1 hc_top, klDiv_smul_left_eq_ofReal h2 hc_top, h_eq_μ, h_eq_ν]
  gcongr

lemma klDiv_smul_smul_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) {c c' : ℝ≥0∞} (hc_top : c ≠ ∞) (hc' : c' ≠ 0)
    (hc'_top : c' ≠ ∞) :
    klDiv (c • μ₁) (c' • ν₁) ≤ klDiv (c • μ₂) (c' • ν₂) := by
  lift c to ℝ≥0 using hc_top
  lift c' to ℝ≥0 using hc'_top
  have hc'0 : c' ≠ 0 := by simpa using hc'
  have h := klDiv_smul_left_le_of_le h_eq_μ h_eq_ν h_le (c := ((c'⁻¹ * c : ℝ≥0) : ℝ≥0∞))
    ENNReal.coe_ne_top
  rw [← ENNReal.smul_def, ← ENNReal.smul_def] at h
  rw [← ENNReal.smul_def, ← ENNReal.smul_def, ← ENNReal.smul_def, ← ENNReal.smul_def,
    klDiv_smul_right_eq_smul_left hc'0, klDiv_smul_right_eq_smul_left hc'0, smul_smul, smul_smul]
  gcongr

/-- Monotonicity of the Kullback-Leibler divergence of the normalized measures, for fixed
masses. -/
lemma klDiv_inv_smul_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) :
    klDiv ((μ₁ .univ)⁻¹ • μ₁) ((ν₁ .univ)⁻¹ • ν₁)
      ≤ klDiv ((μ₂ .univ)⁻¹ • μ₂) ((ν₂ .univ)⁻¹ • ν₂) := by
  by_cases hν : ν₂ .univ = 0
  · have hν₁ : ν₁ .univ = 0 := h_eq_ν.trans hν
    obtain rfl := Measure.measure_univ_eq_zero.mp hν
    obtain rfl := Measure.measure_univ_eq_zero.mp hν₁
    simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.inv_zero, smul_zero]
    by_cases hμ : μ₂ = 0
    · subst hμ
      obtain rfl : μ₁ = 0 := Measure.measure_univ_eq_zero.mp (h_eq_μ.trans (by simp))
      simp
    · have : NeZero μ₂ := ⟨hμ⟩
      rw [klDiv_zero_right (μ := (μ₂ .univ)⁻¹ • μ₂)]
      exact le_top
  have : NeZero ν₂ := ⟨fun h ↦ hν (by simp [h])⟩
  have : NeZero ν₁ := ⟨fun h ↦ hν (h_eq_ν.symm.trans (by simp [h]))⟩
  by_cases hμ : μ₂ .univ = 0
  · have hμ₁ : μ₁ .univ = 0 := h_eq_μ.trans hμ
    obtain rfl := Measure.measure_univ_eq_zero.mp hμ
    obtain rfl := Measure.measure_univ_eq_zero.mp hμ₁
    simp only [smul_zero, klDiv_zero_left, measure_univ, le_refl]
  rw [h_eq_μ, h_eq_ν]
  exact klDiv_smul_smul_le_of_le h_eq_μ h_eq_ν h_le (ENNReal.inv_ne_top.mpr hμ)
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hν)

/-! ### Restriction to an event -/

section Restrict

open ProbabilityTheory

variable {s : Set α}

/-- **Expectation of the log-likelihood ratio on an event**:
`μ(s) log (μ(s) / ν(s)) ≤ ∫ x in s, llr μ ν x ∂μ`. Only the restrictions of `μ` and `ν` to `s`
matter: absolute continuity and integrability are required on `s` only. -/
lemma mul_log_le_setIntegral_llr [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ.restrict s ≪ ν.restrict s) (h_int : IntegrableOn (llr μ ν) s μ)
    (hs : MeasurableSet s) :
    μ.real s * Real.log (μ.real s / ν.real s) ≤ ∫ x in s, llr μ ν x ∂μ := by
  have h_llr : llr (μ.restrict s) (ν.restrict s) =ᵐ[μ.restrict s] llr μ ν := by
    filter_upwards [hμν.ae_le (Measure.rnDeriv_restrict_restrict μ ν hs)] with x hx
    rw [llr, llr, hx]
  have h_int' : Integrable (llr (μ.restrict s) (ν.restrict s)) (μ.restrict s) :=
    h_int.congr h_llr.symm
  have h := mul_log_le_toReal_klDiv hμν h_int'
  rw [toReal_klDiv hμν h_int', integral_congr_ae h_llr] at h
  simp only [measureReal_restrict_apply_univ] at h
  linarith

/-- The Kullback-Leibler divergence between the restrictions of two finite measures to an event
`s`: `KL(μ|s, ν|s) = KL(μ(s) • ρ, ν(s) • ρ) + μ(s) KL(μ[|s], ν[|s])` for any probability
measure `ρ`. -/
lemma klDiv_restrict_eq_add {β : Type*} {mβ : MeasurableSpace β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (s : Set α) (ρ : Measure β) [IsProbabilityMeasure ρ] :
    klDiv (μ.restrict s) (ν.restrict s) = klDiv (μ s • ρ) (ν s • ρ) + μ s * klDiv μ[|s] ν[|s] := by
  rcases eq_or_ne (μ s) 0 with hμs | hμs
  · have := ρ.smul_finite (measure_ne_top ν s)
    simp [Measure.restrict_eq_zero.mpr hμs, hμs, klDiv_zero_left]
  rcases eq_or_ne (ν s) 0 with hνs | hνs
  · have : NeZero (μ.restrict s) := ⟨by simp [Measure.restrict_eq_zero, hμs]⟩
    have : NeZero (μ s • ρ) := ⟨by simp [hμs, IsProbabilityMeasure.ne_zero]⟩
    simp [Measure.restrict_eq_zero.mpr hνs, hνs, klDiv_zero_right]
  have h_restrict (ξ : Measure α) [IsFiniteMeasure ξ] (h : ξ s ≠ 0) :
      ξ.restrict s = ξ s • ξ[|s] := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]
  have := cond_isProbabilityMeasure (μ := μ) hμs
  have := cond_isProbabilityMeasure (μ := ν) hνs
  rw [h_restrict μ hμs, h_restrict ν hνs]
  exact klDiv_smul_smul_eq_add _ _ ρ (measure_ne_top _ _) (measure_ne_top _ _)

end Restrict

end InformationTheory
