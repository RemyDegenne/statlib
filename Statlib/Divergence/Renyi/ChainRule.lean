/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Posterior
public import Statlib.Divergence.Renyi.CondRenyi
public import Statlib.Divergence.Renyi.DataProcessing
public import Statlib.Divergence.Renyi.Variational

/-!
# Chain rule for the Rényi divergence

For finite measures `μ`, `ν`, Markov kernels `κ`, `η` and `0 < a`,
`Rₐ(μ ⊗ₘ κ, ν ⊗ₘ η) = Rₐ(μ, ν) + Rₐ(κ, η | μ^(a, ν))`, in which `μ^(a, ν) = renyiMeasure a μ ν` is
the Rényi measure and `Rₐ(κ, η | ρ) = condRenyiDiv a κ η ρ = Rₐ(ρ ⊗ₘ κ, ρ ⊗ₘ η)` is the
conditional Rényi divergence.

The chain rule holds without assumptions on the measurable spaces. The proof for probability
measures goes through the Hellinger integrals `∫⁻ (∂μ/∂ν) ^ a ∂ν`. Writing `ρ = μ^(a, ν)`, whose
density with respect to `ν` is `(∂μ/∂ν) ^ a` up to a constant, the Hellinger integral of
`ρ ⊗ₘ κ` and `ρ ⊗ₘ η` is proportional to that of `μ ⊗ₘ κ` and `ν ⊗ₘ η`, by the decomposition
`∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) = ∂μ/∂ν * ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` (`rnDeriv_compProd'`) and the equality
`∂(ρ ⊗ₘ κ)/∂(ρ ⊗ₘ η) = ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` for `ρ ≪ μ`
(`rnDeriv_compProd_of_absolutelyContinuous`). The case of finite measures follows by normalizing
`μ` and `ν`, which does not change the Rényi divergences and multiplies the Rényi measure by a
constant (`renyiMeasure_smul_smul`, `condRenyiDiv_smul_measure`).

## Main statements

* `renyiDiv_compProd_eq_add_condRenyiDiv`: the chain rule.
* `renyiDiv_compProd_eq_add_condRenyiDiv_posterior`: the chain rule with the posterior kernels
  (Bayesian inverses),
  `Rₐ(μ ⊗ₘ κ, ν ⊗ₘ η) = Rₐ(κ ∘ₘ μ, η ∘ₘ ν) + Rₐ(κ†μ, η†ν | (κ ∘ₘ μ)^(a, η ∘ₘ ν))`.
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {κ η : Kernel α β} {a : ℝ}

/-- `renyiDiv_compProd_eq_add_condRenyiDiv` for probability measures with `Rₐ(μ, ν) < ∞`. -/
private lemma renyiDiv_compProd_eq_add_condRenyiDiv_of_isProbabilityMeasure
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsMarkovKernel κ] [IsMarkovKernel η] (ha0 : 0 < a) (hR : renyiDiv a μ ν ≠ ∞) :
    renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) = renyiDiv a μ ν + condRenyiDiv a κ η (renyiMeasure a μ ν) := by
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [renyiMeasure_one, condRenyiDiv, renyiDiv_one_of_isProbabilityMeasure,
      renyiDiv_one_of_isProbabilityMeasure, renyiDiv_one_of_isProbabilityMeasure,
      klDiv_compProd_eq_add]
  set ρ := renyiMeasure a μ ν
  set c := exp (-(a - 1) * (renyiDiv a μ ν).toReal)
  have h_prob : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top ha0 hR
  -- the Hellinger integrals of the joint measures are proportional
  have h_key : ∫⁻ p, ((∂ρ ⊗ₘ κ/∂ρ ⊗ₘ η) p) ^ a ∂(ρ ⊗ₘ η)
      = ENNReal.ofReal c * ∫⁻ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ^ a ∂(ν ⊗ₘ η) := by
    have h_or : a < 1 ∨ μ ≪ ν := ha1.lt_or_gt.imp_right fun ha1 ↦
      absolutelyContinuous_of_renyiDiv_ne_top ha1.le hR
    -- `ρ ⊗ₘ η` is `ν ⊗ₘ η` tilted by `(∂μ/∂ν) ^ a`
    have hρη : ρ ⊗ₘ η
        = (ν ⊗ₘ η).withDensity (fun p ↦ ((∂μ/∂ν) p.1) ^ a * ENNReal.ofReal c) := by
      have hρ : ρ = _ := renyiMeasure_eq_withDensity ha0.le h_or
      rw [hρ]
      exact Measure.withDensity_compProd (by fun_prop)
    calc ∫⁻ p, ((∂ρ ⊗ₘ κ/∂ρ ⊗ₘ η) p) ^ a ∂(ρ ⊗ₘ η)
    _ = ∫⁻ p, ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p) ^ a ∂(ρ ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [rnDeriv_compProd_of_absolutelyContinuous (κ := κ) (η := η)
          (renyiMeasure_absolutelyContinuous_left ν ha0)] with p hp
        rw [hp]
    _ = ∫⁻ p, ENNReal.ofReal c * (((∂μ/∂ν) p.1) ^ a * ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p) ^ a)
          ∂(ν ⊗ₘ η) := by
        rw [hρη, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
        refine lintegral_congr fun p ↦ ?_
        simp only [Pi.mul_apply]
        ring
    _ = ENNReal.ofReal c * ∫⁻ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ^ a ∂(ν ⊗ₘ η) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [rnDeriv_compProd' μ ν κ η] with p hp
        rw [hp, ENNReal.mul_rpow_of_nonneg _ _ ha0.le]
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr (exp_pos _)).ne'
  -- the divergence between the joint measures is finite iff the conditional divergence is finite
  have h_fin : renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞ ↔ renyiDiv a (ρ ⊗ₘ κ) (ρ ⊗ₘ η) ≠ ∞ := by
    rcases ha1.lt_or_gt with ha1 | ha1
    · rw [ne_eq, ne_eq, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1,
        renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1,
        ← lintegral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha0,
        ← lintegral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha0, h_key, mul_eq_zero,
        or_iff_right hc0]
    · have hμν : μ ≪ ν := ((renyiDiv_ne_top_iff_of_one_lt ha1).mp hR).2
      -- `ρ` and `μ` have the same null sets
      have hρμ : ρ ≪ μ := renyiMeasure_absolutelyContinuous_left ν ha0
      have hμρ : μ ≪ ρ := absolutelyContinuous_renyiMeasure a .rfl hμν
      have h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ ρ ⊗ₘ κ ≪ ρ ⊗ₘ η := by
        rw [Measure.absolutelyContinuous_compProd_iff, and_iff_right hμν]
        exact ⟨fun h ↦ (hρμ.compProd_left κ).trans (h.trans (hμρ.compProd_left η)),
          fun h ↦ (hμρ.compProd_left κ).trans (h.trans (hρμ.compProd_left η))⟩
      rw [renyiDiv_ne_top_iff_of_one_lt ha1, renyiDiv_ne_top_iff_of_one_lt ha1,
        integrable_rpow_rnDeriv_iff_lintegral_ne_top ha0.le,
        integrable_rpow_rnDeriv_iff_lintegral_ne_top ha0.le, h_key, h_ac]
      simp [ENNReal.mul_eq_top, hc0]
  by_cases hP : renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞
  · have hP' : renyiDiv a (ρ ⊗ₘ κ) (ρ ⊗ₘ η) = ∞ := by
      by_contra h
      exact h_fin.mpr h hP
    rw [hP, condRenyiDiv, hP', add_top]
  have hP' : renyiDiv a (ρ ⊗ₘ κ) (ρ ⊗ₘ η) ≠ ∞ := h_fin.mp hP
  have hH_pos := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha0 hP
  have h_real : ∫ p, ((∂ρ ⊗ₘ κ/∂ρ ⊗ₘ η) p).toReal ^ a ∂(ρ ⊗ₘ η)
      = c * ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ^ a ∂(ν ⊗ₘ η) := by
    rw [integral_rpow_rnDeriv_eq_toReal_lintegral ha0.le,
      integral_rpow_rnDeriv_eq_toReal_lintegral ha0.le, h_key, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (exp_pos _).le]
  have h_toReal : (renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal
      = (renyiDiv a μ ν).toReal + (renyiDiv a (ρ ⊗ₘ κ) (ρ ⊗ₘ η)).toReal := by
    rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha0 ha1 hP,
      toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha0 ha1 hP', h_real,
      log_mul (exp_pos _).ne' hH_pos.ne', log_exp]
    have : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    field_simp
    ring
  rw [condRenyiDiv, ← ENNReal.ofReal_toReal hP, h_toReal,
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hR,
    ENNReal.ofReal_toReal hP']

/-- **Chain rule** for the Rényi divergence: for finite measures `μ`, `ν`, Markov kernels `κ`, `η`
and `0 < a`, `Rₐ(μ ⊗ₘ κ, ν ⊗ₘ η) = Rₐ(μ, ν) + Rₐ(κ, η | μ^(a, ν))`, in which
`μ^(a, ν) = renyiMeasure a μ ν`. For `a = 1`, this is the chain rule for the Kullback-Leibler
divergence. -/
theorem renyiDiv_compProd_eq_add_condRenyiDiv
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (ha0 : 0 < a) :
    renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) = renyiDiv a μ ν + condRenyiDiv a κ η (renyiMeasure a μ ν) := by
  -- degenerate cases: `μ = 0` or `ν = 0`
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rcases eq_or_ne a 1 with rfl | ha1
    · rcases eq_zero_or_neZero ν with rfl | hν
      · simp [condRenyiDiv]
      have hc : (ν .univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (NeZero.ne _)
      have := ν.smul_finite hc
      have := (ν ⊗ₘ η).smul_finite hc
      simp [condRenyiDiv, klDiv_zero_left, Measure.compProd_apply_univ,
        ENNReal.inv_mul_cancel (NeZero.ne (ν .univ)) (measure_ne_top _ _)]
    simp only [Measure.compProd_zero_left, renyiMeasure_zero_left ha0, condRenyiDiv,
      renyiDiv_zero_measure_left ha0.le ha1]
    split_ifs <;> simp
  rcases eq_zero_or_neZero ν with rfl | hν
  · simp [renyiDiv_zero_measure_right ha0.le]
  by_cases hR : renyiDiv a μ ν = ∞
  · rw [hR, top_add, eq_top_iff, ← hR]
    calc renyiDiv a μ ν = renyiDiv a (μ ⊗ₘ κ).fst (ν ⊗ₘ η).fst := by
          rw [Measure.fst_compProd, Measure.fst_compProd]
    _ ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) := renyiDiv_fst_le ha0.le _ _
  -- reduce to probability measures by normalizing `μ` and `ν`: the Rényi divergences do not change
  -- and the Rényi measure is multiplied by a constant `k ∈ (0, ∞)`
  have h_or : a < 1 ∨ μ ≪ ν := (lt_or_ge a 1).imp_right fun ha1 ↦
    absolutelyContinuous_of_renyiDiv_ne_top ha1 hR
  set cμ := (μ .univ)⁻¹
  set cν := (ν .univ)⁻¹
  have hcμ0 : cμ ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  have hcμ_top : cμ ≠ ∞ := ENNReal.inv_ne_top.mpr (NeZero.ne _)
  have hcν0 : cν ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  have hcν_top : cν ≠ ∞ := ENNReal.inv_ne_top.mpr (NeZero.ne _)
  set k := cμ ^ a * cν ^ (1 - a)
  have hk0 : k ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hcμ0) hcμ_top).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hcν0) hcν_top).ne'
  have hk_top : k ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hcμ0 hcμ_top)
    (ENNReal.rpow_ne_top_of_ne_zero hcν0 hcν_top)
  have h_eq := renyiMeasure_smul_smul ha0.le h_or hcμ0 hcμ_top hcν0 hcν_top
  have hR' : renyiDiv a (cμ • μ) (cν • ν) ≠ ∞ := by
    rwa [renyiDiv_smul_smul ha0.le hcμ0 hcμ_top hcν0 hcν_top]
  -- the Rényi measure of `μ` and `ν` is finite, since the normalized one is a probability measure
  have : IsFiniteMeasure (renyiMeasure a μ ν) := by
    have h_prob := isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top ha0 hR'
    rw [h_eq] at h_prob
    rw [← one_smul ℝ≥0∞ (renyiMeasure a μ ν), ← ENNReal.inv_mul_cancel hk0 hk_top, ← smul_smul]
    exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hk0)
  calc renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) = renyiDiv a ((cμ • μ) ⊗ₘ κ) ((cν • ν) ⊗ₘ η) := by
        rw [Measure.compProd_smul_left, Measure.compProd_smul_left,
          renyiDiv_smul_smul ha0.le hcμ0 hcμ_top hcν0 hcν_top]
  _ = renyiDiv a (cμ • μ) (cν • ν) + condRenyiDiv a κ η (renyiMeasure a (cμ • μ) (cν • ν)) :=
        renyiDiv_compProd_eq_add_condRenyiDiv_of_isProbabilityMeasure ha0 hR'
  _ = renyiDiv a μ ν + condRenyiDiv a κ η (renyiMeasure a μ ν) := by
        rw [renyiDiv_smul_smul ha0.le hcμ0 hcμ_top hcν0 hcν_top, h_eq,
          condRenyiDiv_smul_measure ha0.le κ η _ hk0 hk_top]

/-- **Chain rule** for the Rényi divergence of order `a > 0`, with posterior kernels
(Bayesian inverses): `Rₐ(μ ⊗ₘ κ, ν ⊗ₘ η) = Rₐ(κ ∘ₘ μ, η ∘ₘ ν) + Rₐ(κ†μ, η†ν | ρ)` with
`ρ = renyiMeasure a (κ ∘ₘ μ) (η ∘ₘ ν)`. -/
theorem renyiDiv_compProd_eq_add_condRenyiDiv_posterior [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] (ha0 : 0 < a) :
    renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η)
      = renyiDiv a (κ ∘ₘ μ) (η ∘ₘ ν)
        + condRenyiDiv a (κ†μ) (η†ν) (renyiMeasure a (κ ∘ₘ μ) (η ∘ₘ ν)) := by
  rw [← renyiDiv_compProd_eq_add_condRenyiDiv ha0, compProd_posterior_eq_map_swap,
    compProd_posterior_eq_map_swap]
  exact (renyiDiv_map_measurableEmbedding ha0.le _ _
    MeasurableEquiv.prodComm.measurableEmbedding).symm

end ProbabilityTheory
