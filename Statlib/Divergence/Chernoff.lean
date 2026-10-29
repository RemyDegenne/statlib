/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Basic

/-!
# Chernoff divergence

## Main definitions

* `chernoffDiv a μ ν`: the Chernoff divergence of order `a`,
  `⨅ ξ, max (renyiDiv a ξ μ) (renyiDiv a ξ ν)` over probability measures `ξ`.

## Main statements

* `chernoffDiv_comm`: the Chernoff divergence is symmetric.
* `chernoffDiv_zero_measure_left`, `chernoffDiv_zero_measure_right`: the Chernoff divergence
  between the zero measure and any measure is infinite.
* `chernoffDiv_one`: the Chernoff divergence of order `1` as an infimum of Kullback-Leibler
  divergences.
* `chernoffDiv_smul_smul`, `chernoffDiv_eq_chernoffDiv_inv_smul`: invariance under scaling of the
  measures.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- Chernoff divergence of order `a` between two measures `μ, ν`.
This is the infimum over probability measures `ξ` of the maximum of the Rényi divergences
of order `a` from `ξ` to `μ` and from `ξ` to `ν`. -/
noncomputable def chernoffDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (renyiDiv a ξ μ) (renyiDiv a ξ ν)

/-- The Chernoff divergence is symmetric. -/
lemma chernoffDiv_comm (a : ℝ) (μ ν : Measure α) : chernoffDiv a μ ν = chernoffDiv a ν μ := by
  simp_rw [chernoffDiv, max_comm]

/-- The Chernoff divergence between the zero measure and any measure is infinite. -/
@[simp]
lemma chernoffDiv_zero_measure_left (ha : 0 ≤ a) (ν : Measure α) : chernoffDiv a 0 ν = ∞ :=
  iInf₂_eq_top.mpr fun ξ _ ↦ by rw [renyiDiv_zero_measure_right ha ξ, max_eq_left le_top]

/-- The Chernoff divergence between any measure and the zero measure is infinite. -/
@[simp]
lemma chernoffDiv_zero_measure_right (ha : 0 ≤ a) (μ : Measure α) : chernoffDiv a μ 0 = ∞ := by
  rw [chernoffDiv_comm, chernoffDiv_zero_measure_left ha]

/-- For probability measures, the Chernoff divergence of order `1` is the infimum over probability
measures `ξ` of `max (KL(ξ, μ)) (KL(ξ, ν))`. -/
lemma chernoffDiv_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    chernoffDiv 1 μ ν
      = ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (klDiv ξ μ) (klDiv ξ ν) := by
  simp_rw [chernoffDiv]
  congr with ξ
  congr with hξ
  rw [renyiDiv_one_of_isProbabilityMeasure, renyiDiv_one_of_isProbabilityMeasure]

/-- The Chernoff divergence is invariant under scaling of the measures by positive finite
constants. -/
lemma chernoffDiv_smul_smul (ha : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c c' : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) (hc' : c' ≠ 0) (hc'_top : c' ≠ ∞) :
    chernoffDiv a (c • μ) (c' • ν) = chernoffDiv a μ ν :=
  iInf_congr fun _ ↦ iInf_congr fun _ ↦ by
    rw [renyiDiv_smul_right' ha hc hc_top, renyiDiv_smul_right' ha hc' hc'_top]

/-- The Chernoff divergence between finite measures is the Chernoff divergence between the
normalized measures. -/
lemma chernoffDiv_eq_chernoffDiv_inv_smul (ha : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    chernoffDiv a μ ν = chernoffDiv a ((μ .univ)⁻¹ • μ) ((ν .univ)⁻¹ • ν) := by
  rcases eq_zero_or_neZero μ with rfl | _
  · simp [ha]
  rcases eq_zero_or_neZero ν with rfl | _
  · simp [ha]
  exact (chernoffDiv_smul_smul ha (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _)) (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))).symm

end ProbabilityTheory
