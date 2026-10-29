/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.TotalVariation
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Statlib.ForMathlib.MeasureTheory.Measure.Real

/-!
# Total variation distance and events

We express the total variation distance `etvDist μ ν` (the total variation norm of `μ - ν`) in
terms of the suprema over events of `μ E - ν E` and of `ν E - μ E`, using a Hahn decomposition of
`μ` and `ν`.

## Main statements

* `etvDist_eq_iSup_sub_add_iSup_sub`: if `μ` is finite,
  `etvDist μ ν = (⨆ E, μ E - ν E) + ⨆ E, ν E - μ E`.
* `etvDist_eq_two_mul_iSup_sub_add`: if `μ` is finite and `μ(𝒳) ≤ ν(𝒳)`,
  `etvDist μ ν = 2 * (⨆ E, μ E - ν E) + (ν(𝒳) - μ(𝒳))`.
* `etvDist_eq_two_mul_iSup_sub`: for finite measures with the same mass (for example probability
  measures), `etvDist μ ν = 2 * ⨆ E, μ E - ν E`.

In all these statements, the suprema are over measurable sets `E`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳}

/-- The total variation distance is the sum of the suprema over events of `μ E - ν E` and of
`ν E - μ E`. This needs only one of the two measures to be finite: if `ν` is not finite, both sides
are infinite. -/
theorem etvDist_eq_iSup_sub_add_iSup_sub (μ ν : Measure 𝒳) [IsFiniteMeasure μ] :
    etvDist μ ν = (⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E)
      + ⨆ E, ⨆ (_ : MeasurableSet E), ν E - μ E := by
  by_cases hν : IsFiniteMeasure ν
  swap
  · have h_top : ⨆ E, ⨆ (_ : MeasurableSet E), ν E - μ E = ∞ := by
      refine eq_top_iff.mpr (le_iSup₂_of_le univ MeasurableSet.univ ?_)
      rw [not_isFiniteMeasure_iff.mp hν, ENNReal.top_sub (measure_ne_top μ _)]
    rw [etvDist_of_not_isFiniteMeasure_right hν, h_top, add_top]
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  rw [hs.iSup_measure_sub, hs.compl.iSup_measure_sub, compl_compl, hs.etvDist_eq, add_comm]

/-- If `μ` is finite and `μ(𝒳) ≤ ν(𝒳)`, then `etvDist μ ν = 2 * (⨆ E, μ E - ν E) + (ν(𝒳) - μ(𝒳))`.
If `ν` is not finite, both sides are infinite. -/
theorem etvDist_eq_two_mul_iSup_sub_add (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    (h : μ univ ≤ ν univ) :
    etvDist μ ν = 2 * (⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E) + (ν univ - μ univ) := by
  by_cases hν : IsFiniteMeasure ν
  swap
  · rw [etvDist_of_not_isFiniteMeasure_right hν, not_isFiniteMeasure_iff.mp hν,
      ENNReal.top_sub (measure_ne_top μ _), add_top]
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h_real : μ.real univ ≤ ν.real univ := ENNReal.toReal_mono (measure_ne_top _ _) h
  have h_s : ν.real sᶜ ≤ μ.real sᶜ := ENNReal.toReal_mono (measure_ne_top _ _)
    (by simpa using Measure.le_iff'.mp hs.ge_on_compl univ)
  rw [hs.iSup_measure_sub, ← ofReal_tvDist, hs.tvDist_eq, ← ofReal_measureReal_sub_measureReal,
    ← ofReal_measureReal_sub_measureReal, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  have := measureReal_add_measureReal_compl (μ := μ) hs.measurableSet
  have := measureReal_add_measureReal_compl (μ := ν) hs.measurableSet
  linarith

/-- For finite measures with the same mass, for example probability measures,
`etvDist μ ν = 2 * ⨆ E, μ E - ν E`. -/
theorem etvDist_eq_two_mul_iSup_sub (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    (h : μ univ = ν univ) :
    etvDist μ ν = 2 * ⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E := by
  rw [etvDist_eq_two_mul_iSup_sub_add μ ν h.le, h, tsub_self, add_zero]

end ProbabilityTheory
