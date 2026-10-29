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
# Statistical information as a supremum over events

We express the statistical information `statInfo μ ν π` of finite measures as a supremum over
events of differences of the measures weighted by the prior, using a Hahn decomposition and the
relation between the statistical information and the total variation distance.

## Main statements

* `statInfo_eq_iSup_sub`, `statInfo_eq_iSup_sub'`: for finite measures and a finite prior,
  `I_π(μ, ν) = sup_E (π₁ ν(E) - π₀ μ(E)) - max {0, π₁ ν(𝒳) - π₀ μ(𝒳)}`, and the symmetric
  formula. Since the subtraction in `ℝ≥0∞` is truncated at `0`, the maximum is written as a
  subtraction.
* `statInfo_one_one_eq_iSup_sub`: if `μ(𝒳) ≤ ν(𝒳)`, the statistical information for the prior
  `(1, 1)` is `sup_E (μ(E) - ν(E))`.

In all these statements, the suprema are over measurable sets `E`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳}

/-- The statistical information for the prior `(1, 1)` is
`sup_E (ν(E) - μ(E)) - max {0, ν(𝒳) - μ(𝒳)}`. -/
private lemma statInfo_one_one_eq_iSup_sub_sub [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    statInfo μ ν (Measure.boolMeasure 1 1)
      = (⨆ E, ⨆ (_ : MeasurableSet E), ν E - μ E) - (ν univ - μ univ) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  -- real form of the statistical information, from its expression in terms of `tvDist`
  have h_real : (statInfo μ ν (Measure.boolMeasure 1 1)).toReal
      = (ν.real s - μ.real s) - max (ν.real univ - μ.real univ) 0 := by
    have h_tv := tvDist_eq_two_mul_toReal_statInfo_add_abs μ ν
    rw [hs.tvDist_eq] at h_tv
    have hμ := measureReal_add_measureReal_compl (μ := μ) hs.measurableSet
    have hν := measureReal_add_measureReal_compl (μ := ν) hs.measurableSet
    rcases le_total (μ.real univ) (ν.real univ) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at h_tv
      rw [max_eq_left (sub_nonneg.mpr h)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at h_tv
      rw [max_eq_right (sub_nonpos.mpr h)]
      linarith
  rw [hs.compl.iSup_measure_sub, compl_compl, ← ofReal_measureReal_sub_measureReal,
    ← ofReal_measureReal_sub_measureReal, ← ENNReal.ofReal_toReal (statInfo_ne_top _ _ _),
    h_real, ENNReal.ofReal_sub _ (le_max_right _ 0), ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_zero]

/-- **Statistical information as a supremum over events**: for finite measures and a finite prior,
`I_π(μ, ν) = sup_E (π₁ ν(E) - π₀ μ(E)) - max {0, π₁ ν(𝒳) - π₀ μ(𝒳)}`. -/
theorem statInfo_eq_iSup_sub (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = (⨆ E, ⨆ (_ : MeasurableSet E), π {true} * ν E - π {false} * μ E)
      - (π {true} * ν univ - π {false} * μ univ) := by
  have := μ.smul_finite (measure_ne_top π {false})
  have := ν.smul_finite (measure_ne_top π {true})
  rw [statInfo_eq_statInfo_one_one, statInfo_one_one_eq_iSup_sub_sub]
  simp only [smul_apply, smul_eq_mul]

/-- **Statistical information as a supremum over events**: for finite measures and a finite prior,
`I_π(μ, ν) = sup_E (π₀ μ(E) - π₁ ν(E)) - max {0, π₀ μ(𝒳) - π₁ ν(𝒳)}`. -/
theorem statInfo_eq_iSup_sub' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = (⨆ E, ⨆ (_ : MeasurableSet E), π {false} * μ E - π {true} * ν E)
      - (π {false} * μ univ - π {true} * ν univ) := by
  rw [statInfo_symm, statInfo_eq_iSup_sub]
  simp [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), Set.preimage]

/-- If `μ(𝒳) ≤ ν(𝒳)`, the statistical information for the prior `(1, 1)` is
`sup_E (μ(E) - ν(E))`. -/
lemma statInfo_one_one_eq_iSup_sub (μ ν : Measure 𝒳) [IsFiniteMeasure ν] (h : μ univ ≤ ν univ) :
    statInfo μ ν (Measure.boolMeasure 1 1) = ⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E := by
  have : IsFiniteMeasure μ := ⟨h.trans_lt (measure_lt_top ν _)⟩
  simpa [tsub_eq_zero_of_le h] using statInfo_eq_iSup_sub' μ ν (Measure.boolMeasure 1 1)

end ProbabilityTheory
