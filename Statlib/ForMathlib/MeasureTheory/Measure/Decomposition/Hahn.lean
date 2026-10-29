/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn

/-!
# Hahn decompositions and suprema over measurable sets

If `s` is a Hahn decomposition for the measures `μ` and `ν` (`μ ≤ ν` on `s` and `ν ≤ μ` on `sᶜ`)
and `ν sᶜ < ∞`, then the supremum of `μ E - ν E` over measurable sets `E` is attained at `sᶜ`.
The finiteness assumption is needed: for `x ≠ y`, `∅` is a Hahn decomposition for
`μ = δ_x + ∞ • δ_y` and `ν = ∞ • δ_y`, but `μ univ - ν univ = 0 < 1 = μ {x} - ν {x}`.

## Main statements

* `MeasureTheory.IsHahnDecomposition.measure_sub_le`: if `s` is a Hahn decomposition for `μ` and
  `ν`, then `μ E - ν E ≤ μ sᶜ - ν sᶜ` for every measurable set `E`.
* `MeasureTheory.IsHahnDecomposition.iSup_measure_sub`: if `s` is a Hahn decomposition for `μ` and
  `ν`, then `⨆ E, μ E - ν E = μ sᶜ - ν sᶜ`, where the supremum is over measurable sets.
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s E : Set α}

/-- If `s` is a Hahn decomposition for `μ` and `ν` (`μ ≤ ν` on `s` and `ν ≤ μ` on `sᶜ`) with
`ν sᶜ < ∞`, then `μ E - ν E ≤ μ sᶜ - ν sᶜ` for every measurable set `E`. -/
lemma IsHahnDecomposition.measure_sub_le (h : IsHahnDecomposition μ ν s) (hE : MeasurableSet E)
    (hν : ν sᶜ ≠ ∞ := by finiteness) :
    μ E - ν E ≤ μ sᶜ - ν sᶜ := by
  have h_le : μ (E ∩ s) ≤ ν (E ∩ s) := by
    simpa [Measure.restrict_apply' h.measurableSet] using Measure.le_iff'.mp h.le_on E
  have h_ge (t : Set α) : ν (sᶜ ∩ t) ≤ μ (sᶜ ∩ t) := by
    simpa [Measure.restrict_apply' h.measurableSet.compl, inter_comm]
      using Measure.le_iff'.mp h.ge_on_compl t
  have hE_sdiff : E \ s = sᶜ ∩ E := by rw [sdiff_eq, inter_comm]
  -- split `E` along `s`, then complete `sᶜ ∩ E` into `sᶜ`
  calc μ E - ν E = μ (E ∩ s) + μ (sᶜ ∩ E) - (ν (E ∩ s) + ν (sᶜ ∩ E)) := by
        rw [← hE_sdiff, measure_inter_add_sdiff _ h.measurableSet,
          measure_inter_add_sdiff _ h.measurableSet]
  _ ≤ ν (E ∩ s) + μ (sᶜ ∩ E) - (ν (E ∩ s) + ν (sᶜ ∩ E)) := by gcongr
  _ ≤ μ (sᶜ ∩ E) - ν (sᶜ ∩ E) := add_tsub_add_le_tsub_left
  _ ≤ μ (sᶜ ∩ E) - ν (sᶜ ∩ E) + (μ (sᶜ \ E) - ν (sᶜ \ E)) := le_self_add
  _ = μ (sᶜ ∩ E) + μ (sᶜ \ E) - (ν (sᶜ ∩ E) + ν (sᶜ \ E)) :=
        AddLECancellable.tsub_add_tsub_comm
          (ENNReal.cancel_of_ne (ne_top_of_le_ne_top hν (measure_mono inter_subset_left)))
          (ENNReal.cancel_of_ne (ne_top_of_le_ne_top hν (measure_mono sdiff_subset))) (h_ge E)
          (by simpa [sdiff_eq] using h_ge Eᶜ)
  _ = μ sᶜ - ν sᶜ := by rw [measure_inter_add_sdiff _ hE, measure_inter_add_sdiff _ hE]

/-- If `s` is a Hahn decomposition for `μ` and `ν` (`μ ≤ ν` on `s` and `ν ≤ μ` on `sᶜ`) with
`ν sᶜ < ∞`, then the supremum of `μ E - ν E` over measurable sets `E` is attained at `sᶜ`. -/
lemma IsHahnDecomposition.iSup_measure_sub (h : IsHahnDecomposition μ ν s)
    (hν : ν sᶜ ≠ ∞ := by finiteness) :
    ⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E = μ sᶜ - ν sᶜ :=
  le_antisymm (iSup₂_le fun _ hE ↦ h.measure_sub_le hE hν)
    (le_iSup₂_of_le sᶜ h.measurableSet.compl le_rfl)

end MeasureTheory
