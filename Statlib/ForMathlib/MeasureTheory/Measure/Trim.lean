/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Restriction of a measure to a sub-σ-algebra

## Main statements

* `MeasureTheory.isProbabilityMeasure_trim`: the restriction `μ.trim hm` of a probability measure
  to a sub-σ-algebra is a probability measure.
* `MeasureTheory.sigmaFinite_trim_comap`: if `μ.map g` is σ-finite, so is the restriction of `μ`
  to the σ-algebra `mβ.comap g`.
-/

@[expose] public section

namespace MeasureTheory

/-- The restriction of a probability measure to a sub-σ-algebra is a probability measure. -/
instance isProbabilityMeasure_trim {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.trim hm) :=
  ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]⟩

/-- If `μ.map g` is σ-finite, so is the restriction of `μ` to the σ-algebra `mβ.comap g`. -/
lemma sigmaFinite_trim_comap {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {g : α → β} (hg : Measurable g) [SigmaFinite (μ.map g)] :
    SigmaFinite (μ.trim hg.comap_le) := by
  have h : SigmaFinite (μ.map g) := inferInstance
  rw [← map_trim_comap hg] at h
  exact SigmaFinite.of_map _ (comap_measurable g).aemeasurable h

end MeasureTheory
