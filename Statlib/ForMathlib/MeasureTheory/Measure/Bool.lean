/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures on `Bool`

A measure on `Bool` is determined by its values on `{false}` and `{true}`.

## Main definitions

* `MeasureTheory.Measure.boolMeasure a b`: the measure on `Bool` with mass `a` at `false` and `b`
  at `true`.

## Main statements

* `MeasureTheory.Measure.ext_bool`: two measures on `Bool` which agree on `{false}` and `{true}`
  are equal.
* `MeasureTheory.Measure.eq_boolMeasure`: every measure `π` on `Bool` is
  `boolMeasure (π {false}) (π {true})`.
* `MeasureTheory.Measure.map_decide_mem_eq_boolMeasure`: the law of the indicator of a measurable
  set `s` under `μ` is `boolMeasure (μ sᶜ) (μ s)`.
* `MeasureTheory.lintegral_bool`: `∫⁻ x, f x ∂π = f false * π {false} + f true * π {true}`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

lemma _root_.measurable_decide_mem {α : Type*} {mα : MeasurableSpace α} {s : Set α}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    Measurable fun x ↦ decide (x ∈ s) :=
  measurable_to_bool (by simpa [Set.preimage] using hs)

namespace Measure

@[ext]
lemma ext_bool {π₁ π₂ : Measure Bool} (h_false : π₁ {false} = π₂ {false})
    (h_true : π₁ {true} = π₂ {true}) :
    π₁ = π₂ :=
  ext_iff_singleton.mpr (Bool.forall_bool.mpr ⟨h_false, h_true⟩)

/-- The measure on `Bool` with mass `a` at `false` and `b` at `true`. -/
noncomputable
def boolMeasure (a b : ℝ≥0∞) : Measure Bool := a • dirac false + b • dirac true

@[simp]
lemma boolMeasure_apply_false (a b : ℝ≥0∞) : boolMeasure a b {false} = a := by simp [boolMeasure]

@[simp]
lemma boolMeasure_apply_true (a b : ℝ≥0∞) : boolMeasure a b {true} = b := by simp [boolMeasure]

/-- The total mass of `boolMeasure a b`. The set `{false, true}` is the simp normal form of
`Set.univ : Set Bool` (`Bool.univ_eq`). -/
@[simp]
lemma boolMeasure_apply_univ (a b : ℝ≥0∞) : boolMeasure a b {false, true} = a + b := by
  simp [boolMeasure]

lemma isFiniteMeasure_boolMeasure {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    IsFiniteMeasure (boolMeasure a b) :=
  ⟨by simp [lt_top_iff_ne_top, ha, hb]⟩

/-- The uniform measure `boolMeasure 1 1` is finite. -/
instance isFiniteMeasure_boolMeasure_one_one : IsFiniteMeasure (boolMeasure 1 1) :=
  isFiniteMeasure_boolMeasure ENNReal.one_ne_top ENNReal.one_ne_top

lemma eq_boolMeasure (π : Measure Bool) : π = boolMeasure (π {false}) (π {true}) := by
  ext <;> simp

lemma withDensity_eq_boolMeasure (π : Measure Bool) (f : Bool → ℝ≥0∞) :
    π.withDensity f = boolMeasure (f false * π {false}) (f true * π {true}) := by
  ext <;> simp [mul_comm]

/-- The law under `μ` of the indicator `x ↦ decide (x ∈ s)` of a measurable set `s`. -/
lemma map_decide_mem_eq_boolMeasure {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    μ.map (fun x ↦ decide (x ∈ s)) = boolMeasure (μ sᶜ) (μ s) := by
  have hg := measurable_decide_mem hs
  ext
  · rw [map_apply hg (measurableSet_singleton _), boolMeasure_apply_false]
    congr with x
    simp
  · rw [map_apply hg (measurableSet_singleton _), boolMeasure_apply_true]
    congr with x
    simp

end Measure

lemma lintegral_bool {f : Bool → ℝ≥0∞} (π : Measure Bool) :
    ∫⁻ x, f x ∂π = f false * π {false} + f true * π {true} := by
  simp [add_comm, lintegral_fintype]

end MeasureTheory
