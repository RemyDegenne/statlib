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
* `MeasureTheory.Measure.prob_true_eq_one_sub`: `π {true} = 1 - π {false}` for a probability
  measure `π` on `Bool`.
* `MeasureTheory.Measure.isProbabilityMeasure_boolMeasure`: `boolMeasure a b` is a probability
  measure if `a + b = 1`.
* `MeasureTheory.Measure.eq_boolMeasure_toNNReal`: every probability measure `π` on `Bool` is the
  prior `boolMeasure α (1 - α)` with `α = π {false}`.
* `MeasureTheory.Measure.map_decide_mem_eq_boolMeasure`: the law of the indicator of a measurable
  set `s` under `μ` is `boolMeasure (μ sᶜ) (μ s)`.
* `MeasureTheory.lintegral_bool`: `∫⁻ x, f x ∂π = f false * π {false} + f true * π {true}`.

## Implementation notes

Two conventions are used for the prior `(α, 1 - α)` on `Bool`:
`boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞)` with `α : ℝ≥0`, and
`boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))` with `p : ℝ`. They are related by
`MeasureTheory.Measure.boolMeasure_coe_eq_ofReal`. The second one is the Bernoulli distribution
`Ber(false, true, p)` (`MeasureTheory.Measure.boolMeasure_ofReal_eq_bernoulliMeasure`, in
`Statlib.ForMathlib.Probability.Distributions.Bernoulli`).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open scoped ENNReal NNReal

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

/-- `boolMeasure a b` is finite for masses `a b : ℝ≥0`. -/
instance isFiniteMeasure_boolMeasure_coe (a b : ℝ≥0) : IsFiniteMeasure (boolMeasure a b) :=
  isFiniteMeasure_boolMeasure ENNReal.coe_ne_top ENNReal.coe_ne_top

/-- `boolMeasure a b` is finite for masses given by `ENNReal.ofReal`. -/
instance isFiniteMeasure_boolMeasure_ofReal (a b : ℝ) :
    IsFiniteMeasure (boolMeasure (ENNReal.ofReal a) (ENNReal.ofReal b)) :=
  isFiniteMeasure_boolMeasure ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- `boolMeasure a b` is a probability measure if `a + b = 1`. -/
lemma isProbabilityMeasure_boolMeasure {a b : ℝ≥0∞} (h : a + b = 1) :
    IsProbabilityMeasure (boolMeasure a b) :=
  ⟨by simp [h]⟩

/-- The prior `(α, 1 - α)` on `Bool`, for `α : ℝ≥0` with `α ≤ 1`, is a probability measure. -/
lemma isProbabilityMeasure_boolMeasure_coe {α : ℝ≥0} (hα : α ≤ 1) :
    IsProbabilityMeasure (boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞)) :=
  isProbabilityMeasure_boolMeasure <| by
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hα, ENNReal.coe_one]

/-- The prior `(p, 1 - p)` on `Bool`, for `p ∈ [0, 1]`, is a probability measure. -/
lemma isProbabilityMeasure_boolMeasure_ofReal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))) :=
  isProbabilityMeasure_boolMeasure <| by
    rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1), add_sub_cancel, ENNReal.ofReal_one]

/-- The prior `boolMeasure α (1 - α)` with `α : ℝ≥0`, written with `ENNReal.ofReal`. -/
lemma boolMeasure_coe_eq_ofReal (α : ℝ≥0) :
    boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞)
      = boolMeasure (ENNReal.ofReal α) (ENNReal.ofReal (1 - α)) := by
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal, NNReal.sub_def, NNReal.coe_one]

lemma eq_boolMeasure (π : Measure Bool) : π = boolMeasure (π {false}) (π {true}) := by
  ext <;> simp

lemma prob_true_eq_one_sub (π : Measure Bool) [IsProbabilityMeasure π] :
    π {true} = 1 - π {false} := by
  rw [← prob_compl_eq_one_sub (measurableSet_singleton false), Bool.compl_singleton, Bool.not_false]

/-- A probability measure `π` on `Bool` is `boolMeasure α (1 - α)` for `α = π {false}`. -/
lemma eq_boolMeasure_toNNReal (π : Measure Bool) [IsProbabilityMeasure π] :
    π = boolMeasure ((π {false}).toNNReal : ℝ≥0∞) ((1 - (π {false}).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  conv_lhs => rw [eq_boolMeasure π]
  rw [ENNReal.coe_toNNReal (measure_ne_top π _), ENNReal.coe_sub, ENNReal.coe_one,
    ENNReal.coe_toNNReal (measure_ne_top π _), prob_true_eq_one_sub]

lemma withDensity_eq_boolMeasure (π : Measure Bool) (f : Bool → ℝ≥0∞) :
    π.withDensity f = boolMeasure (f false * π {false}) (f true * π {true}) := by
  ext <;> simp [mul_comm]

@[simp]
lemma smul_boolMeasure (c a b : ℝ≥0∞) : c • boolMeasure a b = boolMeasure (c * a) (c * b) := by
  simp [boolMeasure, smul_add, smul_smul]

/-- The restriction of `boolMeasure a b` to `{true}` is `b • dirac true`. -/
lemma restrict_boolMeasure_true (a b : ℝ≥0∞) :
    (boolMeasure a b).restrict {true} = b • dirac true := by
  simp [boolMeasure]

/-- The restriction of `boolMeasure a b` to `{true}ᶜ` is `a • dirac false`. -/
lemma restrict_boolMeasure_compl_true (a b : ℝ≥0∞) :
    (boolMeasure a b).restrict {true}ᶜ = a • dirac false := by
  simp [boolMeasure]

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
