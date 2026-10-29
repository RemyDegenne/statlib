/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool

/-!
# The Kullback-Leibler divergence and events

We decompose the Kullback-Leibler divergence between two finite measures along an event `s` and its
complement, in terms of the measures conditioned on `s` and on `sᶜ`.

## Main statements

* `klDiv_eq_klDiv_boolMeasure_add_add`: **chain rule for an event**. For finite measures `μ, ν`
  and an event `s`, `KL(μ, ν)` is the Kullback-Leibler divergence between the laws of the indicator
  of `s`, plus `μ(s) KL(μ[|s], ν[|s]) + μ(sᶜ) KL(μ[|sᶜ], ν[|sᶜ])`, in which `μ[|s]` is the measure
  `μ` conditioned on `s`.
-/

@[expose] public section

open MeasureTheory Set InformationTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

/-- **Chain rule for an event**: for finite measures `μ, ν` and an event `s`, `KL(μ, ν)` is the
Kullback-Leibler divergence between the laws of the indicator of `s` under `μ` and `ν`, plus
`μ(s) KL(μ[|s], ν[|s]) + μ(sᶜ) KL(μ[|sᶜ], ν[|sᶜ])`. -/
theorem klDiv_eq_klDiv_boolMeasure_add_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (Measure.boolMeasure (μ sᶜ) (μ s)) (Measure.boolMeasure (ν sᶜ) (ν s))
      + μ s * klDiv μ[|s] ν[|s] + μ sᶜ * klDiv μ[|sᶜ] ν[|sᶜ] := by
  have := Measure.isFiniteMeasure_boolMeasure (measure_ne_top μ sᶜ) (measure_ne_top μ s)
  have := Measure.isFiniteMeasure_boolMeasure (measure_ne_top ν sᶜ) (measure_ne_top ν s)
  rw [klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl μ ν hs,
    klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl _ _ (measurableSet_singleton true),
    Measure.restrict_boolMeasure_true, Measure.restrict_boolMeasure_true,
    Measure.restrict_boolMeasure_compl_true, Measure.restrict_boolMeasure_compl_true,
    klDiv_restrict_eq_add s (Measure.dirac true), klDiv_restrict_eq_add sᶜ (Measure.dirac false)]
  ring

end ProbabilityTheory
