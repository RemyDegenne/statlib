/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.KullbackLeibler.KLDivFun
public import Statlib.Divergence.FDiv.Basic
public import Statlib.Divergence.FDiv.Measurable

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence `klDiv` is defined in Mathlib (`InformationTheory.klDiv`).
This file relates it to the f-divergence for the divergence function `klDivFun`.

## Main statements

* `klDiv_eq_fDiv`: `klDiv μ ν = fDiv klDivFun μ ν`
* `measurable_klDiv`: measurability of `a ↦ klDiv (κ a) (η a)` for finite kernels `κ, η`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma klDiv_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = fDiv klDivFun μ ν := by
  classical
  rw [klDiv_eq_lintegral_klFun, fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun,
    lintegral_klDivFun_rnDeriv]

lemma measurable_klDiv {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  simp_rw [klDiv_eq_fDiv]
  exact measurable_fDiv _ _

end ProbabilityTheory
