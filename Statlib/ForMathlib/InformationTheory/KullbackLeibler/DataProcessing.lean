/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Data-processing inequalities for the Kullback-Leibler divergence

Consequences of Mathlib's data-processing inequality for measurable maps, `klDiv_map_le`.

## Main statements

* `klDiv_fst_le`, `klDiv_snd_le`: the divergence between marginals is at most the divergence
  between the joint measures.
* `le_klDiv_compProd`: `klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)` for Markov kernels `κ, η`.
* `klDiv_comp_le_compProd`: `klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

lemma klDiv_fst_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.fst ν.fst ≤ klDiv μ ν :=
  klDiv_map_le μ ν measurable_fst

lemma klDiv_snd_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.snd ν.snd ≤ klDiv μ ν :=
  klDiv_map_le μ ν measurable_snd

lemma le_klDiv_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simpa using klDiv_fst_le (μ ⊗ₘ κ) (ν ⊗ₘ η)

lemma klDiv_comp_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simpa using klDiv_snd_le (μ ⊗ₘ κ) (ν ⊗ₘ η)

end InformationTheory
