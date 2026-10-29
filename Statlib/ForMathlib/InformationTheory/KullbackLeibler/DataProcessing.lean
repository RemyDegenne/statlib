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
* `klDiv_map_measurableEmbedding`: the divergence is invariant under measurable embeddings, and in
  particular under the swap of the coordinates of a product space (`klDiv_map_swap`).
* `klDiv_trim_mono`: the divergence between the restrictions of two finite measures to a
  sub-σ-algebra is monotone in the sub-σ-algebra. For instance, the divergence between the
  restrictions to the σ-algebras of stopping times `σ ≤ τ` is monotone, by
  `MeasureTheory.IsStoppingTime.measurableSpace_mono`.

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

/-- The Kullback-Leibler divergence is invariant under measurable embeddings. -/
lemma klDiv_map_measurableEmbedding (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : MeasurableEmbedding f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hf.measurable) ?_
  cases isEmpty_or_nonempty α
  · simp [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty ν]
  calc klDiv μ ν = klDiv ((μ.map f).map hf.invFun) ((ν.map f).map hf.invFun) := by
        simp [Measure.map_map hf.measurable_invFun hf.measurable, hf.leftInverse_invFun.id]
  _ ≤ klDiv (μ.map f) (ν.map f) := klDiv_map_le _ _ hf.measurable_invFun

/-- The Kullback-Leibler divergence is invariant under swapping the coordinates. -/
lemma klDiv_map_swap (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν :=
  klDiv_map_measurableEmbedding μ ν MeasurableEquiv.prodComm.measurableEmbedding

/-- The Kullback-Leibler divergence between the restrictions of two finite measures to a
sub-σ-algebra is monotone in the sub-σ-algebra. -/
lemma klDiv_trim_mono (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {m₁ m₂ : MeasurableSpace α} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mα) :
    klDiv (μ.trim (h₁₂.trans h₂)) (ν.trim (h₁₂.trans h₂)) ≤ klDiv (μ.trim h₂) (ν.trim h₂) := by
  rw [← trim_trim (μ := μ) (hm₁₂ := h₁₂), ← trim_trim (μ := ν) (hm₁₂ := h₁₂)]
  exact klDiv_trim_le _ _ h₁₂

end InformationTheory
