/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Compositions of measures with parallel compositions of kernels

Complements to `Mathlib.Probability.Kernel.Composition.Lemmas`.

## Main statements

* `MeasureTheory.Measure.fst_parallelComp_comp`, `MeasureTheory.Measure.snd_parallelComp_comp`:
  the marginals of `(κ ∥ₖ η) ∘ₘ ρ` are `κ ∘ₘ ρ.fst` and `η ∘ₘ ρ.snd` (for Markov kernels `η`,
  resp. `κ`).
* `MeasureTheory.Measure.prod_comp_comp`: `(κ ∘ₘ μ).prod (η ∘ₘ ν) = (κ ∥ₖ η) ∘ₘ (μ.prod ν)`.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- The first marginal of `(κ ∥ₖ η) ∘ₘ ρ` is `κ ∘ₘ ρ.fst` when `η` is a Markov kernel. -/
lemma fst_parallelComp_comp (ρ : Measure (α × β)) (κ : Kernel α γ) [IsSFiniteKernel κ]
    (η : Kernel β δ) [IsMarkovKernel η] :
    ((κ ∥ₖ η) ∘ₘ ρ).fst = κ ∘ₘ ρ.fst := by
  ext s hs
  rw [fst_apply hs, bind_apply (measurable_fst hs) (Kernel.aemeasurable _),
    bind_apply hs (Kernel.aemeasurable _), Measure.fst,
    lintegral_map (κ.measurable_coe hs) measurable_fst]
  congr with p
  rw [show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set δ) by ext; simp,
    Kernel.parallelComp_apply_prod]
  simp

/-- The second marginal of `(κ ∥ₖ η) ∘ₘ ρ` is `η ∘ₘ ρ.snd` when `κ` is a Markov kernel. -/
lemma snd_parallelComp_comp (ρ : Measure (α × β)) (κ : Kernel α γ) [IsMarkovKernel κ]
    (η : Kernel β δ) [IsSFiniteKernel η] :
    ((κ ∥ₖ η) ∘ₘ ρ).snd = η ∘ₘ ρ.snd := by
  ext s hs
  rw [snd_apply hs, bind_apply (measurable_snd hs) (Kernel.aemeasurable _),
    bind_apply hs (Kernel.aemeasurable _), Measure.snd,
    lintegral_map (η.measurable_coe hs) measurable_snd]
  congr with p
  rw [show Prod.snd ⁻¹' s = (Set.univ : Set γ) ×ˢ s by ext; simp,
    Kernel.parallelComp_apply_prod]
  simp

/-- The product of `κ ∘ₘ μ` and `η ∘ₘ ν` is the composition of `μ.prod ν` with `κ ∥ₖ η`. -/
lemma prod_comp_comp (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : Kernel α γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η] :
    (κ ∘ₘ μ).prod (η ∘ₘ ν) = (κ ∥ₖ η) ∘ₘ (μ.prod ν) := by
  rw [prod_comp_right, prod_comp_left, comp_assoc, Kernel.parallelComp_comp_parallelComp,
    Kernel.id_comp, Kernel.comp_id]

end MeasureTheory.Measure
