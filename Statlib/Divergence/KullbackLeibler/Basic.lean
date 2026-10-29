/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.KullbackLeibler.KLDivFun
public import Statlib.Divergence.FDiv.Convex
public import Statlib.Divergence.FDiv.Measurable

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence `klDiv` is defined in Mathlib (`InformationTheory.klDiv`).
This file relates it to the f-divergence for the divergence function `klDivFun`, and deduces
properties of `klDiv` from those of `fDiv`.

## Main statements

* `klDiv_eq_fDiv`: `klDiv μ ν = fDiv klDivFun μ ν` for finite measures `μ, ν`.
* `klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl`: `KL(μ, ν)` is the sum of the divergences
  between the restrictions to an event and to its complement.
* `measurable_klDiv`: measurability of `a ↦ klDiv (κ a) (η a)` for finite kernels `κ, η`.
* `klDiv_add_add_le`: `KL(μ₀ + μ₁, ν₀ + ν₁) ≤ KL(μ₀, ν₀) + KL(μ₁, ν₁)`.
* `klDiv_smul_add_smul_le`: **joint convexity** of the Kullback-Leibler divergence,
  `KL(a • μ₀ + b • μ₁, a • ν₀ + b • ν₁) ≤ a * KL(μ₀, ν₀) + b * KL(μ₁, ν₁)`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The Kullback-Leibler divergence between two finite measures is the f-divergence for the
divergence function `klDivFun`. -/
lemma klDiv_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = fDiv klDivFun μ ν := by
  classical
  rw [klDiv_eq_lintegral_klFun, fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun,
    lintegral_klDivFun_rnDeriv]

/-- The Kullback-Leibler divergence between two finite measures is the sum of the
Kullback-Leibler divergences between their restrictions to an event and to its complement. -/
lemma klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set α} (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  rw [klDiv_eq_fDiv, klDiv_eq_fDiv, klDiv_eq_fDiv,
    fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl _ _ hs]

/-- For finite kernels `κ, η`, the function `a ↦ klDiv (κ a) (η a)` is measurable. -/
lemma measurable_klDiv {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  simp_rw [klDiv_eq_fDiv]
  exact measurable_fDiv _ _

/-- The Kullback-Leibler divergence of the sum of two pairs of measures is at most the sum of the
divergences. -/
theorem klDiv_add_add_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] :
    klDiv (μ₀ + μ₁) (ν₀ + ν₁) ≤ klDiv μ₀ ν₀ + klDiv μ₁ ν₁ := by
  simp_rw [klDiv_eq_fDiv]
  exact fDiv_add_add_le _ _ _ _

/-- **Joint convexity** of the Kullback-Leibler divergence. -/
theorem klDiv_smul_add_smul_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (a b : ℝ≥0) :
    klDiv (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * klDiv μ₀ ν₀ + b * klDiv μ₁ ν₁ := by
  simp_rw [klDiv_eq_fDiv]
  exact fDiv_smul_add_smul_le _ _ _ _ a b

end ProbabilityTheory
