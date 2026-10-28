/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.CompProd

/-!
# Joint convexity of f-divergences

## Main statements

* `fDiv_add_add_le`: `fDiv f (μ₀ + μ₁) (ν₀ + ν₁) ≤ fDiv f μ₀ ν₀ + fDiv f μ₁ ν₁`.
* `fDiv_smul_add_smul_le`: **joint convexity** of f-divergences,
  `fDiv f (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * fDiv f μ₀ ν₀ + b * fDiv f μ₁ ν₁`.

Both are proved by embedding the measures in `Bool × α` and applying the data-processing
inequality to the projection `Prod.snd`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {f : DivFunction}

/-- The f-divergence of the sum of two pairs of measures is at most the sum of the
f-divergences. -/
theorem fDiv_add_add_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] :
    fDiv f (μ₀ + μ₁) (ν₀ + ν₁) ≤ fDiv f μ₀ ν₀ + fDiv f μ₁ ν₁ := by
  -- we embed the measures in `Bool × α` and use the data-processing inequality for `Prod.snd`
  let P : Measure (Bool × α) := μ₀.map (Prod.mk false) + μ₁.map (Prod.mk true)
  let Q : Measure (Bool × α) := ν₀.map (Prod.mk false) + ν₁.map (Prod.mk true)
  have h_snd (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).snd = ξ₀ + ξ₁ := by
    rw [Measure.snd_add, Measure.snd, Measure.snd,
      Measure.map_map measurable_snd measurable_prodMk_left,
      Measure.map_map measurable_snd measurable_prodMk_left]
    simp [Function.comp_def]
  -- `P` and `Q` restricted to `{false} × α` and to its complement are the two pairs of measures
  set s : Set (Bool × α) := {p | p.1 = false}
  have hs : MeasurableSet s := measurable_fst (measurableSet_singleton false)
  have h_restrict (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).restrict s = ξ₀.map (Prod.mk false) := by
    rw [Measure.restrict_add, Measure.restrict_map measurable_prodMk_left hs,
      Measure.restrict_map measurable_prodMk_left hs]
    simp [s, preimage]
  have h_restrict_compl (ξ₀ ξ₁ : Measure α) :
      (ξ₀.map (Prod.mk false) + ξ₁.map (Prod.mk true)).restrict sᶜ = ξ₁.map (Prod.mk true) := by
    rw [Measure.restrict_add, Measure.restrict_map measurable_prodMk_left hs.compl,
      Measure.restrict_map measurable_prodMk_left hs.compl]
    simp [s, preimage]
  calc fDiv f (μ₀ + μ₁) (ν₀ + ν₁) = fDiv f P.snd Q.snd := by rw [h_snd, h_snd]
  _ ≤ fDiv f P Q := fDiv_snd_le P Q
  _ = fDiv f μ₀ ν₀ + fDiv f μ₁ ν₁ := by
    rw [fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl P Q hs, h_restrict, h_restrict,
      h_restrict_compl, h_restrict_compl,
      fDiv_map_measurableEmbedding (measurableEmbedding_prodMk_left false),
      fDiv_map_measurableEmbedding (measurableEmbedding_prodMk_left true)]

/-- **Joint convexity** of f-divergences. -/
theorem fDiv_smul_add_smul_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (a b : ℝ≥0) :
    fDiv f (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * fDiv f μ₀ ν₀ + b * fDiv f μ₁ ν₁ := by
  rw [← fDiv_smul_smul, ← fDiv_smul_smul]
  exact fDiv_add_add_le _ _ _ _

end ProbabilityTheory
