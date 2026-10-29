/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.ProductMeasure

/-!
# Infinite product measures

## Main statements

* `MeasureTheory.integral_comp_eval_infinitePi`: the integral of a function of the coordinate `i`
  under `Measure.infinitePi μ` is its integral against `μ i`. This is the analogue of Mathlib's
  `MeasureTheory.integral_comp_eval` for finite products.
* `MeasureTheory.Measure.infinitePi_map_restrictLe`: the law of the coordinates `≤ n` under
  `Measure.infinitePi μ` is the finite product measure.
-/

@[expose] public section

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  {μ : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- The integral of a function of the coordinate `i` under `Measure.infinitePi μ` is its integral
against `μ i`. -/
lemma integral_comp_eval_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : ι}
    {f : X i → E} (hf : AEStronglyMeasurable f (μ i)) :
    ∫ x, f (x i) ∂Measure.infinitePi μ = ∫ x, f x ∂μ i := by
  rw [← (measurePreserving_eval_infinitePi μ i).map_eq, integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval_infinitePi μ i).map_eq]

/-- The law of the coordinates `≤ n` under the product measure `Measure.infinitePi μ` is the finite
product measure. -/
lemma Measure.infinitePi_map_restrictLe [Preorder ι] [LocallyFiniteOrderBot ι]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (n : ι) :
    (Measure.infinitePi μ).map (Preorder.restrictLe n) = Measure.pi fun i : Set.Iic n ↦ μ i := by
  rw [Preorder.restrictLe, Measure.infinitePi_map_restrict', Measure.infinitePi_eq_pi]

end MeasureTheory
