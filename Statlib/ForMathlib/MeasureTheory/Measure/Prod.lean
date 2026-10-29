/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Products of mutually singular measures

Complements to `Mathlib.MeasureTheory.Measure.Prod`.

## Main statements

* `MeasureTheory.Measure.MutuallySingular.prod_of_left`,
  `MeasureTheory.Measure.MutuallySingular.prod_of_right`: products of measures are mutually singular
  if one pair of factors is.
* `MeasureTheory.Measure.prod.instNeZero`: the product of two nonzero measures is nonzero.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- If `μ₁ ⟂ₘ ν₁`, then `μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂`. -/
lemma MutuallySingular.prod_of_left {μ₁ ν₁ : Measure α} (h : μ₁ ⟂ₘ ν₁) (μ₂ ν₂ : Measure β) :
    μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂ := by
  by_cases hμ₂ : SFinite μ₂
  swap; · simp [prod_eq_zero_of_not_sfinite hμ₂]
  by_cases hν₂ : SFinite ν₂
  swap; · simp [prod_eq_zero_of_not_sfinite hν₂]
  refine ⟨h.nullSet ×ˢ Set.univ, h.measurableSet_nullSet.prod .univ, ?_, ?_⟩
  · rw [prod_prod, h.measure_nullSet, zero_mul]
  · rw [show (h.nullSet ×ˢ Set.univ)ᶜ = h.nullSetᶜ ×ˢ (Set.univ : Set β) by ext; simp, prod_prod,
      h.measure_compl_nullSet, zero_mul]

/-- If `μ₂ ⟂ₘ ν₂`, then `μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂`. -/
lemma MutuallySingular.prod_of_right {μ₂ ν₂ : Measure β} (h : μ₂ ⟂ₘ ν₂) (μ₁ ν₁ : Measure α) :
    μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂ := by
  by_cases hμ₂ : SFinite μ₂
  swap; · simp [prod_eq_zero_of_not_sfinite hμ₂]
  by_cases hν₂ : SFinite ν₂
  swap; · simp [prod_eq_zero_of_not_sfinite hν₂]
  refine ⟨Set.univ ×ˢ h.nullSet, MeasurableSet.univ.prod h.measurableSet_nullSet, ?_, ?_⟩
  · rw [prod_prod, h.measure_nullSet, mul_zero]
  · rw [show (Set.univ ×ˢ h.nullSet)ᶜ = (Set.univ : Set α) ×ˢ h.nullSetᶜ by ext; simp, prod_prod,
      h.measure_compl_nullSet, mul_zero]

instance prod.instNeZero {μ : Measure α} {ν : Measure β} [SFinite ν] [NeZero μ] [NeZero ν] :
    NeZero (μ.prod ν) :=
  ⟨fun h ↦ by simpa [← Set.univ_prod_univ, prod_prod, NeZero.ne] using congr($h .univ)⟩

end MeasureTheory.Measure
