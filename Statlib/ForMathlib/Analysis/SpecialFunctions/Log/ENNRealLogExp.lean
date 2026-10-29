/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Bounds by the exponential of a supremum

## Main statements

* `EReal.le_exp_neg_biSup`: if `x ≤ exp (-f i)` for all `i` in a nonempty set `s`, then
  `x ≤ exp (-⨆ i ∈ s, f i)`.
-/

@[expose] public section

open scoped ENNReal

namespace EReal

/-- If `x ≤ exp (-f i)` for all `i` in a nonempty set `s`, then `x ≤ exp (-⨆ i ∈ s, f i)`. -/
lemma le_exp_neg_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → ℝ≥0∞}
    {x : ℝ≥0∞} (h : ∀ i ∈ s, x ≤ EReal.exp (-(f i : EReal))) :
    x ≤ EReal.exp (-((⨆ i ∈ s, f i : ℝ≥0∞) : EReal)) := by
  have h' : ∀ i ∈ s, (f i : EReal) ≤ -ENNReal.log x := fun i hi ↦ by
    have h := h i hi
    rwa [← ENNReal.exp_log x, EReal.exp_le_exp_iff, EReal.le_neg] at h
  obtain ⟨i₀, hi₀⟩ := hs
  rw [← ENNReal.exp_log x, EReal.exp_le_exp_iff, EReal.le_neg,
    ← EReal.coe_toENNReal ((EReal.coe_ennreal_nonneg _).trans (h' i₀ hi₀)),
    EReal.coe_ennreal_le_coe_ennreal_iff]
  refine iSup₂_le fun i hi ↦ ?_
  rw [← EReal.toENNReal_coe (x := f i)]
  exact EReal.toENNReal_le_toENNReal (h' i hi)

end EReal
