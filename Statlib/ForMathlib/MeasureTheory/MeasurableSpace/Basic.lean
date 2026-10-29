/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurable spaces

## Main statements

* `MeasurableSpace.finite_setOf_measurableSet_comap`: if `g` has finite range, the σ-algebra
  `mβ.comap g` has finitely many measurable sets.
-/

@[expose] public section

open Set MeasureTheory

namespace MeasurableSpace

variable {α β : Type*} {mβ : MeasurableSpace β}

/-- The σ-algebra induced by a map with finite range has finitely many measurable sets. -/
lemma finite_setOf_measurableSet_comap {g : α → β} (hg : (range g).Finite) :
    {s | MeasurableSet[mβ.comap g] s}.Finite := by
  refine (hg.finite_subsets.image fun t ↦ g ⁻¹' t).subset ?_
  rintro s ⟨t, -, rfl⟩
  exact ⟨t ∩ range g, inter_subset_right, preimage_inter_range⟩

end MeasurableSpace
