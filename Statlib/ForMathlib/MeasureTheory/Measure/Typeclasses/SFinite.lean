/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Atoms of maximal mass

## Main statements

* `MeasureTheory.Measure.exists_forall_measure_singleton_le`: a finite measure on a nonempty space
  with measurable singletons has an atom of maximal mass.
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory.Measure

/-- A finite measure has an atom of maximal mass. -/
lemma exists_forall_measure_singleton_le {α : Type*} {mα : MeasurableSpace α}
    [MeasurableSingletonClass α] [Nonempty α] (μ : Measure α) [IsFiniteMeasure μ] :
    ∃ z, ∀ y, μ {y} ≤ μ {z} := by
  by_cases! h : ∀ y, μ {y} = 0
  · exact ⟨Classical.arbitrary α, fun y ↦ by simp [h y]⟩
  obtain ⟨y₀, hy₀⟩ := h
  -- only finitely many atoms have mass at least `μ {y₀}`, and we take the largest of them
  have h_fin : {y | μ {y₀} ≤ μ {y}}.Finite :=
    finite_const_le_meas_of_disjoint_iUnion μ (pos_iff_ne_zero.mpr hy₀) measurableSet_singleton
      (fun _ _ hij ↦ disjoint_singleton.mpr hij) (measure_ne_top μ _)
  obtain ⟨z, hz, hz_max⟩ := exists_max_image _ (fun y ↦ μ {y}) h_fin ⟨y₀, le_refl (μ {y₀})⟩
  refine ⟨z, fun y ↦ ?_⟩
  by_cases hy : μ {y₀} ≤ μ {y}
  · exact hz_max y hy
  · exact (not_le.mp hy).le.trans hz

end MeasureTheory.Measure
