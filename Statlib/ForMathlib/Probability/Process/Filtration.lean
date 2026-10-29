/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Filtrations of finitely many coordinates

## Main statements

* `MeasureTheory.Filtration.iSup_piFinset_eq_pi`: for a family of finite sets `s n` covering the
  index set, the σ-algebras `Filtration.piFinset (s n)` of events depending only on the coordinates
  in `s n` generate the product σ-algebra.
* `MeasureTheory.Filtration.measurable_piLE_apply`: the coordinate `i` is measurable with respect
  to `Filtration.piLE j` for `i ≤ j`.
-/

@[expose] public section

open MeasurableSpace

namespace MeasureTheory.Filtration

/-- The σ-algebras of events depending only on the coordinates in `s n`, for a family of finite sets
`s n` covering the index set, generate the product σ-algebra. -/
lemma iSup_piFinset_eq_pi {ι κ : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {s : κ → Finset ι} (hs : ∀ i, ∃ n, i ∈ s n) :
    ⨆ n, piFinset (X := X) (s n) = pi := by
  refine le_antisymm (iSup_le fun n ↦ piFinset.le (s n)) (iSup_le fun i ↦ ?_)
  obtain ⟨n, hn⟩ := hs i
  -- the evaluation at `i` is the evaluation at `⟨i, hn⟩` of the restriction to `s n`
  exact le_iSup_of_le n
    ((measurable_pi_apply (⟨i, hn⟩ : s n)).comp (comap_measurable (s n).restrict)).comap_le

/-- The coordinate `i` of `ω : Π i, X i` is measurable with respect to `Filtration.piLE j` for
`i ≤ j`. -/
lemma measurable_piLE_apply {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {i j : ι} (hij : i ≤ j) :
    Measurable[piLE (X := X) j] fun ω ↦ ω i :=
  (measurable_pi_apply (⟨i, hij⟩ : Set.Iic j)).comp (comap_measurable (Preorder.restrictLe j))

end MeasureTheory.Filtration
