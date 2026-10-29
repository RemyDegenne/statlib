/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Stopping times that never take the value `⊤`

## Main statements

* `MeasureTheory.measurable_of_isStoppingTime`: a stopping time with values in a countable index
  type `ι` is measurable.
* `MeasureTheory.trim_stoppingTime_eq_withDensity`: for a filtration `ℱ` indexed by `ℕ`, if the
  restriction of `P` to `ℱ n` has density `L n` with respect to the restriction of `Q` for all `n`,
  then the restriction of `P` to the σ-algebra of a stopping time `τ` has density
  `ω ↦ L (τ ω) ω`.

## Implementation notes

The stopping time `τ` takes values in the index type `ι` (`ℕ` for the second statement) and the
stopping time property is stated for its coercion `fun ω ↦ (τ ω : WithTop ι)`, as required by
`MeasureTheory.IsStoppingTime`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- A stopping time with values in a countable index type `ι` is measurable. -/
lemma measurable_of_isStoppingTime {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [PartialOrder ι]
    [Countable ι] [MeasurableSpace ι] {ℱ : Filtration ι mΩ} {τ : Ω → ι}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ι))) :
    Measurable τ := by
  refine measurable_to_countable' fun n ↦ ?_
  have h := ℱ.le n _ (hτ.measurableSet_eq_of_countable n)
  simpa [Set.preimage, Set.mem_singleton_iff] using h

/-- Let `τ` be a stopping time with values in `ℕ`. If for all `n`, the restriction of `P` to the
σ-algebra `ℱ n` has density `L n` with respect to the restriction of `Q`, then the restriction of
`P` to the σ-algebra of `τ` has density `ω ↦ L (τ ω) ω` with respect to the restriction of `Q`. -/
lemma trim_stoppingTime_eq_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℕ mΩ} {P Q : Measure Ω} {L : ℕ → Ω → ℝ≥0∞}
    (hL : ∀ n, Measurable[ℱ n] (L n))
    (hPQ : ∀ n, P.trim (ℱ.le n) = (Q.trim (ℱ.le n)).withDensity (L n)) {τ : Ω → ℕ}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) :
    P.trim hτ.measurableSpace_le
      = (Q.trim hτ.measurableSpace_le).withDensity fun ω ↦ L (τ ω) ω := by
  have hL_τ : Measurable[hτ.measurableSpace] fun ω ↦ L (τ ω) ω :=
    measurable_stoppedValue (StronglyAdapted.isStronglyProgressive_of_discrete
      fun n ↦ (hL n).stronglyMeasurable) hτ
  refine @Measure.ext _ hτ.measurableSpace _ _ fun E hE ↦ ?_
  -- `E` is the disjoint union of the events `E ∩ {τ = n}`, which are measurable at time `n`
  have h_meas (n : ℕ) : MeasurableSet[ℱ n] (E ∩ {ω | τ ω = n}) := by
    simpa using (hτ.measurableSet_inter_eq_iff E n).mp
      (hE.inter (hτ.measurableSet_eq_of_countable' n))
  have h_meas' (n : ℕ) : MeasurableSet (E ∩ {ω | τ ω = n}) := ℱ.le n _ (h_meas n)
  have h_union : E = ⋃ n, E ∩ {ω | τ ω = n} := by
    ext ω; simp
  have h_disj : Pairwise (Function.onFun Disjoint fun n ↦ E ∩ {ω | τ ω = n}) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hnm ?_
    rw [← hω.2, ← hω'.2]
  rw [trim_measurableSet_eq _ hE, withDensity_apply _ hE, setLIntegral_trim _ hL_τ hE, h_union,
    measure_iUnion h_disj h_meas', lintegral_iUnion h_meas' h_disj]
  congr with n
  have h_n := congr($(hPQ n) (E ∩ {ω | τ ω = n}))
  rw [trim_measurableSet_eq _ (h_meas n), withDensity_apply _ (h_meas n),
    setLIntegral_trim _ (hL n) (h_meas n)] at h_n
  rw [h_n]
  refine setLIntegral_congr_fun (h_meas' n) fun ω hω ↦ ?_
  rw [hω.2]

end MeasureTheory
