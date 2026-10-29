/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Chernoff
public import Statlib.Divergence.Renyi.Prod

/-!
# Chernoff divergence of product measures

The Chernoff divergence `Cₐ(μ, ν) = ⨅ ξ, max (Rₐ(ξ, μ)) (Rₐ(ξ, ν))` is subadditive on finite
products of finite measures: taking product measures `∏ ξ i` in the infimum and using the
tensorization of the Rényi divergence (`renyiDiv_pi`) gives
`Cₐ(∏ μ i, ∏ ν i) ≤ ∑ i, Cₐ(μ i, ν i)`.

## Main statements

* `ProbabilityTheory.chernoffDiv_pi_le`: `Cₐ(∏ μ i, ∏ ν i) ≤ ∑ i, Cₐ(μ i, ν i)` for `0 ≤ a` and
  finite measures.
* `ProbabilityTheory.chernoffDiv_pi_const_le`: `Cₐ(μ^⊗ι, ν^⊗ι) ≤ |ι| * Cₐ(μ, ν)`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- **Subadditivity of the Chernoff divergence on products**: for `0 ≤ a` and finite measures,
`Cₐ(∏ μ i, ∏ ν i) ≤ ∑ i, Cₐ(μ i, ν i)`. -/
theorem chernoffDiv_pi_le (ha : 0 ≤ a) {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {μ ν : (i : ι) → Measure (β i)} [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] :
    chernoffDiv a (Measure.pi μ) (Measure.pi ν) ≤ ∑ i, chernoffDiv a (μ i) (ν i) := by
  -- for `ε > 0`, choose for each `i` a probability measure `ξ i` which is `ε / |ι|`-optimal in the
  -- infimum defining `Cₐ(μ i, ν i)`, and use the product measure `∏ ξ i`
  refine ENNReal.le_of_forall_pos_le_add fun ε hε h_lt ↦ ?_
  have h_ex i : ∃ ξ : Measure (β i), ∃ _ : IsProbabilityMeasure ξ,
      max (renyiDiv a ξ (μ i)) (renyiDiv a ξ (ν i))
        < chernoffDiv a (μ i) (ν i) + ε / Fintype.card ι := by
    have h_ne : chernoffDiv a (μ i) (ν i) ≠ ∞ :=
      (ENNReal.sum_lt_top.mp h_lt i (Finset.mem_univ i)).ne
    simpa only [chernoffDiv, iInf_lt_iff] using ENNReal.lt_add_right h_ne
      (ENNReal.div_pos (by simpa using hε.ne') (ENNReal.natCast_ne_top _)).ne'
  choose ξ hξ h_lt_ξ using h_ex
  calc chernoffDiv a (Measure.pi μ) (Measure.pi ν)
      ≤ max (renyiDiv a (Measure.pi ξ) (Measure.pi μ)) (renyiDiv a (Measure.pi ξ) (Measure.pi ν)) :=
        iInf₂_le (Measure.pi ξ) (by infer_instance)
    _ = max (∑ i, renyiDiv a (ξ i) (μ i)) (∑ i, renyiDiv a (ξ i) (ν i)) := by
        rw [renyiDiv_pi ha, renyiDiv_pi ha]
    _ ≤ ∑ i, max (renyiDiv a (ξ i) (μ i)) (renyiDiv a (ξ i) (ν i)) :=
        max_le (Finset.sum_le_sum fun _ _ ↦ le_max_left _ _)
          (Finset.sum_le_sum fun _ _ ↦ le_max_right _ _)
    _ ≤ ∑ i, (chernoffDiv a (μ i) (ν i) + ε / Fintype.card ι) :=
        Finset.sum_le_sum fun i _ ↦ (h_lt_ξ i).le
    _ ≤ ∑ i, chernoffDiv a (μ i) (ν i) + ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        exact ENNReal.mul_div_le

/-- **Subadditivity of the Chernoff divergence on powers**: for `0 ≤ a` and finite measures,
`Cₐ(μ^⊗ι, ν^⊗ι) ≤ |ι| * Cₐ(μ, ν)`. -/
theorem chernoffDiv_pi_const_le (ha : 0 ≤ a) {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    chernoffDiv a (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : ι ↦ ν)
      ≤ Fintype.card ι * chernoffDiv a μ ν := by
  simpa [Finset.sum_const, nsmul_eq_mul] using
    chernoffDiv_pi_le ha (μ := fun _ : ι ↦ μ) (ν := fun _ : ι ↦ ν)

end ProbabilityTheory
