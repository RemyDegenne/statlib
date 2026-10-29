/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.ForMathlib.MeasureTheory.Constructions.Pi
public import Statlib.ForMathlib.MeasureTheory.Measure.Prod
public import Statlib.Divergence.KullbackLeibler.CondKL
public import Statlib.Divergence.Renyi.DataProcessing

/-!
# Tensorization of the Rényi divergence

The Rényi divergence between product measures is the sum of the Rényi divergences between the
factors.

## Main statements

* `ProbabilityTheory.renyiDiv_prod`: `Rₐ(μ₁ × μ₂, ν₁ × ν₂) = Rₐ(μ₁, ν₁) + Rₐ(μ₂, ν₂)` for finite
  measures with `μ₁, μ₂ ≠ 0` and `0 ≤ a`.
* `ProbabilityTheory.renyiDiv_pi`: tensorization for finite products.
* `ProbabilityTheory.renyiDiv_pi_const`: `Rₐ(μ^⊗ι, ν^⊗ι) = |ι| * Rₐ(μ, ν)`.

## Implementation notes

The hypothesis `μ₁, μ₂ ≠ 0` cannot be dropped: for `1 < a`, `Rₐ(0, ν) = 0` for all finite `ν`, so
for `μ₁ = 0` the left-hand side vanishes while the right-hand side is `Rₐ(μ₂, ν₂)`.

For two factors, the order `0` is obtained from the positive orders by taking the limit `a → 0⁺`
(`tendsto_renyiDiv_nhdsGT_zero`). Countable products are treated in
`Statlib.Divergence.Renyi.ProdCountable`.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), Theorem 28.
-/

@[expose] public section

open Real MeasureTheory Filter InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {a : ℝ}

/-- `renyiDiv_prod` for probability measures. -/
private lemma renyiDiv_prod_of_isProbabilityMeasure (ha : 0 < a) (μ₁ ν₁ : Measure α)
    (μ₂ ν₂ : Measure β) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) = renyiDiv a μ₁ ν₁ + renyiDiv a μ₂ ν₂ := by
  rcases eq_or_ne a 1 with rfl | ha1
  · simp_rw [renyiDiv_one_of_isProbabilityMeasure]
    exact klDiv_prod_two
  have h_le₁ : renyiDiv a μ₁ ν₁ ≤ renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) := by
    simpa using renyiDiv_map_le ha.le (μ₁.prod μ₂) (ν₁.prod ν₂) measurable_fst
  have h_le₂ : renyiDiv a μ₂ ν₂ ≤ renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) := by
    simpa using renyiDiv_map_le ha.le (μ₁.prod μ₂) (ν₁.prod ν₂) measurable_snd
  by_cases h₁ : renyiDiv a μ₁ ν₁ = ∞
  · rw [h₁, top_add]
    exact eq_top_iff.mpr (h₁ ▸ h_le₁)
  by_cases h₂ : renyiDiv a μ₂ ν₂ = ∞
  · rw [h₂, add_top]
    exact eq_top_iff.mpr (h₂ ▸ h_le₂)
  have h_prod : renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) ≠ ∞ := by
    rcases ha1.lt_or_gt with ha1' | ha1'
    · rw [ne_eq, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha.le ha1',
        ← integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha.ne'
          (integrable_rpow_rnDeriv_of_lt_one ha.le ha1'), integral_rpow_rnDeriv_prod]
      exact mul_pos (integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha h₁)
        (integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha h₂)
    · have h₁' := (renyiDiv_ne_top_iff_of_one_lt ha1').mp h₁
      have h₂' := (renyiDiv_ne_top_iff_of_one_lt ha1').mp h₂
      rw [renyiDiv_ne_top_iff_of_one_lt ha1']
      refine ⟨(h₁'.1.mul_prod h₂'.1).congr ?_, h₁'.2.prod h₂'.2⟩
      filter_upwards [Measure.rnDeriv_prod μ₁ ν₁ μ₂ ν₂] with p hp
      rw [hp, ENNReal.toReal_mul, mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  rw [← ENNReal.ofReal_toReal h_prod, ← ENNReal.ofReal_toReal h₁, ← ENNReal.ofReal_toReal h₂,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha ha1 h_prod,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha ha1 h₁,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha ha1 h₂, integral_rpow_rnDeriv_prod,
    log_mul (integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha h₁).ne'
      (integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha h₂).ne', mul_add]

/-- `renyiDiv_prod` for `0 < a`. -/
private lemma renyiDiv_prod_of_pos (ha : 0 < a) (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsFiniteMeasure μ₁] [NeZero μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [NeZero μ₂]
    [IsFiniteMeasure ν₂] :
    renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) = renyiDiv a μ₁ ν₁ + renyiDiv a μ₂ ν₂ := by
  rcases eq_zero_or_neZero ν₁ with rfl | _
  · simp [renyiDiv_zero_measure_right ha.le]
  rcases eq_zero_or_neZero ν₂ with rfl | _
  · simp [renyiDiv_zero_measure_right ha.le]
  -- reduce to probability measures by normalizing
  rw [renyiDiv_eq_renyiDiv_inv_smul ha.le (μ := μ₁), renyiDiv_eq_renyiDiv_inv_smul ha.le (μ := μ₂),
    ← renyiDiv_prod_of_isProbabilityMeasure ha, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    renyiDiv_smul_smul ha.le]
  all_goals simp [ENNReal.mul_eq_top, NeZero.ne, measure_ne_top]

/-- **Tensorization** of the Rényi divergence: for finite measures with `μ₁, μ₂ ≠ 0` and `0 ≤ a`,
`Rₐ(μ₁ × μ₂, ν₁ × ν₂) = Rₐ(μ₁, ν₁) + Rₐ(μ₂, ν₂)`. -/
theorem renyiDiv_prod (ha : 0 ≤ a) (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsFiniteMeasure μ₁] [NeZero μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [NeZero μ₂]
    [IsFiniteMeasure ν₂] :
    renyiDiv a (μ₁.prod μ₂) (ν₁.prod ν₂) = renyiDiv a μ₁ ν₁ + renyiDiv a μ₂ ν₂ := by
  rcases ha.eq_or_lt with rfl | ha
  · exact tendsto_nhds_unique tendsto_renyiDiv_nhdsGT_zero
      ((tendsto_renyiDiv_nhdsGT_zero.add tendsto_renyiDiv_nhdsGT_zero).congr'
        (eventually_nhdsWithin_of_forall fun _ hb ↦ (renyiDiv_prod_of_pos hb _ _ _ _).symm))
  exact renyiDiv_prod_of_pos ha μ₁ ν₁ μ₂ ν₂

universe u

/-- **Tensorization** of the Rényi divergence for finite products of finite measures, with
`μ i ≠ 0` and `0 ≤ a`: `Rₐ(∏ μ i, ∏ ν i) = ∑ i, Rₐ(μ i, ν i)`. -/
theorem renyiDiv_pi (ha : 0 ≤ a) {ι : Type*} [Fintype ι] {β : ι → Type u}
    [∀ i, MeasurableSpace (β i)] {μ ν : (i : ι) → Measure (β i)} [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NeZero (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    renyiDiv a (Measure.pi μ) (Measure.pi ν) = ∑ i, renyiDiv a (μ i) (ν i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {β : ι → Type u}
    [(i : ι) → MeasurableSpace (β i)] {μ ν : (i : ι) → Measure (β i)}
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NeZero (μ i)] [∀ i, IsFiniteMeasure (ν i)],
    renyiDiv a (Measure.pi μ) (Measure.pi ν) = ∑ i, renyiDiv a (μ i) (ν i)) ?_ ?_ ?_ ι
  · intro ι ι' hι' e h β _ μ ν _ _ _
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    specialize h (β := fun i ↦ β (e i)) (μ := fun i ↦ μ (e i)) (ν := fun i ↦ ν (e i))
    rw [Fintype.sum_equiv e.symm _ (fun i ↦ renyiDiv a (μ (e i)) (ν (e i)))
      (fun i ↦ by rw [Equiv.apply_symm_apply]), ← h, ← Measure.pi_map_piCongrLeft e μ,
      ← Measure.pi_map_piCongrLeft e ν,
      renyiDiv_map_measurableEmbedding ha _ _ (MeasurableEquiv.measurableEmbedding _)]
  · intro β _ μ ν _ _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, renyiDiv_self, Finset.univ_eq_empty,
      Finset.sum_empty]
  · intro ι hι ind_h β _ μ ν _ _ _
    specialize ind_h (β := fun i ↦ β i) (μ := fun i ↦ μ i) (ν := fun i ↦ ν i)
    rw [Fintype.sum_option, add_comm, ← ind_h, ← renyiDiv_prod ha,
      ← Measure.pi_map_piOptionEquivProd μ, ← Measure.pi_map_piOptionEquivProd ν,
      renyiDiv_map_measurableEmbedding ha _ _ (MeasurableEquiv.measurableEmbedding _)]

/-- **Tensorization** of the Rényi divergence for powers of finite measures, with `μ ≠ 0` and
`0 ≤ a`: `Rₐ(μ^⊗ι, ν^⊗ι) = |ι| * Rₐ(μ, ν)`. -/
theorem renyiDiv_pi_const (ha : 0 ≤ a) {ι : Type*} [Fintype ι] [IsFiniteMeasure μ] [NeZero μ]
    [IsFiniteMeasure ν] :
    renyiDiv a (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν))
      = Fintype.card ι * renyiDiv a μ ν := by
  rw [renyiDiv_pi ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Tensorization** of the Rényi divergence for powers of finite measures, for the real value:
`Rₐ(μ^⊗ι, ν^⊗ι) = |ι| * Rₐ(μ, ν)`. -/
lemma toReal_renyiDiv_pi_const (ha : 0 ≤ a) {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    [NeZero μ] [IsFiniteMeasure ν] :
    (renyiDiv a (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν))).toReal
      = Fintype.card ι * (renyiDiv a μ ν).toReal := by
  rw [renyiDiv_pi_const ha, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end ProbabilityTheory
