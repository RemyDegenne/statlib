/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tonelli's theorem for finite products of functions

Lebesgue integral versions of Mathlib's `MeasureTheory.integral_fin_nat_prod_eq_prod` and
`MeasureTheory.integral_fintype_prod_eq_prod`.

## Main statements

* `MeasureTheory.lintegral_fintype_prod_eq_prod`: **Tonelli's theorem** for a product of functions
  of each coordinate, `∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i)`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- **Tonelli's theorem** for a product of functions of each coordinate, on a product space indexed
by `Fin n`. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ)
      _ = ∫⁻ y : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            f 0 y.1 * ∏ j, f (Fin.succAbove 0 j) (y.2 j)
            ∂((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        refine lintegral_congr fun y ↦ ?_
        simp only [Fin.prod_univ_succAbove _ 0, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ j, ∫⁻ x, f (Fin.succAbove 0 j) x ∂(μ (Fin.succAbove 0 j)) := by
        have h_meas : AEMeasurable (fun y : (j : Fin n) → E (Fin.succAbove 0 j) ↦
            ∏ j, f (Fin.succAbove 0 j) (y j)) (Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) :=
          Finset.aemeasurable_fun_prod _ fun j _ ↦
            (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ j)
        rw [lintegral_prod_mul (hf 0) h_meas, ih fun i ↦ hf _]
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) :=
        (Fin.prod_univ_succAbove (fun i ↦ ∫⁻ x, f i x ∂(μ i)) 0).symm

/-- **Tonelli's theorem** for a product of functions of each coordinate, on a product space indexed
by a finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod fun i ↦ hf _

end MeasureTheory
