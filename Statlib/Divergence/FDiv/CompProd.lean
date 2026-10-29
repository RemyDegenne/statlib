/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Statlib.Divergence.FDiv.Trim
public import Statlib.ForMathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# f-Divergences of composition-products and data-processing inequalities

## Main statements

* `fDiv_compProd_left`: `fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν` for a Markov kernel `κ`.
* `fDiv_prod_left`: `fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν` for a probability measure `ξ`.
* `fDiv_prod_right`: `fDiv f (ξ.prod μ) (ξ.prod ν) = ξ univ * fDiv f μ ν` for a finite measure `ξ`.
* `fDiv_comp_right_le`: **data-processing inequality**,
  `fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν` for a Markov kernel `κ`.
* `fDiv_fst_le`, `fDiv_snd_le`, `le_fDiv_compProd`, `fDiv_comp_le_compProd`: other forms of the
  data-processing inequality.
* `fDiv_comp_eq_of_comp_eq_id`: a kernel with a Markov left inverse preserves f-divergences.
  For example, a kernel `κ : α → α × β` with `κ.fst = Kernel.id` (`fDiv_comp_eq_of_fst_eq_id`).

The data-processing inequalities follow from the data-processing inequality for measurable maps
`fDiv_map_le`, which rests on Jensen's inequality for the conditional Lebesgue expectation. They
hold without any assumption on the measurable spaces.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), which also proves these inequalities through
the disintegration of the composition-product, under assumptions on the measurable spaces.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : DivFunction}

@[simp]
lemma fDiv_compProd_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine fDiv_congr_measure ?_ ?_
  · have h_eq : (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) x))
        =ᵐ[ν ⊗ₘ κ] fun x ↦ f ((∂μ/∂ν) x.1) := by
      filter_upwards [rnDeriv_measure_compProd_left μ ν κ] with x hx
      rw [hx]
    rw [lintegral_congr_ae h_eq, Measure.lintegral_compProd]
    · simp
    · exact DivFunction.measurable_comp_rnDeriv.comp measurable_fst
  · rw [singularPart_compProd_left, Measure.compProd_apply_univ]

/-- The f-divergence is invariant under taking the product with a probability measure. -/
lemma fDiv_prod_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure β) [IsProbabilityMeasure ξ] :
    fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν := by
  simpa [Measure.compProd_const] using fDiv_compProd_left (f := f) μ ν (Kernel.const α ξ)

/-- The f-divergence between two products with the same first factor `ξ` is the f-divergence
between the second factors, multiplied by the mass of `ξ`. -/
lemma fDiv_prod_right (ξ : Measure β) [IsFiniteMeasure ξ] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    fDiv f (ξ.prod μ) (ξ.prod ν) = ξ .univ * fDiv f μ ν := by
  rcases eq_zero_or_neZero ξ with rfl | hξ
  · simp
  -- write `ξ = c • ξ'` for a probability measure `ξ'`, then swap the factors
  set c : ℝ≥0 := (ξ .univ).toNNReal
  have hc : (c : ℝ≥0∞) = ξ .univ := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hc0 : c ≠ 0 := by
    rw [← ENNReal.coe_ne_zero, hc]
    exact NeZero.ne _
  have : IsProbabilityMeasure (c⁻¹ • ξ) := ⟨by
    rw [Measure.smul_apply, ← hc, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hc0,
      ENNReal.inv_mul_cancel (by simpa using hc0) ENNReal.coe_ne_top]⟩
  have h_prod (ρ : Measure α) [SFinite ρ] : ξ.prod ρ = c • (c⁻¹ • ξ).prod ρ := by
    rw [Measure.prod_smul_left, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have h_emb : MeasurableEmbedding (Prod.swap : α × β → β × α) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [h_prod μ, h_prod ν, fDiv_smul_smul, ← Measure.prod_swap (μ := μ),
    ← Measure.prod_swap (μ := ν), fDiv_map_measurableEmbedding h_emb, fDiv_prod_left, hc]

lemma fDiv_fst_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν :=
  fDiv_map_le measurable_fst

lemma fDiv_snd_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν :=
  fDiv_map_le measurable_snd

/-- Composing with Markov kernels can only increase an f-divergence, even with different kernels
on the two sides. -/
lemma le_fDiv_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  have h := fDiv_fst_le (f := f) (μ ⊗ₘ κ) (ν ⊗ₘ η)
  rwa [Measure.fst_compProd, Measure.fst_compProd] at h

lemma fDiv_comp_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [← Measure.snd_compProd]
  exact fDiv_snd_le _ _

/-- **Data processing inequality** for the f-divergence. -/
theorem fDiv_comp_right_le (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  (fDiv_comp_le_compProd μ ν κ κ).trans_eq (fDiv_compProd_left μ ν κ)

/-- A kernel `κ` with a Markov left inverse `η`, that is `η ∘ₖ κ = Kernel.id`, preserves
f-divergences. Such a kernel is Markov. -/
lemma fDiv_comp_eq_of_comp_eq_id (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) (η : Kernel β α) [IsMarkovKernel η] (h : η ∘ₖ κ = Kernel.id) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) = fDiv f μ ν := by
  have : IsMarkovKernel κ := ⟨fun x ↦ ⟨by
    simpa [Kernel.comp_apply' _ _ _ MeasurableSet.univ] using congr(($h x) Set.univ)⟩⟩
  refine le_antisymm (fDiv_comp_right_le μ ν κ) ?_
  calc fDiv f μ ν = fDiv f (η ∘ₘ (κ ∘ₘ μ)) (η ∘ₘ (κ ∘ₘ ν)) := by
        rw [Measure.comp_assoc, Measure.comp_assoc, h, Measure.id_comp, Measure.id_comp]
  _ ≤ fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) := fDiv_comp_right_le _ _ η

/-- A kernel `κ : α → α × β` such that the first marginal of `κ x` is `δ_x` for all `x`
preserves f-divergences. -/
lemma fDiv_comp_eq_of_fst_eq_id (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α (α × β)) (hκ : κ.fst = Kernel.id) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) = fDiv f μ ν :=
  fDiv_comp_eq_of_comp_eq_id μ ν κ (Kernel.deterministic Prod.fst measurable_fst)
    (by rwa [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq])

end ProbabilityTheory
