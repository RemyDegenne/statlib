/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.Renyi.Order

/-!
# Data-processing inequalities for the Rényi divergence

For finite measures and every order `a ≥ 0`, the Rényi divergence satisfies the data-processing
inequality. For `a > 0`, it is deduced from the data-processing inequality for the Hellinger
divergence of order `a` (`le_renyiDiv_of_le_hellingerDiv`). The order `0` follows by taking the
limit `a → 0⁺` (`tendsto_renyiDiv_nhdsGT_zero`).

## Main statements

* `le_renyiDiv_of_forall_le_hellingerDiv`: for `a ≥ 0` and measures with the same masses, an
  inequality between the Hellinger divergences of all positive orders gives the same inequality
  between Rényi divergences of order `a`.
* `renyiDiv_comp_le_compProd`, `renyiDiv_comp_right_le`, `renyiDiv_map_le`: data-processing
  inequalities.
* `renyiDiv_map_measurableEmbedding`: invariance under measurable embeddings.
* `renyiDiv_boolMeasure_le`: data-processing inequality for the indicator of an event,
  `Rₐ(μ_E, ν_E) ≤ Rₐ(μ, ν)` for the laws `μ_E`, `ν_E` of `x ↦ decide (x ∈ E)`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), Theorem 9.
-/

@[expose] public section

open MeasureTheory Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {a : ℝ}

/-- For `a ≥ 0` and measures with the same masses, an inequality between the Hellinger divergences
of all positive orders gives the same inequality between the Rényi divergences of order `a`. For
`a > 0`, only the order `a` matters (`le_renyiDiv_of_le_hellingerDiv`); the order `0` is the limit
of the positive orders. -/
lemma le_renyiDiv_of_forall_le_hellingerDiv {μ₁ ν₁ : Measure α} {μ₂ ν₂ : Measure β}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (ha : 0 ≤ a) (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : ∀ b, 0 < b → hellingerDiv b μ₁ ν₁ ≤ hellingerDiv b μ₂ ν₂) :
    renyiDiv a μ₁ ν₁ ≤ renyiDiv a μ₂ ν₂ := by
  rcases ha.eq_or_lt with rfl | ha
  · exact le_of_tendsto_of_tendsto tendsto_renyiDiv_nhdsGT_zero tendsto_renyiDiv_nhdsGT_zero
      (eventually_nhdsWithin_of_forall fun b hb ↦
        le_renyiDiv_of_le_hellingerDiv hb h_eq_μ h_eq_ν (h_le b hb))
  exact le_renyiDiv_of_le_hellingerDiv ha h_eq_μ h_eq_ν (h_le a ha)

/-- The Rényi divergence between composition-products with Markov kernels is at least the Rényi
divergence between the first marginals. -/
lemma le_renyiDiv_compProd (ha : 0 ≤ a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    renyiDiv a μ ν ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_renyiDiv_of_forall_le_hellingerDiv ha Measure.compProd_apply_univ.symm
    Measure.compProd_apply_univ.symm fun _ _ ↦ le_hellingerDiv_compProd μ ν κ η

/-- **Data processing inequality** for the first marginals. -/
lemma renyiDiv_fst_le (ha : 0 ≤ a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ.fst ν.fst ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_forall_le_hellingerDiv ha Measure.fst_univ Measure.fst_univ
    fun _ _ ↦ hellingerDiv_fst_le μ ν

/-- **Data processing inequality** for the second marginals. -/
lemma renyiDiv_snd_le (ha : 0 ≤ a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ.snd ν.snd ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_forall_le_hellingerDiv ha Measure.snd_univ Measure.snd_univ
    fun _ _ ↦ hellingerDiv_snd_le μ ν

/-- The Rényi divergence between the compositions `κ ∘ₘ μ` and `η ∘ₘ ν` is at most the Rényi
divergence between the composition-products. -/
lemma renyiDiv_comp_le_compProd (ha : 0 ≤ a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    renyiDiv a (κ ∘ₘ μ) (η ∘ₘ ν) ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_renyiDiv_of_forall_le_hellingerDiv ha (Measure.snd_compProd μ κ ▸ Measure.snd_univ)
    (Measure.snd_compProd ν η ▸ Measure.snd_univ) fun _ _ ↦ hellingerDiv_comp_le_compProd μ ν κ η

/-- **Data processing inequality** for the Rényi divergence and a Markov kernel. -/
lemma renyiDiv_comp_right_le (ha : 0 ≤ a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    renyiDiv a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_forall_le_hellingerDiv ha Measure.comp_apply_univ Measure.comp_apply_univ
    fun _ _ ↦ hellingerDiv_comp_right_le μ ν κ

/-- **Data processing inequality** for the Rényi divergence and a measurable map. -/
lemma renyiDiv_map_le (ha : 0 ≤ a) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : Measurable g) :
    renyiDiv a (μ.map g) (ν.map g) ≤ renyiDiv a μ ν := by
  rw [← Measure.deterministic_comp_eq_map hg, ← Measure.deterministic_comp_eq_map hg]
  exact renyiDiv_comp_right_le ha μ ν _

/-- The Rényi divergence is invariant under measurable embeddings. -/
lemma renyiDiv_map_measurableEmbedding (ha : 0 ≤ a) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {g : α → β} (hg : MeasurableEmbedding g) :
    renyiDiv a (μ.map g) (ν.map g) = renyiDiv a μ ν := by
  refine le_antisymm (renyiDiv_map_le ha μ ν hg.measurable) ?_
  cases isEmpty_or_nonempty α
  · -- both sides are Rényi divergences between zero measures, on `α` and on `β`
    rcases eq_or_ne a 1 with rfl | ha1
    · simp [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty ν]
    · simp [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty ν, ha, ha1]
  calc renyiDiv a μ ν = renyiDiv a ((μ.map g).map hg.invFun) ((ν.map g).map hg.invFun) := by
        simp [Measure.map_map hg.measurable_invFun hg.measurable, hg.leftInverse_invFun.id]
  _ ≤ renyiDiv a (μ.map g) (ν.map g) := renyiDiv_map_le ha _ _ hg.measurable_invFun

/-- **Data processing inequality** for the indicator of an event: the Rényi divergence between
the laws of `x ↦ decide (x ∈ E)` under `μ` and `ν` is at most `Rₐ(μ, ν)`. For probability
measures, those laws are the Bernoulli distributions with means `μ E` and `ν E`. -/
lemma renyiDiv_boolMeasure_le (ha : 0 ≤ a) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {E : Set α} (hE : MeasurableSet E) :
    renyiDiv a (Measure.boolMeasure (μ Eᶜ) (μ E)) (Measure.boolMeasure (ν Eᶜ) (ν E))
      ≤ renyiDiv a μ ν := by
  classical
  rw [← Measure.map_decide_mem_eq_boolMeasure μ hE, ← Measure.map_decide_mem_eq_boolMeasure ν hE]
  exact renyiDiv_map_le ha μ ν (measurable_decide_mem hE)

end ProbabilityTheory
