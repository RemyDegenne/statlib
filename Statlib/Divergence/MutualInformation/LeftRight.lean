/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.CompProd
public import Statlib.Divergence.MutualInformation.Basic

/-!
# Left and right `f`-mutual informations

For a divergence function `f`, a measure `μ` on `α` and a kernel `κ : α ⇝ β`, we define two
generalizations of the mutual information `I(μ ⊗ κ) = KL(μ ⊗ κ, μ × (κ ∘ μ))`, in which the
Kullback-Leibler divergence is replaced by the f-divergence `D_f` and the second marginal by an
optimized probability measure `ξ`:
* the left `f`-mutual information `⨅ ξ, D_f(μ × ξ, μ ⊗ κ)`,
* the right `f`-mutual information `⨅ ξ, D_f(μ ⊗ κ, μ × ξ)`.

The Kullback-Leibler mutual informations are the case `f = klDivFun`.

## Main definitions

* `mutualInfoLeft f μ κ`: the left `f`-mutual information.
* `mutualInfoRight f μ κ`: the right `f`-mutual information.

## Main statements

* `mutualInfoLeft_klDivFun_eq_iInf`, `mutualInfoRight_klDivFun_eq_iInf`: the Kullback-Leibler
  mutual informations as infima of Kullback-Leibler divergences.
* `mutualInfoRight_klDivFun`: for a probability measure `μ` and a Markov kernel `κ`, the right
  Kullback-Leibler mutual information of `μ` and `κ` is the mutual information `I(μ ⊗ κ)`.
* `mutualInfoLeft_comp_le`, `mutualInfoRight_comp_le`: **data-processing inequalities** for the
  left and right `f`-mutual informations.
-/

@[expose] public section

open MeasureTheory InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {f : DivFunction} {μ : Measure α} {κ : Kernel α β} {c : ℝ≥0∞}

/-- The left `f`-mutual information of a measure `μ` and a kernel `κ`: the infimum over
probability measures `ξ` of `fDiv f (μ.prod ξ) (μ ⊗ₘ κ)`. -/
noncomputable
def mutualInfoLeft (f : DivFunction) (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ⨅ (ξ : Measure β) (_ : IsProbabilityMeasure ξ), fDiv f (μ.prod ξ) (μ ⊗ₘ κ)

/-- The right `f`-mutual information of a measure `μ` and a kernel `κ`: the infimum over
probability measures `ξ` of `fDiv f (μ ⊗ₘ κ) (μ.prod ξ)`. -/
noncomputable
def mutualInfoRight (f : DivFunction) (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ⨅ (ξ : Measure β) (_ : IsProbabilityMeasure ξ), fDiv f (μ ⊗ₘ κ) (μ.prod ξ)

section Bounds

variable (f μ κ) in
lemma mutualInfoLeft_le (ξ : Measure β) [IsProbabilityMeasure ξ] :
    mutualInfoLeft f μ κ ≤ fDiv f (μ.prod ξ) (μ ⊗ₘ κ) :=
  iInf₂_le ξ ‹_›

variable (f μ κ) in
lemma mutualInfoRight_le (ξ : Measure β) [IsProbabilityMeasure ξ] :
    mutualInfoRight f μ κ ≤ fDiv f (μ ⊗ₘ κ) (μ.prod ξ) :=
  iInf₂_le ξ ‹_›

lemma le_mutualInfoLeft
    (h : ∀ (ξ : Measure β) [IsProbabilityMeasure ξ], c ≤ fDiv f (μ.prod ξ) (μ ⊗ₘ κ)) :
    c ≤ mutualInfoLeft f μ κ :=
  le_iInf₂ fun ξ _ ↦ h ξ

lemma le_mutualInfoRight
    (h : ∀ (ξ : Measure β) [IsProbabilityMeasure ξ], c ≤ fDiv f (μ ⊗ₘ κ) (μ.prod ξ)) :
    c ≤ mutualInfoRight f μ κ :=
  le_iInf₂ fun ξ _ ↦ h ξ

end Bounds

section KullbackLeibler

/-- The left Kullback-Leibler mutual information is the infimum over probability measures `ξ` of
`KL(μ × ξ, μ ⊗ₘ κ)`. -/
lemma mutualInfoLeft_klDivFun_eq_iInf (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β)
    [IsFiniteKernel κ] :
    mutualInfoLeft klDivFun μ κ
      = ⨅ (ξ : Measure β) (_ : IsProbabilityMeasure ξ), klDiv (μ.prod ξ) (μ ⊗ₘ κ) :=
  iInf_congr fun _ ↦ iInf_congr fun _ ↦ klDiv_eq_fDiv.symm

/-- The right Kullback-Leibler mutual information is the infimum over probability measures `ξ` of
`KL(μ ⊗ₘ κ, μ × ξ)`. -/
lemma mutualInfoRight_klDivFun_eq_iInf (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β)
    [IsFiniteKernel κ] :
    mutualInfoRight klDivFun μ κ
      = ⨅ (ξ : Measure β) (_ : IsProbabilityMeasure ξ), klDiv (μ ⊗ₘ κ) (μ.prod ξ) :=
  iInf_congr fun _ ↦ iInf_congr fun _ ↦ klDiv_eq_fDiv.symm

/-- The right Kullback-Leibler mutual information is the mutual information: the infimum over
probability measures `ξ` of `KL(μ ⊗ₘ κ, μ × ξ)` is `I(μ ⊗ₘ κ)`, attained at `ξ = κ ∘ₘ μ`. -/
theorem mutualInfoRight_klDivFun (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    mutualInfoRight klDivFun μ κ = mutualInfo (μ ⊗ₘ κ) := by
  refine le_antisymm ((mutualInfoRight_le _ μ κ (κ ∘ₘ μ)).trans_eq ?_) ?_
  · rw [← klDiv_eq_fDiv, mutualInfo_compProd]
  · rw [mutualInfoRight_klDivFun_eq_iInf]
    refine le_iInf₂ fun ξ _ ↦ ?_
    rw [klDiv_compProd_prod_eq_mutualInfo_add]
    exact le_self_add

end KullbackLeibler

section DataProcessing

/-- **Data-processing inequality** for the left `f`-mutual information. -/
theorem mutualInfoLeft_comp_le (f : DivFunction) (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel β γ) [IsMarkovKernel η] :
    mutualInfoLeft f μ (η ∘ₖ κ) ≤ mutualInfoLeft f μ κ := by
  refine le_mutualInfoLeft fun ξ _ ↦ (mutualInfoLeft_le f μ _ (η ∘ₘ ξ)).trans ?_
  rw [Measure.prod_comp_right, ← Measure.parallelComp_comp_compProd]
  exact fDiv_comp_right_le _ _ _

/-- **Data-processing inequality** for the right `f`-mutual information. -/
theorem mutualInfoRight_comp_le (f : DivFunction) (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel β γ) [IsMarkovKernel η] :
    mutualInfoRight f μ (η ∘ₖ κ) ≤ mutualInfoRight f μ κ := by
  refine le_mutualInfoRight fun ξ _ ↦ (mutualInfoRight_le f μ _ (η ∘ₘ ξ)).trans ?_
  rw [Measure.prod_comp_right, ← Measure.parallelComp_comp_compProd]
  exact fDiv_comp_right_le _ _ _

end DataProcessing

end ProbabilityTheory
