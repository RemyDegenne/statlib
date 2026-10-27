/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Kullback-Leibler divergence between Bernoulli distributions

The Kullback-Leibler divergence between two Bernoulli distributions with parameters `p` and `q`
is `p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))` for `q ∈ (0, 1)`. We define it as the
real-valued function `klBerReal` given by that formula.

The definition and its basic API are copied from LMLPapers
(`LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`), which also
defines the `ℝ≥0∞`-valued version and identifies it with `klDiv` between Bernoulli measures.

## Main definitions

* `InformationTheory.klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`: the
  binary Kullback-Leibler divergence, as a real number.

## Main statements

* `klBerReal_one_sub`: `klBerReal (1 - p) (1 - q) = klBerReal p q`.
* `klBerReal_nonneg`: Gibbs' inequality, `0 ≤ klBerReal p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`.
-/

@[expose] public section

open Real

namespace InformationTheory

variable {p q : ℝ}

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. The formula is only meaningful for
`q ∈ (0, 1)`. -/
noncomputable def klBerReal (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Unfolding lemma for `klBerReal`. -/
lemma klBerReal_apply (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

/-- The binary divergence from the parameter `0`. -/
@[simp] lemma klBerReal_zero_left : klBerReal 0 q = -log (1 - q) := by simp [klBerReal]

/-- The binary divergence from the parameter `1`. -/
@[simp] lemma klBerReal_one_left : klBerReal 1 q = -log q := by simp [klBerReal]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  simp only [klBerReal, sub_sub_cancel]
  ring

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  simp [klBerReal, div_self hp, sub_ne_zero.2 hp1.symm]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBerReal_eq_of_ne (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBerReal, mul_log_div hq, mul_log_div (sub_ne_zero.2 hq1.symm)]

/-- The binary divergence in terms of the binary entropy: for `q ∉ {0, 1}`,
`klBerReal p q = -binEntropy p - p log q - (1 - p) log (1 - q)`. -/
lemma klBerReal_eq_neg_binEntropy_sub (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = -binEntropy p - p * log q - (1 - p) * log (1 - q) := by
  rw [klBerReal_eq_of_ne hq hq1]
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  ring

/-- **Gibbs' inequality** for Bernoulli distributions: the binary divergence is nonnegative. -/
lemma klBerReal_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klBerReal p q := by
  have h₁ := sub_le_mul_log_div hp0 hq0
  have h₂ := sub_le_mul_log_div (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)
  rw [klBerReal]
  linarith

end InformationTheory
