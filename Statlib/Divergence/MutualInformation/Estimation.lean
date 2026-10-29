/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.KullbackLeibler.Estimation
public import Statlib.Divergence.MutualInformation.LeftRight

/-!
# Lower bounds on the `f`-mutual informations from the Bayes risk

Consider an estimation task with prior `π` on `Θ`, data kernel `P : Θ ⇝ 𝓧` and a loss with values
in `[0, 1]`. Let `R_π^P` be its Bayes risk and `R_π^{d_Θ}` the Bayes risk of the same task without
observations, i.e. with the discard kernel `Kernel.discard Θ`. We show that the left and right
`f`-mutual informations of `π` and `P` are lower bounded by the binary `f`-divergences between
those two Bayes risks:
`d_f(R_π^{d_Θ}, R_π^P) ≤ I_{D_f}^L(π, P)` and `d_f(R_π^P, R_π^{d_Θ}) ≤ I_{D_f}^R(π, P)`.

The proof applies the lower bound `fDiv_bernoulliMeasure_bayesRisk_le` to `π × ξ = π ⊗ const ξ`
for every probability measure `ξ`: the Bayes risk of a constant kernel does not depend on the
constant and equals the Bayes risk without observations.

For the Kullback-Leibler divergence, the right mutual information is at most the mutual
information `I(π ⊗ P)` (`mutualInfoRight_klDivFun`), which gives the bound
`kl(R_π^P, R_π^{d_Θ}) ≤ I(π ⊗ P)`, a version of Fano's inequality.

## Main statements

* `fDiv_bernoulliMeasure_le_mutualInfoLeft`: `d_f(R_π^{d_Θ}, R_π^P) ≤ I_{D_f}^L(π, P)`.
* `fDiv_bernoulliMeasure_le_mutualInfoRight`: `d_f(R_π^P, R_π^{d_Θ}) ≤ I_{D_f}^R(π, P)`.
* `ofReal_klBerReal_bayesRisk_le_mutualInfoLeft`, `ofReal_klBerReal_bayesRisk_le_mutualInfoRight`:
  the same bounds for the Kullback-Leibler divergence, with the real binary divergence
  `klBerReal`.
* `ofReal_klBerReal_bayesRisk_le_mutualInfo`: `kl(R_π^P, R_π^{d_Θ}) ≤ I(π ⊗ P)`.
-/

@[expose] public section

open MeasureTheory Function InformationTheory unitInterval

open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞} {f : DivFunction}
  {π : Measure Θ} [IsProbabilityMeasure π] {P : Kernel Θ 𝓧} [IsMarkovKernel P]

/-- **Lower bound on the left `f`-mutual information from the Bayes risk**: for a loss with values
in `[0, 1]`, `d_f(R_π^{d_Θ}, R_π^P) ≤ I_{D_f}^L(π, P)`, where `d_f` is the binary `f`-divergence,
`R_π^P` the Bayes risk with data kernel `P` and `R_π^{d_Θ}` the Bayes risk without observations. -/
theorem fDiv_bernoulliMeasure_le_mutualInfoLeft (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) {p q : I}
    (hp : ENNReal.ofReal p = bayesRisk ℓ (Kernel.discard Θ) π)
    (hq : ENNReal.ofReal q = bayesRisk ℓ P π) :
    fDiv f Ber(true, false, p) Ber(true, false, q) ≤ mutualInfoLeft f π P := by
  refine le_mutualInfoLeft fun ξ _ ↦ ?_
  rw [← Measure.compProd_const]
  exact fDiv_bernoulliMeasure_bayesRisk_le hℓ hℓ1
    (hp.trans (bayesRisk_const_eq_bayesRisk_discard ℓ ξ π).symm) hq

/-- **Lower bound on the right `f`-mutual information from the Bayes risk**: for a loss with values
in `[0, 1]`, `d_f(R_π^P, R_π^{d_Θ}) ≤ I_{D_f}^R(π, P)`, where `d_f` is the binary `f`-divergence,
`R_π^P` the Bayes risk with data kernel `P` and `R_π^{d_Θ}` the Bayes risk without observations. -/
theorem fDiv_bernoulliMeasure_le_mutualInfoRight (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) {p q : I}
    (hp : ENNReal.ofReal p = bayesRisk ℓ (Kernel.discard Θ) π)
    (hq : ENNReal.ofReal q = bayesRisk ℓ P π) :
    fDiv f Ber(true, false, q) Ber(true, false, p) ≤ mutualInfoRight f π P := by
  refine le_mutualInfoRight fun ξ _ ↦ ?_
  rw [← Measure.compProd_const]
  exact fDiv_bernoulliMeasure_bayesRisk_le hℓ hℓ1 hq
    (hp.trans (bayesRisk_const_eq_bayesRisk_discard ℓ ξ π).symm)

variable (π P)

/-- **Lower bound on the left Kullback-Leibler mutual information from the Bayes risk**: for a loss
with values in `[0, 1]`, `kl(R_π^{d_Θ}, R_π^P) ≤ I_{KL}^L(π, P)`. -/
theorem ofReal_klBerReal_bayesRisk_le_mutualInfoLeft (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) :
    ENNReal.ofReal
        (klBerReal (bayesRisk ℓ (Kernel.discard Θ) π).toReal (bayesRisk ℓ P π).toReal)
      ≤ mutualInfoLeft klDivFun π P := by
  refine le_mutualInfoLeft fun ξ _ ↦ ?_
  rw [← klDiv_eq_fDiv, ← Measure.compProd_const, ← bayesRisk_const_eq_bayesRisk_discard ℓ ξ π]
  exact ofReal_klBerReal_bayesRisk_le_klDiv π π P (Kernel.const Θ ξ) hℓ hℓ1

/-- **Lower bound on the right Kullback-Leibler mutual information from the Bayes risk**: for a
loss with values in `[0, 1]`, `kl(R_π^P, R_π^{d_Θ}) ≤ I_{KL}^R(π, P)`. -/
theorem ofReal_klBerReal_bayesRisk_le_mutualInfoRight (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) :
    ENNReal.ofReal
        (klBerReal (bayesRisk ℓ P π).toReal (bayesRisk ℓ (Kernel.discard Θ) π).toReal)
      ≤ mutualInfoRight klDivFun π P := by
  refine le_mutualInfoRight fun ξ _ ↦ ?_
  rw [← klDiv_eq_fDiv, ← Measure.compProd_const, ← bayesRisk_const_eq_bayesRisk_discard ℓ ξ π]
  exact ofReal_klBerReal_bayesRisk_le_klDiv π π (Kernel.const Θ ξ) P hℓ hℓ1

/-- **Fano-type inequality**: for a loss with values in `[0, 1]`, the binary Kullback-Leibler
divergence between the Bayes risk `R_π^P` and the Bayes risk without observations `R_π^{d_Θ}` is
at most the mutual information `I(π ⊗ P)`. -/
theorem ofReal_klBerReal_bayesRisk_le_mutualInfo (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) :
    ENNReal.ofReal
        (klBerReal (bayesRisk ℓ P π).toReal (bayesRisk ℓ (Kernel.discard Θ) π).toReal)
      ≤ mutualInfo (π ⊗ₘ P) :=
  (ofReal_klBerReal_bayesRisk_le_mutualInfoRight π P hℓ hℓ1).trans_eq (mutualInfoRight_klDivFun π P)

end ProbabilityTheory
