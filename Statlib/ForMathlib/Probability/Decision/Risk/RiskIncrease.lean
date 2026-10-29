/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Decision.Risk.RiskIncrease

/-!
# Additional properties of the risk increase

## Main statements

* `riskIncrease_eq_sub_add_riskIncrease_comp`: for a Markov kernel `η`, the risk increase of `P`
  is the increase of the Bayes risk when the data is processed with `η`, plus the risk increase
  of `η ∘ₖ P`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}

/-- The risk increase of `P` is the increase of the Bayes risk when processing the data with a
Markov kernel `η`, plus the risk increase of `η ∘ₖ P`. -/
lemma riskIncrease_eq_sub_add_riskIncrease_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    riskIncrease ℓ P π
      = (bayesRisk ℓ (η ∘ₖ P) π - bayesRisk ℓ P π) + riskIncrease ℓ (η ∘ₖ P) π := by
  have h_discard : bayesRisk ℓ (Kernel.discard 𝓧' ∘ₖ (η ∘ₖ P)) π
      = bayesRisk ℓ (Kernel.discard 𝓧 ∘ₖ P) π := by
    rw [← Kernel.comp_assoc, Kernel.comp_discard]
  have h1 : bayesRisk ℓ P π ≤ bayesRisk ℓ (η ∘ₖ P) π := bayesRisk_le_bayesRisk_comp ℓ P π η
  have h2 : bayesRisk ℓ (η ∘ₖ P) π ≤ bayesRisk ℓ (Kernel.discard 𝓧 ∘ₖ P) π :=
    h_discard ▸ bayesRisk_le_bayesRisk_comp ℓ (η ∘ₖ P) π (Kernel.discard 𝓧')
  rw [riskIncrease, riskIncrease, h_discard, add_comm, tsub_add_tsub_cancel h2 h1]

end ProbabilityTheory
