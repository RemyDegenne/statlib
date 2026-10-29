/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Hellinger.TotalVariation
public import Statlib.Divergence.Renyi.Prod

/-!
# Total variation distance between product measures and the Rényi divergence of order `1/2`

For probability measures `μ`, `ν` and a finite index type `ι` with `n` elements, write
`R = R_{1/2}(μ, ν)` and `TV = tvDist / 2`. The Rényi divergence of order `1/2` tensorizes,
`R_{1/2}(μ^⊗ι, ν^⊗ι) = n * R` (`renyiDiv_pi_const`). Together with the comparison between the
total variation distance and the Rényi divergence of order `1/2` (through the squared Hellinger
distance), this gives
`exp (-n R) / 2 ≤ 1 - √(1 - exp (-n R)) ≤ 1 - TV(μ^⊗ι, ν^⊗ι) ≤ exp (-n R / 2)`.

## Main statements

* `one_sub_tvDist_pi_div_two_le_exp`: `1 - TV(μ^⊗ι, ν^⊗ι) ≤ exp (-n R / 2)`.
* `one_sub_sqrt_one_sub_exp_le_one_sub_tvDist_pi_div_two`:
  `1 - √(1 - exp (-n R)) ≤ 1 - TV(μ^⊗ι, ν^⊗ι)` if `μ` and `ν` are not mutually singular.
* `exp_neg_div_two_le_one_sub_tvDist_pi_div_two`: `exp (-n R) / 2 ≤ 1 - TV(μ^⊗ι, ν^⊗ι)` if `μ`
  and `ν` are not mutually singular.
-/

@[expose] public section

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {ι : Type*} [Fintype ι]

/-- For probability measures `μ`, `ν` and a finite index type `ι` with `n` elements,
`1 - TV(μ^⊗ι, ν^⊗ι) ≤ exp (-n R_{1/2}(μ, ν) / 2)`, where `TV = tvDist / 2`. -/
theorem one_sub_tvDist_pi_div_two_le_exp [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) / 2
      ≤ exp (-(Fintype.card ι * (renyiDiv 2⁻¹ μ ν).toReal) / 2) := by
  rw [← toReal_renyiDiv_pi_const (by norm_num)]
  exact one_sub_tvDist_div_two_le_exp

/-- For probability measures `μ`, `ν` which are not mutually singular and a finite index type
`ι` with `n` elements, `1 - √(1 - exp (-n R_{1/2}(μ, ν))) ≤ 1 - TV(μ^⊗ι, ν^⊗ι)`, where
`TV = tvDist / 2`. -/
theorem one_sub_sqrt_one_sub_exp_le_one_sub_tvDist_pi_div_two [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h_ms : ¬ μ ⟂ₘ ν) :
    1 - √(1 - exp (-(Fintype.card ι * (renyiDiv 2⁻¹ μ ν).toReal)))
      ≤ 1 - tvDist (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) / 2 := by
  rw [← toReal_renyiDiv_pi_const (by norm_num)]
  exact one_sub_sqrt_one_sub_exp_le_one_sub_tvDist_div_two
    (Measure.not_mutuallySingular_pi fun _ ↦ h_ms)

/-- For probability measures `μ`, `ν` which are not mutually singular and a finite index type
`ι` with `n` elements, `exp (-n R_{1/2}(μ, ν)) / 2 ≤ 1 - TV(μ^⊗ι, ν^⊗ι)`, where
`TV = tvDist / 2`. -/
theorem exp_neg_div_two_le_one_sub_tvDist_pi_div_two [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h_ms : ¬ μ ⟂ₘ ν) :
    exp (-(Fintype.card ι * (renyiDiv 2⁻¹ μ ν).toReal)) / 2
      ≤ 1 - tvDist (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) / 2 := by
  rw [← toReal_renyiDiv_pi_const (by norm_num)]
  exact exp_neg_div_two_le_one_sub_tvDist_div_two (Measure.not_mutuallySingular_pi fun _ ↦ h_ms)

end ProbabilityTheory
