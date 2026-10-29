/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Variational
public import Statlib.Testing.Sequential.KLDiv

/-!
# Rényi divergence of i.i.d. sequences observed up to a stopping time

Let `μ^ℕ = Measure.infinitePi (fun _ : ℕ ↦ μ)`, let `τ` be a stopping time for the filtration
`Filtration.piLE` with values in `ℕ`, and let `μ_τ` be the restriction of `μ^ℕ` to the σ-algebra of
`τ`. For `a ∈ (0, 1)` and probability measures `μ`, `ν` that are not mutually singular, let
`ξ = renyiMeasure a μ ν` be the tilted probability measure of the variational formula for the Rényi
divergence. Then `R_a(μ_τ, ν_τ) ≤ ξ^ℕ[τ + 1] * R_a(μ, ν)`.

The inequality is in general strict: by a change of measure,
`exp ((a - 1) R_a(μ_τ, ν_τ)) = ξ^ℕ[exp ((a - 1) (τ + 1) R_a(μ, ν))]`, and the inequality follows
from Jensen's inequality, with equality when `τ` is deterministic. In particular the restriction of
`ξ^ℕ` to the σ-algebra of `τ` is not `renyiMeasure a μ_τ ν_τ` in general.

## Main statements

* `renyiDiv_trim_stoppingTime_le`: `R_a(μ_τ, ν_τ) ≤ ξ^ℕ[τ + 1] * R_a(μ, ν)`, with the expectation
  computed in `ℝ≥0∞`.
-/

@[expose] public section

open MeasureTheory Filtration InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {τ : (ℕ → 𝓧) → ℕ} {a : ℝ}

/-- **Rényi divergence at a stopping time**: for `a ∈ (0, 1)`, probability measures `μ`, `ν` that
are not mutually singular and `ξ = renyiMeasure a μ ν`, `R_a(μ_τ, ν_τ) ≤ ξ^ℕ[τ + 1] * R_a(μ, ν)`,
where `μ_τ` and `ν_τ` are the restrictions of `μ^ℕ` and `ν^ℕ` to the σ-algebra of the stopping
time `τ`. -/
theorem renyiDiv_trim_stoppingTime_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) (h_ms : ¬ μ ⟂ₘ ν)
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ))) :
    renyiDiv a ((Measure.infinitePi fun _ : ℕ ↦ μ).trim hτ.measurableSpace_le)
        ((Measure.infinitePi fun _ : ℕ ↦ ν).trim hτ.measurableSpace_le)
      ≤ (∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂(Measure.infinitePi fun _ : ℕ ↦ renyiMeasure a μ ν))
        * renyiDiv a μ ν := by
  have := isProbabilityMeasure_renyiMeasure ha0 ha1 h_ms
  set ξ := renyiMeasure a μ ν
  set hm := hτ.measurableSpace_le
  -- `(1 - a) R_a(μ, ν) = a KL(ξ, μ) + (1 - a) KL(ξ, ν)`
  have h_kl := mul_klDiv_add_mul_klDiv ha0 ha1 (renyiMeasure_absolutelyContinuous_left ν ha0)
    (renyiMeasure_absolutelyContinuous_right μ ha1)
  rw [klDiv_self, zero_add] at h_kl
  -- variational formula for the Rényi divergence between the stopped measures, with `ξ_τ`
  refine (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal (1 - a)) (by simp [ha1])
    ENNReal.ofReal_ne_top).mp ?_
  refine (mul_renyiDiv_le_mul_klDiv_add_mul_klDiv _ _
    ((Measure.infinitePi fun _ : ℕ ↦ ξ).trim hm) ha0 ha1).trans_eq ?_
  rw [klDiv_trim_stoppingTime hτ, klDiv_trim_stoppingTime hτ]
  calc _ = (∫⁻ ω, (τ ω + 1 : ℝ≥0∞) ∂(Measure.infinitePi fun _ : ℕ ↦ ξ))
      * (ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν) := by ring
  _ = _ := by rw [h_kl]; ring

end ProbabilityTheory
