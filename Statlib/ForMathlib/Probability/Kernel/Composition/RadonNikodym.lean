/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Radon-Nikodym derivatives of compositions and composition-products

## Main statements

* `ProbabilityTheory.rnDeriv_compProd'`: `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) = ∂μ/∂ν * ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`,
  without assumptions on the measurable spaces nor absolute continuity hypotheses.
* `ProbabilityTheory.rnDeriv_compProd_of_absolutelyContinuous`: for `ρ ≪ μ`,
  `∂(ρ ⊗ₘ κ)/∂(ρ ⊗ₘ η) = ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`, `ρ ⊗ₘ η`-almost everywhere.
* `MeasureTheory.Measure.sigmaFinite_compProd`: `μ ⊗ₘ κ` is σ-finite for a σ-finite `μ` and a
  finite kernel `κ`.
* `ProbabilityTheory.compProd_eq_compProd_singularPart_add_withDensity`: Lebesgue decomposition of
  `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η`.
* `ProbabilityTheory.rnDeriv_measure_compProd_right_of_sigmaFinite`: Mathlib's
  `rnDeriv_measure_compProd_right`, `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) = ∂κ/∂η`, for a σ-finite measure `μ`.
* `ProbabilityTheory.rnDeriv_measure_compProd_right'`,
  `ProbabilityTheory.rnDeriv_measure_compProd'`: corollaries of
  `rnDeriv_measure_compProd_right_of_sigmaFinite` and of the Mathlib result
  `rnDeriv_measure_compProd`, in "a.e. a, a.e. b" form.
* `ProbabilityTheory.toReal_rnDeriv_comp_ae_eq_condExp`: the Radon-Nikodym derivative
  `∂(κ ∘ₘ μ)/∂(η ∘ₘ ν)`, evaluated at the second coordinate, is the conditional expectation of
  `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` given the second coordinate.
* `ProbabilityTheory.toReal_rnDeriv_comp_ae_eq_condExp_right`: the Radon-Nikodym derivative
  `∂(κ ∘ₘ μ)/∂(κ ∘ₘ ν)`, evaluated at the second coordinate, is the conditional expectation of
  `(x, y) ↦ ∂μ/∂ν x` given the second coordinate (see [Csiszár, 1963]).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).

## References

* I. Csiszár, *Eine informationstheoretische Ungleichung und ihre Anwendung auf den Beweis der
  Ergodizität von Markoffschen Ketten*, A Magyar Tudományos Akadémia Matematikai Kutató
  Intézetének Közleményei 8 (1963), 85–108.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {κ η : Kernel α β}

/-- The composition-product of a σ-finite measure and a finite kernel is σ-finite. -/
instance _root_.MeasureTheory.Measure.sigmaFinite_compProd [SigmaFinite μ] [IsFiniteKernel κ] :
    SigmaFinite (μ ⊗ₘ κ) := by
  refine ⟨⟨⟨fun n ↦ spanningSets μ n ×ˢ Set.univ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · rw [Measure.compProd_apply_prod (measurableSet_spanningSets μ n) .univ]
    calc ∫⁻ a in spanningSets μ n, κ a .univ ∂μ
    _ ≤ ∫⁻ _ in spanningSets μ n, κ.bound ∂μ :=
      lintegral_mono fun a ↦ Kernel.measure_le_bound κ a .univ
    _ < ∞ := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top κ.bound_lt_top (measure_spanningSets_lt_top μ n)
  · rw [← Set.iUnion_prod_const, iUnion_spanningSets, Set.univ_prod_univ]

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` is the product of `∂μ/∂ν` and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`. This is Mathlib's `rnDeriv_compProd` without its hypothesis
`μ ⊗ₘ κ ≪ μ ⊗ₘ η`. -/
lemma rnDeriv_compProd' (μ ν : Measure α) (κ η : Kernel α β) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
      fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p := by
  -- the part of `μ ⊗ₘ κ` singular with respect to `μ ⊗ₘ η` is also singular with respect to
  -- `ν ⊗ₘ η`, whose part absolutely continuous with respect to `μ ⊗ₘ η` comes from `ν`'s part
  -- absolutely continuous with respect to `μ`
  have h_sing : (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) ⟂ₘ ν ⊗ₘ η := by
    have hν : ν ⊗ₘ η = ν.singularPart μ ⊗ₘ η + μ.withDensity (ν.rnDeriv μ) ⊗ₘ η := by
      rw [← Measure.compProd_add_left, ← ν.haveLebesgueDecomposition_add μ]
    rw [hν]
    refine Measure.MutuallySingular.add_right ?_ ?_
    · exact ((Measure.mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η).mono_ac
        (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)) .rfl
    · exact (Measure.mutuallySingular_singularPart _ _).mono_ac .rfl
        ((withDensity_absolutelyContinuous _ _).compProd_left η)
  have h_add := Measure.rnDeriv_add' ((μ ⊗ₘ κ).singularPart (μ ⊗ₘ η))
    ((μ ⊗ₘ η).withDensity ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η))) (ν ⊗ₘ η)
  rw [← (μ ⊗ₘ κ).haveLebesgueDecomposition_add (μ ⊗ₘ η)] at h_add
  filter_upwards [h_add, Measure.rnDeriv_eq_zero_of_mutuallySingular h_sing .rfl,
    Measure.rnDeriv_withDensity_left (μ := μ ⊗ₘ η) (ν := ν ⊗ₘ η)
      (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.rnDeriv_ne_top (μ ⊗ₘ κ) _),
    rnDeriv_measure_compProd_left μ ν η] with p h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, h4, Pi.zero_apply, zero_add, mul_comm]

/-- If `ρ ≪ μ`, then `∂(ρ ⊗ₘ κ)/∂(ρ ⊗ₘ η)` is `ρ ⊗ₘ η`-almost everywhere equal to
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`. -/
lemma rnDeriv_compProd_of_absolutelyContinuous {ρ : Measure α} [IsFiniteMeasure ρ]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (hρμ : ρ ≪ μ) :
    (ρ ⊗ₘ κ).rnDeriv (ρ ⊗ₘ η) =ᵐ[ρ ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) := by
  -- with `h = ∂ρ/∂μ`, `ρ ⊗ₘ κ` is `μ ⊗ₘ κ` with density `h ∘ fst`, and the same for `η`: both
  -- derivatives with respect to `μ ⊗ₘ η` are `h ∘ fst` times the derivatives of the statement
  have hρ (ξ : Kernel α β) [IsFiniteKernel ξ] :
      ρ ⊗ₘ ξ = (μ ⊗ₘ ξ).withDensity (fun p ↦ ρ.rnDeriv μ p.1) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ρ μ hρμ]
    exact Measure.withDensity_compProd (Measure.measurable_rnDeriv ρ μ)
  have h_top : ∀ᵐ p ∂(μ ⊗ₘ η), ρ.rnDeriv μ p.1 ≠ ∞ :=
    Measure.ae_compProd_of_ae_fst η ((Measure.measurable_rnDeriv ρ μ)
      (measurableSet_singleton ∞).compl) (Measure.rnDeriv_ne_top ρ μ)
  have h_top' : ∀ᵐ p ∂(μ ⊗ₘ κ), ρ.rnDeriv μ p.1 ≠ ∞ :=
    Measure.ae_compProd_of_ae_fst κ ((Measure.measurable_rnDeriv ρ μ)
      (measurableSet_singleton ∞).compl) (Measure.rnDeriv_ne_top ρ μ)
  have h_eq : ∀ᵐ p ∂(μ ⊗ₘ η), ρ.rnDeriv μ p.1 ≠ 0 →
      (ρ ⊗ₘ κ).rnDeriv (ρ ⊗ₘ η) p = (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p := by
    have h2 : (ρ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
        fun p ↦ ρ.rnDeriv μ p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p := by
      rw [hρ κ]
      exact Measure.rnDeriv_withDensity_left (by fun_prop) h_top'
    filter_upwards [rnDeriv_compProd' ρ μ κ η, h2, h_top] with p hp1 hp2 hp_top hp0
    exact (ENNReal.mul_right_inj hp0 hp_top).mp (hp1.symm.trans hp2)
  rw [hρ η, Filter.EventuallyEq, ae_withDensity_iff (by fun_prop)]
  rwa [← hρ η]

section CountableOrCountablyGenerated

variable [CountableOrCountablyGenerated α β]

/-- Lebesgue decomposition of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η`: the singular part is
`μ ⊗ₘ κ.singularPart η` and the density is `(a, b) ↦ ∂κ/∂η a b`. -/
lemma compProd_eq_compProd_singularPart_add_withDensity (μ : Measure α)
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
  by_cases hμ : SFinite μ
  swap; · simp [Measure.compProd_of_not_sfinite _ _ hμ]
  conv_lhs => rw [← Kernel.rnDeriv_add_singularPart κ η]
  rw [Measure.compProd_add_right, add_comm,
    Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` (with the same measure) equals `∂κ/∂η`.
This is Mathlib's `rnDeriv_measure_compProd_right` for a σ-finite instead of finite measure `μ`.

σ-finiteness cannot be weakened to s-finiteness: for `μ = ∞ • Measure.dirac a`, the measure
`μ ⊗ₘ η` is not σ-finite and densities with respect to it are not unique. -/
lemma rnDeriv_measure_compProd_right_of_sigmaFinite (μ : Measure α) [SigmaFinite μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ κ.rnDeriv η p.1 p.2 :=
  (Measure.eq_rnDeriv (Kernel.measurable_rnDeriv κ η)
    (Measure.MutuallySingular.compProd_of_right μ μ
      (.of_forall <| Kernel.mutuallySingular_singularPart κ η))
    (compProd_eq_compProd_singularPart_add_withDensity μ κ η)).symm

/-- Version of `rnDeriv_measure_compProd_right_of_sigmaFinite` in "a.e. a, a.e. b" form: for
`μ`-almost every `a`, `b ↦ ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) (a, b)` is `η a`-a.e. equal to `∂(κ a)/∂(η a)`. -/
lemma rnDeriv_measure_compProd_right' (μ : Measure α) [SigmaFinite μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂μ, (fun x ↦ (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, x))
      =ᵐ[η a] fun x ↦ (∂κ a/∂η a) x := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd_right_of_sigmaFinite μ κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

/-- Version of `rnDeriv_measure_compProd` in "a.e. a, a.e. b" form: for `ν`-almost every `a`,
`b ↦ ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) (a, b)` is `η a`-a.e. equal to `∂μ/∂ν a * ∂(κ a)/∂(η a) b`. -/
lemma rnDeriv_measure_compProd' (μ ν : Measure α) (κ η : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b))
      =ᵐ[η a] fun b ↦ (∂μ/∂ν) a * (∂κ a/∂η a) b := by
  have h a := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  have h' := Measure.ae_ae_of_ae_compProd <| rnDeriv_measure_compProd μ ν κ η
  filter_upwards [h'] with a ha
  filter_upwards [ha, h a] with b hb1 hb2
  rw [hb1, hb2]

end CountableOrCountablyGenerated

/-- The Radon-Nikodym derivative `∂(κ ∘ₘ μ)/∂(η ∘ₘ ν)`, evaluated at the second coordinate, is
the conditional expectation of `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` given the second coordinate.

The absolute continuity hypothesis holds for example if `μ ≪ ν` and `κ a ≪ η a` for `μ`-almost
every `a` (see `MeasureTheory.Measure.AbsolutelyContinuous.compProd`). -/
lemma toReal_rnDeriv_comp_ae_eq_condExp [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    (fun p : α × β ↦ ((κ ∘ₘ μ).rnDeriv (η ∘ₘ ν) p.2).toReal)
      =ᵐ[ν ⊗ₘ η] (ν ⊗ₘ η)[fun p ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal | mβ.comap Prod.snd] := by
  have h := toReal_rnDeriv_map h_ac measurable_snd
  rwa [← Measure.snd, ← Measure.snd, Measure.snd_compProd, Measure.snd_compProd] at h

/-- The Radon-Nikodym derivative `∂(κ ∘ₘ μ)/∂(κ ∘ₘ ν)`, evaluated at the second coordinate, is the
conditional expectation of `(x, y) ↦ ∂μ/∂ν x` given the second coordinate. -/
lemma toReal_rnDeriv_comp_ae_eq_condExp_right [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] (hμν : μ ≪ ν) :
    (fun p : α × β ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) p.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun p ↦ (μ.rnDeriv ν p.1).toReal | mβ.comap Prod.snd] := by
  refine (toReal_rnDeriv_comp_ae_eq_condExp (hμν.compProd_left κ)).trans ?_
  refine condExp_congr_ae ?_
  filter_upwards [rnDeriv_measure_compProd_left μ ν κ] with p hp
  rw [hp]

end ProbabilityTheory
