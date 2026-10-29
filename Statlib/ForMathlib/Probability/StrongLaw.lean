/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.Probability.StrongLaw
public import Statlib.ForMathlib.Probability.ProductMeasure

/-!
# Weak law of large numbers

## Main statements

* `ProbabilityTheory.weak_law_tendstoInMeasure`: **weak law of large numbers**, for a sequence of
  pairwise independent identically distributed integrable random variables with values in a Banach
  space: the empirical means converge in measure to the mean. It is deduced from Mathlib's strong
  law `ProbabilityTheory.strong_law_ae`.
* `ProbabilityTheory.tendsto_measureReal_lt_sum_comp_eval`: the weak law for an i.i.d. sequence with
  law `ξ`, realized as the coordinates under `ξ^ℕ = Measure.infinitePi`: for `β > 0`, the
  probability that `∑ i ≤ m, f (ω i)` exceeds `(m + 1) * (∫ f ∂ξ + β)` tends to `0`.
-/

@[expose] public section

open MeasureTheory Filter

open scoped Function Topology

namespace ProbabilityTheory

section WeakLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Weak law of large numbers**: if `X n` is a sequence of pairwise independent identically
distributed integrable random variables taking values in a Banach space, then
`n⁻¹ • ∑ i ∈ range n, X i` converges in measure to `𝔼[X 0]`. -/
theorem weak_law_tendstoInMeasure (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop
      (fun _ ↦ μ[X 0]) := by
  -- if `X 0 = 0` almost everywhere, then all the means vanish almost everywhere
  by_cases h : ∀ᵐ ω ∂μ, X 0 ω = 0
  · have I : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 :=
      ae_all_iff.2 fun i ↦ (hident i).symm.ae_snd (p := fun x ↦ x = 0) measurableSet_eq h
    refine fun ε hε ↦ tendsto_const_nhds.congr fun n ↦ ?_
    refine (measure_eq_zero_iff_ae_notMem.2 ?_).symm
    filter_upwards [I] with ω hω
    simp [hω, integral_eq_zero_of_ae h, hε.ne']
  -- otherwise `μ` is a probability measure and we use the strong law
  have : IsProbabilityMeasure μ :=
    hint.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hindep zero_ne_one)
  have hmeas (i : ℕ) : AEStronglyMeasurable (X i) μ :=
    (hident i).aestronglyMeasurable_iff.2 hint.aestronglyMeasurable
  exact tendstoInMeasure_of_tendsto_ae
    (fun n ↦ (Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ hmeas i).const_smul _)
    (strong_law_ae X hint hindep hident)

end WeakLaw

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ξ : Measure 𝓧}

/-- **Weak law of large numbers** for an i.i.d. sequence: for `β > 0`, the probability under
`ξ^ℕ` that `∑ i ≤ m, f (ω i)` exceeds `(m + 1) * (∫ f ∂ξ + β)` tends to `0`. -/
lemma tendsto_measureReal_lt_sum_comp_eval [IsProbabilityMeasure ξ] {f : 𝓧 → ℝ}
    (hf : Integrable f ξ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun m : ℕ ↦ (Measure.infinitePi fun _ : ℕ ↦ ξ).real
        {ω | (m + 1) * (∫ x, f x ∂ξ + β) < ∑ i ∈ Finset.Iic m, f (ω i)})
      atTop (𝓝 0) := by
  -- reduce to the case of a measurable function
  wlog hf_meas : Measurable f generalizing f with h_meas
  · have hfg : f =ᵐ[ξ] hf.1.mk f := hf.1.ae_eq_mk
    have h_ae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ ↦ ξ), ∀ i, f (ω i) = hf.1.mk f (ω i) :=
      ae_all_iff.2 fun i ↦
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ ξ) i).quasiMeasurePreserving.ae hfg
    convert h_meas (hf.congr hfg) hf.1.stronglyMeasurable_mk.measurable using 2 with m
    rw [integral_congr_ae hfg]
    refine measureReal_congr ?_
    filter_upwards [h_ae] with ω hω
    simp only [hω]
  set P := Measure.infinitePi fun _ : ℕ ↦ ξ
  set K := ∫ x, f x ∂ξ
  -- the coordinates of `ω` are i.i.d. with law `ξ`
  have h_ident (i : ℕ) : IdentDistrib (fun ω : ℕ → 𝓧 ↦ f (ω i)) (fun ω ↦ f (ω 0)) P P := by
    refine IdentDistrib.comp
      ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩ hf_meas
    rw [(measurePreserving_eval_infinitePi _ i).map_eq,
      (measurePreserving_eval_infinitePi _ 0).map_eq]
  have h_tim := weak_law_tendstoInMeasure (fun i (ω : ℕ → 𝓧) ↦ f (ω i))
    ((measurePreserving_eval_infinitePi _ 0).integrable_comp_of_integrable hf)
    (fun i j hij ↦ (iIndepFun_infinitePi (X := fun _ ↦ f) fun _ ↦ hf_meas).indepFun hij) h_ident
    (ENNReal.ofReal β) (ENNReal.ofReal_pos.mpr hβ)
  rw [show P[fun ω ↦ f (ω 0)] = K from
    integral_comp_eval_infinitePi (i := 0) hf.aestronglyMeasurable] at h_tim
  -- the event of the statement is included in the deviation event of the empirical mean
  have h_lim : Tendsto (fun m : ℕ ↦ P
      {ω | (m + 1) * (K + β) < ∑ i ∈ Finset.Iic m, f (ω i)}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_add_atTop_iff_nat 1).mpr h_tim) (fun _ ↦ zero_le) fun m ↦ measure_mono
      fun ω hω ↦ ?_
    have h_range : Finset.Iic m = Finset.range (m + 1) := by
      ext i; simp
    simp only [Set.mem_ofPred_eq, h_range] at hω ⊢
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have h_avg : β < ((m + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (m + 1), f (ω i) - K := by
      rw [smul_eq_mul, lt_sub_iff_add_lt, add_comm, inv_mul_eq_div, lt_div_iff₀ hm]
      calc (K + β) * ((m + 1 : ℕ) : ℝ) = (m + 1) * (K + β) := by push_cast; ring
      _ < _ := hω
    exact h_avg.le.trans (le_abs_self _)
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_lim
  rw [ENNReal.toReal_zero] at h
  exact h

end ProbabilityTheory
