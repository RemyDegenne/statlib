/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.BayesEstimator
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Statlib.ForMathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Statlib.ForMathlib.Probability.Kernel.Posterior

/-!
# Losses with values in `{0, 1}` and the 0-1 loss

For a loss with values in `{0, 1}`, the average risk of an estimator is the probability that the
loss is `1`.

The main example is the 0-1 loss `zeroOneLoss θ z = 𝕀{θ ≠ z}`, for estimation problems in which
the action space is the parameter space `Θ` itself. The Bayes risk of such a problem is the
probability of misidentifying the parameter, and a Bayes estimator is given by a maximizer of the
posterior probability of the parameter.

## Main definitions

* `zeroOneLoss`: the 0-1 loss `𝕀{θ ≠ z}`.

## Main statements

* `avgRisk_eq_measure_of_mem_zero_one`, `map_uncurry_compProd_of_mem_zero_one`: for a loss with
  values in `{0, 1}`, the average risk is the probability that the loss is `1`, and the law of the
  loss puts that mass at `1` and the rest of the total mass at `0` (a Bernoulli law when the total
  mass is `1`).
* `HasArgminEstimator.bayesRisk_zeroOneLoss_eq_sub`: when the problem admits an argmin estimator
  (for example when `Θ` is countable), the Bayes risk of the 0-1 loss is
  `(P ∘ₘ π)(univ) - ∫⁻ x, ⨆ z, (P†π) x {z} ∂(P ∘ₘ π)`.
* `isArgminEstimator_zeroOneLoss_of_posterior`, `isArgminEstimator_zeroOneLoss`: an estimator
  that maximizes the posterior probability `z ↦ (P†π) x {z}`, or equivalently for countable `Θ`
  the function `z ↦ π {z} * (dP_z/d(P ∘ₘ π))(x)`, is an argmin estimator, hence a Bayes
  estimator.
* `hasArgminEstimator_zeroOneLoss`: if `Θ` is countable, such an estimator exists.
* `bayesRisk_zeroOneLoss_eq_sub_rnDeriv`: for countable `Θ`, the Bayes risk of the 0-1 loss is
  `(P ∘ₘ π)(univ) - ∫⁻ x, ⨆ z, π {z} * (dP_z/d(P ∘ₘ π))(x) ∂(P ∘ₘ π)`.
* `bayesRisk_zeroOneLoss_le_sub_prod`: for `Θ` countable and weights `w θ ≥ 0` summing to `1` on a
  finite set `s`, the Bayes risk of the 0-1 loss is at most `(P ∘ₘ π)(univ)` minus
  `(∏ θ ∈ s, π {θ} ^ w θ) * ∫⁻ x, ∏ θ ∈ s, (dP_θ/d(P ∘ₘ π))(x) ^ w θ ∂(P ∘ₘ π)`.
-/

@[expose] public section

open MeasureTheory Function Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨}

/-! ### Losses with values in `{0, 1}` -/

section ZeroOneValued

variable {ℓ : Θ → 𝓨 → ℝ≥0∞}

/-- For a loss with values in `{0, 1}`, the average risk of an estimator `κ` is the probability
that the loss is `1` under the joint law of the parameter and the estimate. -/
lemma avgRisk_eq_measure_of_mem_zero_one (hℓ : Measurable (uncurry ℓ))
    (h01 : ∀ θ y, ℓ θ y = 0 ∨ ℓ θ y = 1) (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ P κ π = (π ⊗ₘ (κ ∘ₖ P)) {p | ℓ p.1 p.2 = 1} := by
  have h_eq : uncurry ℓ = {p | ℓ p.1 p.2 = 1}.indicator 1 := by
    ext p
    rcases h01 p.1 p.2 with h | h <;> simp [uncurry_def, h]
  have h_meas : MeasurableSet {p : Θ × 𝓨 | ℓ p.1 p.2 = 1} :=
    hℓ (measurableSet_singleton 1)
  rw [avgRisk, ← lintegral_indicator_one h_meas, ← h_eq, Measure.lintegral_compProd hℓ]
  rfl

/-- For a loss with values in `{0, 1}`, the law of the loss of an estimator `κ` under the joint
law of the parameter and the estimate is a Bernoulli law (scaled by the total mass) whose mass at
`1` is the average risk. -/
lemma map_uncurry_compProd_of_mem_zero_one (hℓ : Measurable (uncurry ℓ))
    (h01 : ∀ θ y, ℓ θ y = 0 ∨ ℓ θ y = 1) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    (π ⊗ₘ (κ ∘ₖ P)).map (uncurry ℓ)
      = ((π ⊗ₘ (κ ∘ₖ P)) univ - avgRisk ℓ P κ π) • Measure.dirac 0
        + avgRisk ℓ P κ π • Measure.dirac 1 := by
  classical
  rw [avgRisk_eq_measure_of_mem_zero_one hℓ h01]
  set A := {p : Θ × 𝓨 | ℓ p.1 p.2 = 1}
  have hA : MeasurableSet A := hℓ (measurableSet_singleton 1)
  ext s hs
  rw [Measure.map_apply hℓ hs, add_apply, smul_apply, smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul]
  have h_pre : uncurry ℓ ⁻¹' s
      = (if (0 : ℝ≥0∞) ∈ s then Aᶜ else ∅) ∪ (if (1 : ℝ≥0∞) ∈ s then A else ∅) := by
    ext p
    by_cases h0 : (0 : ℝ≥0∞) ∈ s <;> by_cases h1 : (1 : ℝ≥0∞) ∈ s <;>
      rcases h01 p.1 p.2 with hp | hp <;> simp [A, uncurry_def, hp, h0, h1]
  rw [h_pre]
  by_cases h0 : (0 : ℝ≥0∞) ∈ s <;> by_cases h1 : (1 : ℝ≥0∞) ∈ s
  · simp [h0, h1, tsub_add_cancel_of_le (measure_mono (subset_univ A))]
  · simp [h0, h1, measure_compl hA (measure_ne_top _ A)]
  · simp [h0, h1]
  · simp [h0, h1]

end ZeroOneValued

/-! ### The 0-1 loss -/

/-- The 0-1 loss `𝕀{θ ≠ z}`. -/
noncomputable
def zeroOneLoss (θ z : Θ) : ℝ≥0∞ := ({z}ᶜ : Set Θ).indicator 1 θ

lemma zeroOneLoss_apply [DecidableEq Θ] (θ z : Θ) :
    zeroOneLoss θ z = if θ = z then 0 else 1 := by
  by_cases h : θ = z <;> simp [zeroOneLoss, h]

@[simp] lemma zeroOneLoss_self (θ : Θ) : zeroOneLoss θ θ = 0 := by simp [zeroOneLoss]

lemma zeroOneLoss_of_ne {θ z : Θ} (h : θ ≠ z) : zeroOneLoss θ z = 1 := by simp [zeroOneLoss, h]

lemma zeroOneLoss_le_one (θ z : Θ) : zeroOneLoss θ z ≤ 1 :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)

lemma measurable_zeroOneLoss [MeasurableEq Θ] : Measurable (uncurry (zeroOneLoss (Θ := Θ))) := by
  have h_eq : uncurry (zeroOneLoss (Θ := Θ)) = (diagonal Θ)ᶜ.indicator 1 := by
    ext p
    by_cases h : p.1 = p.2 <;> simp [uncurry_def, zeroOneLoss, mem_diagonal_iff, h]
  rw [h_eq]
  exact measurable_one.indicator measurableSet_diagonal.compl

lemma lintegral_zeroOneLoss [MeasurableSingletonClass Θ] (ρ : Measure Θ) (z : Θ) :
    ∫⁻ θ, zeroOneLoss θ z ∂ρ = ρ {z}ᶜ :=
  lintegral_indicator_one (measurableSet_singleton z).compl

/-- The smallest expected 0-1 loss of an action under a finite measure `ρ` is the mass of `ρ`
minus the maximal mass of an atom. -/
lemma iInf_lintegral_zeroOneLoss [MeasurableSingletonClass Θ] [Nonempty Θ] (ρ : Measure Θ)
    [IsFiniteMeasure ρ] :
    ⨅ z, ∫⁻ θ, zeroOneLoss θ z ∂ρ = ρ univ - ⨆ z, ρ {z} := by
  simp_rw [lintegral_zeroOneLoss, measure_compl (measurableSet_singleton _) (measure_ne_top _ _)]
  exact (ENNReal.sub_iSup (measure_ne_top ρ univ)).symm

variable [StandardBorelSpace Θ] [Nonempty Θ] {P : Kernel Θ 𝓧} [IsFiniteKernel P]
  {π : Measure Θ} [IsFiniteMeasure π]

/-- If the estimation problem with the 0-1 loss admits an argmin estimator, then its Bayes risk is
the mass of `P ∘ₘ π` minus the expected maximal posterior probability of a parameter. -/
lemma HasArgminEstimator.bayesRisk_zeroOneLoss_eq_sub (h : HasArgminEstimator zeroOneLoss P π) :
    bayesRisk zeroOneLoss P π = (P ∘ₘ π) univ - ∫⁻ x, ⨆ z, (P†π) x {z} ∂(P ∘ₘ π) := by
  rw [h.bayesRisk_eq measurable_zeroOneLoss]
  simp_rw [iInf_lintegral_zeroOneLoss, measure_univ]
  have h_le x : ⨆ z, (P†π) x {z} ≤ 1 := iSup_le fun z ↦ prob_le_one
  -- the supremum is almost surely attained at the value of an argmin estimator `f`, hence it is
  -- almost everywhere measurable
  obtain ⟨f, hf⟩ := h.exists_isArgminEstimator
  have hf_meas : Measurable fun x ↦ (P†π) x {f x} := (P†π).measurable_kernel_prodMk_left
    (measurableSet_eq_fun measurable_snd (hf.measurable.comp measurable_fst))
  have h_eq : (fun x ↦ ⨆ z, (P†π) x {z}) =ᵐ[P ∘ₘ π] fun x ↦ (P†π) x {f x} := by
    filter_upwards [hf.property] with x hx
    rw [lintegral_zeroOneLoss, iInf_lintegral_zeroOneLoss,
      prob_compl_eq_one_sub (measurableSet_singleton _), measure_univ] at hx
    rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top (h_le x), ← hx,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [lintegral_sub' (hf_meas.aemeasurable.congr h_eq.symm) ?_ (ae_of_all _ h_le), lintegral_one]
  refine ((lintegral_mono h_le).trans_lt ?_).ne
  simp [measure_lt_top]

/-- An estimator that maximizes the posterior probability `z ↦ (P†π) x {z}` for almost every `x`
is an argmin estimator for the 0-1 loss, hence a Bayes estimator. -/
lemma isArgminEstimator_zeroOneLoss_of_posterior {f : 𝓧 → Θ} (hf : Measurable f)
    (h : ∀ᵐ x ∂(P ∘ₘ π), ∀ z, (P†π) x {z} ≤ (P†π) x {f x}) :
    IsArgminEstimator zeroOneLoss P π f := by
  refine ⟨hf, ?_⟩
  filter_upwards [h] with x hx
  simp_rw [lintegral_zeroOneLoss, prob_compl_eq_one_sub (measurableSet_singleton _)]
  exact le_antisymm (le_iInf fun z ↦ tsub_le_tsub_left (hx z) 1) (iInf_le _ _)

section Countable

variable [Countable Θ]

/-- The **generalized Bayes estimator** for the 0-1 loss: for a countable parameter space, an
estimator that maximizes `z ↦ π {z} * (dP_z/d(P ∘ₘ π))(x)` for almost every `x` is an argmin
estimator, hence a Bayes estimator. -/
lemma isArgminEstimator_zeroOneLoss {f : 𝓧 → Θ} (hf : Measurable f)
    (h : ∀ᵐ x ∂(P ∘ₘ π), ∀ z,
      π {z} * (P z).rnDeriv (P ∘ₘ π) x ≤ π {f x} * (P (f x)).rnDeriv (P ∘ₘ π) x) :
    IsArgminEstimator zeroOneLoss P π f := by
  refine isArgminEstimator_zeroOneLoss_of_posterior hf ?_
  filter_upwards [h, posterior_singleton_ae_eq P π] with x hx hpost
  simpa only [hpost] using hx

/-- If the parameter space is countable, the estimation problem with the 0-1 loss admits an argmin
estimator: a measurable maximizer of the posterior probability of the parameter. -/
lemma hasArgminEstimator_zeroOneLoss : HasArgminEstimator zeroOneLoss P π := by
  classical
  have : Encodable Θ := Encodable.ofCountable Θ
  have hg z : Measurable fun x ↦ (P†π) x {z} := (P†π).measurable_coe (measurableSet_singleton z)
  -- `p x n`: the parameter with code `n` maximizes the posterior probability `(P†π) x {·}`
  let p : 𝓧 → ℕ → Prop :=
    fun x n ↦ ∃ z, Encodable.encode z = n ∧ ∀ y, (P†π) x {y} ≤ (P†π) x {z}
  have hp x : ∃ n, p x n := by
    obtain ⟨z, hz⟩ := ((P†π) x).exists_forall_measure_singleton_le
    exact ⟨_, z, rfl, hz⟩
  have hp_meas k : MeasurableSet {x | p x k} := by
    simp only [p, ofPred_exists, ofPred_and, ofPred_forall]
    exact MeasurableSet.iUnion fun z ↦ (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun y ↦ measurableSet_le (hg y) (hg z))
  let f : 𝓧 → Θ := fun x ↦ (Encodable.decode₂ Θ (Nat.find (hp x))).getD (Classical.arbitrary Θ)
  have hf_meas : Measurable f :=
    (measurable_from_nat (f := fun n ↦ (Encodable.decode₂ Θ n).getD (Classical.arbitrary Θ))).comp
      (measurable_find hp hp_meas)
  refine ⟨f, isArgminEstimator_zeroOneLoss_of_posterior hf_meas (ae_of_all _ fun x z ↦ ?_)⟩
  obtain ⟨z', hz'_eq, hz'⟩ := Nat.find_spec (hp x)
  have hfx : f x = z' := by simp [f, ← hz'_eq, Encodable.decode₂_encode]
  rw [hfx]
  exact hz' z

/-- For a countable parameter space, the Bayes risk of the 0-1 loss is
`(P ∘ₘ π)(univ) - ∫⁻ x, ⨆ z, π {z} * (dP_z/d(P ∘ₘ π))(x) ∂(P ∘ₘ π)`. -/
lemma bayesRisk_zeroOneLoss_eq_sub_rnDeriv :
    bayesRisk zeroOneLoss P π
      = (P ∘ₘ π) univ - ∫⁻ x, ⨆ z, π {z} * (P z).rnDeriv (P ∘ₘ π) x ∂(P ∘ₘ π) := by
  rw [hasArgminEstimator_zeroOneLoss.bayesRisk_zeroOneLoss_eq_sub]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [posterior_singleton_ae_eq P π] with x hx
  simp_rw [hx]

/-- For a countable parameter space, a finite set `s` of parameters and weights `w θ ≥ 0` with
`∑ θ ∈ s, w θ = 1`, the Bayes risk of the 0-1 loss is at most
`(P ∘ₘ π)(univ) - (∏ θ ∈ s, π {θ} ^ w θ) * ∫⁻ x, ∏ θ ∈ s, (dP_θ/d(P ∘ₘ π))(x) ^ w θ ∂(P ∘ₘ π)`.
For a finite parameter space, take `s = Finset.univ`. -/
lemma bayesRisk_zeroOneLoss_le_sub_prod {s : Finset Θ} {w : Θ → ℝ} (hw : ∀ θ ∈ s, 0 ≤ w θ)
    (hw_sum : ∑ θ ∈ s, w θ = 1) :
    bayesRisk zeroOneLoss P π
      ≤ (P ∘ₘ π) univ
        - (∏ θ ∈ s, π {θ} ^ w θ) * ∫⁻ x, ∏ θ ∈ s, (P θ).rnDeriv (P ∘ₘ π) x ^ w θ ∂(P ∘ₘ π) := by
  rw [bayesRisk_zeroOneLoss_eq_sub_rnDeriv]
  refine tsub_le_tsub_left ?_ _
  rw [← lintegral_const_mul _ (Finset.measurable_prod _ fun θ _ ↦
    (Measure.measurable_rnDeriv _ _).pow_const _)]
  refine lintegral_mono fun x ↦ ?_
  rw [← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun θ hθ ↦ (ENNReal.mul_rpow_of_nonneg _ _ (hw θ hθ)).symm]
  exact (ENNReal.prod_rpow_le_iSup _ hw hw_sum).trans (iSup₂_le fun θ _ ↦ le_iSup_of_le θ le_rfl)

end Countable

end ProbabilityTheory
