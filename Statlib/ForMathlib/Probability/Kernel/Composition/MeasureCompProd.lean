/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Statlib.ForMathlib.Convex
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Statlib.ForMathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Composition-products of measures and kernels: singular parts and integrability

## Main statements

* `MeasureTheory.Measure.absolutelyContinuous_compProd_iff_fst`:
  `ρ ≪ μ ⊗ₘ η ↔ ρ.fst ≪ μ ∧ ρ ≪ ρ.fst ⊗ₘ η` for a measure `ρ` on a product space.
* `ProbabilityTheory.singularPart_compProd_left`, `ProbabilityTheory.singularPart_compProd`,
  `ProbabilityTheory.singularPart_compProd_right`: singular part of `μ ⊗ₘ κ` with respect to
  `ν ⊗ₘ η`.
* `ProbabilityTheory.lintegral_singularPart`: integral of the singular parts of kernels, written as
  a singular part of composition-products.
* `ProbabilityTheory.integrable_f_rnDeriv_compProd_iff`: integrability of
  `f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x)` in terms of the integrability of its sections, for convex `f`.
* `ProbabilityTheory.Measure.compProd_univ_toReal`: `((μ ⊗ₘ κ) univ).toReal` as a Bochner
  integral.
* `MeasureTheory.Measure.neZero_compProd`: `NeZero (μ ⊗ₘ κ)` for a nonzero `μ` and a Markov
  kernel `κ`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

lemma singularPart_compProd_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = μ.singularPart ν ⊗ₘ κ := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, Measure.compProd_add_left,
    Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (Measure.AbsolutelyContinuous.compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ fun _ ↦ by rfl
  rw [this, add_zero, Measure.singularPart_eq_self]
  exact Measure.MutuallySingular.compProd_of_left (Measure.mutuallySingular_singularPart _ _) κ κ

/-- A measure `ρ` on a product space is absolutely continuous with respect to `μ ⊗ₘ η` if and only
if its first marginal is absolutely continuous with respect to `μ` and `ρ ≪ ρ.fst ⊗ₘ η`. -/
lemma _root_.MeasureTheory.Measure.absolutelyContinuous_compProd_iff_fst {ρ : Measure (α × β)}
    [IsFiniteMeasure ρ] {μ : Measure α} [SigmaFinite μ] {η : Kernel α β} [IsSFiniteKernel η] :
    ρ ≪ μ ⊗ₘ η ↔ ρ.fst ≪ μ ∧ ρ ≪ ρ.fst ⊗ₘ η := by
  -- `(ν ⊗ₘ η) (s ×ˢ univ) = 0` as soon as `ν s = 0`
  have h_null {ν : Measure α} [SFinite ν] {s : Set α} (hs : MeasurableSet s) (hs0 : ν s = 0) :
      (ν ⊗ₘ η) (Prod.fst ⁻¹' s) = 0 := by
    rw [← Set.prod_univ, Measure.compProd_apply_prod hs .univ, setLIntegral_measure_zero _ _ hs0]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.2.trans (h.1.compProd_left η)⟩
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
    rw [Measure.fst_apply hs]
    exact h (h_null hs hs0)
  -- the part of `μ` singular with respect to `ρ.fst` is also singular with respect to `ρ`
  have hs := Measure.mutuallySingular_singularPart μ ρ.fst
  have h_ms : ρ ⟂ₘ μ.singularPart ρ.fst ⊗ₘ η := by
    refine ⟨Prod.fst ⁻¹' hs.nullSetᶜ, measurable_fst hs.measurableSet_nullSet.compl, ?_, ?_⟩
    · rw [← Measure.fst_apply hs.measurableSet_nullSet.compl, hs.measure_compl_nullSet]
    · rw [← Set.preimage_compl, compl_compl]
      exact h_null hs.measurableSet_nullSet hs.measure_nullSet
  rw [μ.haveLebesgueDecomposition_add ρ.fst, Measure.compProd_add_left, add_comm] at h
  exact (Measure.absolutelyContinuous_of_add_of_mutuallySingular h h_ms).trans
    ((withDensity_absolutelyContinuous _ _).compProd_left η)

section CompProd

open Real Filter MeasurableSpace

open scoped ENNReal NNReal Topology

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section SingularPart

private lemma lintegral_apply_prodMk_preimage {f : α → Set β → ℝ≥0∞} (hf : ∀ a, f a ∅ = 0)
    {s : Set α} (hs : MeasurableSet s) (t : Set β) :
    ∫⁻ a, f a (Prod.mk a ⁻¹' s ×ˢ t) ∂μ = ∫⁻ a in s, f a t ∂μ := by
  rw [← lintegral_indicator hs _]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha, hf]

variable [CountableOrCountablyGenerated α β]

private lemma singularPart_compProd'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ η.withDensity (κ.rnDeriv η) + μ.singularPart ν ⊗ₘ κ.singularPart η
        + ν.withDensity (∂μ/∂ν) ⊗ₘ κ.singularPart η := by
  conv_lhs => rw [← κ.rnDeriv_add_singularPart η, Measure.compProd_add_right,
    μ.haveLebesgueDecomposition_add ν]
  simp_rw [Measure.compProd_add_left, Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ η.withDensity (κ.rnDeriv η)).singularPart (ν ⊗ₘ η) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (Measure.AbsolutelyContinuous.compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ (Kernel.withDensity_absolutelyContinuous _)
  rw [this, add_zero, ← add_assoc]
  congr
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart ν)
      (η.withDensity (κ.rnDeriv η)) η
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart ν)
      (κ.singularPart η) η
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_right (ν.withDensity (∂μ/∂ν)) ν
      (.of_forall <| κ.mutuallySingular_singularPart _)

lemma singularPart_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ η.withDensity (κ.rnDeriv η) + μ ⊗ₘ κ.singularPart η := by
  rw [singularPart_compProd'']
  have : (μ ⊗ₘ κ.singularPart η) = (μ.singularPart ν ⊗ₘ κ.singularPart η)
        + (ν.withDensity (∂μ/∂ν) ⊗ₘ κ.singularPart η) := by
    rw [← Measure.compProd_add_left, ← μ.haveLebesgueDecomposition_add ν]
  rw [this]
  abel

lemma singularPart_compProd_right (μ : Measure α)
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = μ ⊗ₘ κ.singularPart η :=
  (Measure.eq_singularPart (Kernel.measurable_rnDeriv κ η)
    (Measure.MutuallySingular.compProd_of_right μ μ
      (.of_forall <| Kernel.mutuallySingular_singularPart κ η))
    (compProd_eq_compProd_singularPart_add_withDensity μ κ η)).symm

lemma setLIntegral_singularPart (μ : Measure α) [SFinite μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (κ a).singularPart (η a) t ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd_right, Measure.compProd_apply (hs.prod ht)]
  simp only [Kernel.singularPart_eq_singularPart_measure]
  rw [lintegral_apply_prodMk_preimage (fun _ ↦ by simp) hs]

lemma lintegral_singularPart (μ : Measure α) [SFinite μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, (κ a).singularPart (η a) s ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (.univ ×ˢ s) := by
  rw [← setLIntegral_univ, setLIntegral_singularPart _ _ _ .univ hs]

end SingularPart

section Integrable

variable {E : Type*}

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ := by
  rw [Measure.compProd] at hf
  simpa using hf.integral_compProd

lemma integrable_f_rnDeriv_compProd_iff_of_nonneg [IsFiniteMeasure ν] [IsFiniteKernel η]
    (h_ae : AEStronglyMeasurable (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η))
    (h_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal ∂(η a)) ν := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff h_ae] at h
    exact ⟨h.1, h_int⟩
  · rw [Measure.integrable_compProd_iff h_ae]
    refine ⟨h1, ?_⟩
    convert h2 using 4 with a b
    rw [norm_of_nonneg]
    exact h_nonneg _ ENNReal.toReal_nonneg

lemma integrable_add_affine_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : ℝ → ℝ) (a b : ℝ) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal + a * (μ.rnDeriv ν x).toReal + b) ν
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  have h_int : Integrable (fun x ↦ a * (μ.rnDeriv ν x).toReal + b) ν :=
    (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  simp_rw [add_assoc]
  exact integrable_add_iff_integrable_left' h_int

lemma integrable_sub_affine_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : ℝ → ℝ) (a b : ℝ) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal - (a * (μ.rnDeriv ν x).toReal + b)) ν
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  simp_rw [sub_eq_add_neg, neg_add, ← neg_mul, ← add_assoc]
  rw [integrable_add_affine_iff f]

lemma integrable_f_rnDeriv_compProd_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal ∂(η a)) ν := by
  have h_meas_rnDeriv : Measurable fun x ↦ ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have h_meas : Measurable fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal :=
    (h_cvx.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).measurable_comp_of_nonneg
      h_meas_rnDeriv fun _ ↦ ENNReal.toReal_nonneg
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ f x := h_cvx.exists_affine_le
  simp only [Set.mem_Ici] at h
  rw [← integrable_sub_affine_iff f c c']
  -- the function `f y - (c * y + c')` is nonnegative on `[0, ∞)`
  rw [integrable_f_rnDeriv_compProd_iff_of_nonneg (f := fun y ↦ f y - (c * y + c'))]
  rotate_left
  · exact (h_meas.sub ((h_meas_rnDeriv.const_mul c).add_const c')).aestronglyMeasurable
  · simpa using h
  have h_int' : Integrable (fun p ↦ ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p).toReal) (ν ⊗ₘ η) :=
    Measure.integrable_toReal_rnDeriv
  rw [Measure.integrable_compProd_iff] at h_int'
  swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
  have h_int''' : ∀ᵐ a ∂ν,
      Integrable (fun x ↦ c * ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal + c') (η a) := by
    filter_upwards [h_int'.1] with a h_int''
    exact ((h_int''.const_mul _).add (integrable_const _))
  -- The goal has shape `(P₁ ∧ Q₁) ↔ (P₂ ↔ Q₂)`. We prove first `P₁ ↔ P₂`.
  have h_left : (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal
        - (c * (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal + c')) (η a))
      ↔ ∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a) := by
    refine Filter.eventually_congr ?_
    filter_upwards [h_int'''] with a h_int'''
    simp_rw [sub_eq_add_neg]
    exact integrable_add_iff_integrable_left' h_int'''.fun_neg
  rw [h_left, and_congr_right_iff]
  -- Now we have proved `P₁ ↔ P₂` and it remains to prove `P₂ → (Q₁ ↔ Q₂)`.
  intro h_int
  have : ∀ᵐ a ∂ν, ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal
        - (c * (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal + c') ∂η a
      = ∫ b, f ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b)).toReal ∂η a
        - ∫ b, c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b)).toReal + c' ∂η a := by
    filter_upwards [h_int, h_int'''] with a h_int h_int'''
    rw [← integral_sub h_int h_int''']
  rw [integrable_congr this]
  simp_rw [sub_eq_add_neg]
  rw [integrable_add_iff_integrable_left']
  -- `⊢ Integrable (fun x ↦ -∫ (b : β), c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal + c' ∂η x) ν`
  have h_int_compProd :
      Integrable (fun x ↦ ∫ b, ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal ∂η x) ν := by
    convert h_int'.2 with a b
    rw [norm_of_nonneg ENNReal.toReal_nonneg]
  have : ∀ᵐ x ∂ν, -∫ b, c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal + c' ∂η x
      = -c * ∫ b, ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal ∂η x
        - c' * (η x .univ).toReal := by
    filter_upwards [h_int'.1] with x h_int'
    rw [integral_add _ (integrable_const _)]
    swap; · exact h_int'.const_mul _
    simp only [integral_const, smul_eq_mul, neg_add_rev, neg_mul]
    rw [add_comm, mul_comm]
    congr 1
    rw [mul_comm c, ← smul_eq_mul, ← integral_smul_const]
    simp_rw [smul_eq_mul, mul_comm _ c]
  rw [integrable_congr this]
  refine Integrable.sub (h_int_compProd.const_mul _) (Integrable.const_mul ?_ _)
  simp_rw [← measureReal_def, ← integral_indicator_one MeasurableSet.univ]
  simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply]
  exact Integrable.integral_compProd' (f := fun _ ↦ 1) (integrable_const _)

variable [CountableOrCountablyGenerated α β]

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  rw [integrable_f_rnDeriv_compProd_iff' h_cvx]
  congr! 1
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · filter_upwards [h_ae_eq, h] with a ha h
      rwa [integrable_congr ha.symm]
    · filter_upwards [h_ae_eq, h] with a ha h
      rwa [integrable_congr ha]
  · refine integrable_congr ?_
    filter_upwards [h_ae_eq] with a ha
    exact integral_congr_ae ha

lemma integrable_f_rnDeriv_compProd_right_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
      ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ := by
  rw [integrable_f_rnDeriv_compProd_iff h_cvx]
  have h_one := μ.rnDeriv_self
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]

end Integrable

lemma Measure.compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prodMk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma Measure.compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) .univ).toReal = ∫ x, (κ x .univ).toReal ∂μ :=
  compProd_apply_toReal .univ

/-- The composition-product of a nonzero measure and a Markov kernel is nonzero. -/
instance _root_.MeasureTheory.Measure.neZero_compProd [SFinite μ] [NeZero μ] [IsMarkovKernel κ] :
    NeZero (μ ⊗ₘ κ) :=
  ⟨fun h ↦ NeZero.ne μ (by
    rw [← Measure.measure_univ_eq_zero, ← Measure.compProd_apply_univ (κ := κ), h,
      FunLike.coe_zero, Pi.zero_apply])⟩

end CompProd

end ProbabilityTheory
