/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrals of affine functions on intervals

For an s-finite measure `μ` on `ℝ`, Tonelli's theorem gives
`∫⁻ x in Ioc a t, (t - x) ∂μ = ∫⁻ s in Ioc a t, μ (Ioc a s)` and
`∫⁻ x in Ioc t b, (x - t) ∂μ = ∫⁻ s in Ioc t b, μ (Ioc s b)`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

public section

open Set

open scoped ENNReal

namespace MeasureTheory

/-- Tonelli: `∫⁻ x in Ioc a t, (t - x) ∂μ = ∫⁻ s in Ioc a t, μ (Ioc a s)`. -/
lemma setLIntegral_Ioc_ofReal_const_sub (μ : Measure ℝ) [SFinite μ] (a t : ℝ) :
    ∫⁻ x in Ioc a t, ENNReal.ofReal (t - x) ∂μ = ∫⁻ s in Ioc a t, μ (Ioc a s) := by
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if x ≤ s then 1 else 0
  have hg : Measurable (Function.uncurry g) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc a t, ∫⁻ s in Ioc a t, g x s = ENNReal.ofReal (t - x) := by
    intro x hx
    have : (fun s ↦ g x s) = (Ici x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
    have : Ici x ∩ Ioc a t = Icc x t := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans_le h.1, h.2⟩⟩
    rw [this, Real.volume_Icc]
  have h2 : ∀ s ∈ Ioc a t, ∫⁻ x in Ioc a t, g x s ∂μ = μ (Ioc a s) := by
    intro s hs
    have : (fun x ↦ g x s) = (Iic s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hs.2⟩⟩
  calc ∫⁻ x in Ioc a t, ENNReal.ofReal (t - x) ∂μ
      = ∫⁻ x in Ioc a t, (∫⁻ s in Ioc a t, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc a t, (∫⁻ x in Ioc a t, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc a t, μ (Ioc a s) := setLIntegral_congr_fun measurableSet_Ioc h2

/-- Tonelli: `∫⁻ x in Ioc t b, (x - t) ∂μ = ∫⁻ s in Ioc t b, μ (Ioc s b)`. -/
lemma setLIntegral_Ioc_ofReal_sub_const (μ : Measure ℝ) [SFinite μ] (t b : ℝ) :
    ∫⁻ x in Ioc t b, ENNReal.ofReal (x - t) ∂μ = ∫⁻ s in Ioc t b, μ (Ioc s b) := by
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if s < x then 1 else 0
  have hg : Measurable (Function.uncurry g) :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc t b, ∫⁻ s in Ioc t b, g x s = ENNReal.ofReal (x - t) := by
    intro x hx
    have : (fun s ↦ g x s) = (Iio x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
    have : Iio x ∩ Ioc t b = Ioo t x := by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans hx.2⟩⟩
    rw [this, Real.volume_Ioo]
  have h2 : ∀ s ∈ Ioc t b, ∫⁻ x in Ioc t b, g x s ∂μ = μ (Ioc s b) := by
    intro s hs
    have : (fun x ↦ g x s) = (Ioi s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hs.1.trans h.1, h.2⟩⟩
  calc ∫⁻ x in Ioc t b, ENNReal.ofReal (x - t) ∂μ
      = ∫⁻ x in Ioc t b, (∫⁻ s in Ioc t b, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc t b, (∫⁻ x in Ioc t b, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc t b, μ (Ioc s b) := setLIntegral_congr_fun measurableSet_Ioc h2

end MeasureTheory
