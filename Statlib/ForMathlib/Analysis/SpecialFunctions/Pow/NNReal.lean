/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weighted geometric means in `ℝ≥0∞`

## Main statements

* `ENNReal.rpow_sum_of_nonneg`: `x ^ ∑ i ∈ s, w i = ∏ i ∈ s, x ^ w i` for nonnegative exponents.
* `ENNReal.prod_rpow_le_iSup`: a weighted geometric mean is at most the maximum.
* `ENNReal.min_le_rpow_mul_rpow`: for `a ∈ [0, 1]`, `min x y ≤ x ^ a * y ^ (1 - a)`.
* `ENNReal.min_eq_rpow_mul_rpow_mul_min`: for `u, v ∈ (0, ∞)` and `a : ℝ`,
  `min u v = u ^ a * v ^ (1 - a) * min ((u / v) ^ (1 - a)) ((v / u) ^ a)`.
-/

@[expose] public section

namespace ENNReal

variable {a : ℝ}

/-- `x ^ ∑ i ∈ s, w i = ∏ i ∈ s, x ^ w i` for nonnegative exponents. This is the analogue of
`Real.rpow_sum_of_nonneg`. -/
lemma rpow_sum_of_nonneg {ι : Type*} (x : ℝ≥0∞) {s : Finset ι} {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    x ^ ∑ i ∈ s, w i = ∏ i ∈ s, x ^ w i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ← ih fun j hj ↦ hw j (by simp [hj]),
      ENNReal.rpow_add_of_nonneg _ _ (hw i (by simp))
        (Finset.sum_nonneg fun j hj ↦ hw j (by simp [hj]))]

/-- A weighted geometric mean is at most the maximum: if `w i ≥ 0` for `i ∈ s` and
`∑ i ∈ s, w i = 1`, then `∏ i ∈ s, f i ^ w i ≤ ⨆ i ∈ s, f i`. -/
lemma prod_rpow_le_iSup {ι : Type*} {s : Finset ι} (f : ι → ℝ≥0∞) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw_sum : ∑ i ∈ s, w i = 1) :
    ∏ i ∈ s, f i ^ w i ≤ ⨆ i ∈ s, f i :=
  calc ∏ i ∈ s, f i ^ w i
  _ ≤ ∏ i ∈ s, (⨆ j ∈ s, f j) ^ w i :=
    Finset.prod_le_prod fun i hi ↦ ENNReal.rpow_le_rpow (le_biSup f hi) (hw i hi)
  _ = ⨆ i ∈ s, f i := by rw [← rpow_sum_of_nonneg _ hw, hw_sum, ENNReal.rpow_one]

/-- The minimum of two numbers is at most any of their weighted geometric means:
for `a ∈ [0, 1]`, `min x y ≤ x ^ a * y ^ (1 - a)`. -/
lemma min_le_rpow_mul_rpow (x y : ℝ≥0∞) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    min x y ≤ x ^ a * y ^ (1 - a) := by
  have ha1' : 0 ≤ 1 - a := by linarith
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    calc x = x ^ a * x ^ (1 - a) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ ha0 ha1']; simp
      _ ≤ x ^ a * y ^ (1 - a) := by gcongr
  · rw [min_eq_right h]
    calc y = y ^ a * y ^ (1 - a) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ ha0 ha1']; simp
      _ ≤ x ^ a * y ^ (1 - a) := by gcongr

/-- For `u, v ∈ (0, ∞)` and `a : ℝ`,
`min u v = u ^ a * v ^ (1 - a) * min ((u / v) ^ (1 - a)) ((v / u) ^ a)`. -/
lemma min_eq_rpow_mul_rpow_mul_min {u v : ℝ≥0∞} (hu0 : u ≠ 0) (hu : u ≠ ∞)
    (hv0 : v ≠ 0) (hv : v ≠ ∞) (a : ℝ) :
    min u v = u ^ a * v ^ (1 - a) * min ((u / v) ^ (1 - a)) ((v / u) ^ a) := by
  have h_cancel {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ∞) (b : ℝ) : x ^ b * (x ^ b)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hx0) hx).ne'
      (ENNReal.rpow_ne_top_of_ne_zero hx0 hx)
  rw [Monotone.map_min (mul_right_mono : Monotone (u ^ a * v ^ (1 - a) * ·))]
  congr 1
  · rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_zero hu0 (ENNReal.inv_ne_zero.mpr hv),
      ENNReal.inv_rpow]
    calc u = u ^ a * u ^ (1 - a) * (v ^ (1 - a) * (v ^ (1 - a))⁻¹) := by
          rw [← ENNReal.rpow_add _ _ hu0 hu, h_cancel hv0 hv]
          simp
      _ = u ^ a * v ^ (1 - a) * (u ^ (1 - a) * (v ^ (1 - a))⁻¹) := by ring
  · rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_zero hv0 (ENNReal.inv_ne_zero.mpr hu),
      ENNReal.inv_rpow]
    calc v = v ^ a * v ^ (1 - a) * (u ^ a * (u ^ a)⁻¹) := by
          rw [← ENNReal.rpow_add _ _ hv0 hv, h_cancel hu0 hu]
          simp
      _ = u ^ a * v ^ (1 - a) * (v ^ a * (u ^ a)⁻¹) := by ring

end ENNReal
