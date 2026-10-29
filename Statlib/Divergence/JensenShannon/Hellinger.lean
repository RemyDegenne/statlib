/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Hellinger.Basic
public import Statlib.Divergence.JensenShannon.Basic

/-!
# Inequalities between the Jensen-Shannon and the Hellinger divergences

For finite measures `μ`, `ν`, `α ∈ [0, 1]` and `β ∈ (0, 1)`,
`JS_α(μ, ν) ≤ (1 - α) ^ (1 - β) * α ^ β / (β ^ (1 - β) * (1 - β) ^ β) * (1 - β) * H_β(μ, ν)`.

Both divergences are f-divergences, for functions `f` and `g` which vanish at `1` together with
their derivatives. The inequality follows from a comparison of the second derivatives
(`fDiv_ofReal_le_of_deriv2_le`): the supremum of `f'' / g''` is bounded by the weighted
arithmetic-geometric mean inequality.

## Main statements

* `jensenShannon_le_hellingerDiv`: the inequality above (Theorem 3 of the note cited below).
* `jensenShannon_le_hellingerDiv_self`: the case `β = α`,
  `JS_α(μ, ν) ≤ ((1 - α) / α) ^ (1 - 2 * α) * (1 - α) * H_α(μ, ν)`.
* `jensenShannon_le_mul_hellingerDiv_one_sub`: the case `β = 1 - α`,
  `JS_α(μ, ν) ≤ α * H_{1 - α}(μ, ν)`.
* `jensenShannon_le_mul_klDiv`: the limiting case `β = 1`, `JS_α(μ, ν) ≤ α * KL(μ, ν)`.
* `jensenShannon_le_rpow_mul_hellingerDiv_one_sub`: for `β ∈ [0, 1/2]`,
  `JS_α(μ, ν) ≤ α ^ (1 - β) * H_{1 - β}(μ, ν)` (Corollary 4 of the note).

## References

* R. Degenne, *An inequality between Jensen-Shannon and Hellinger divergences*, short note
  (Theorem 3 and Corollary 4).
* A. Pensia, V. Jog, P.-L. Loh, *The sample complexity of simple binary hypothesis testing*,
  COLT 2024. They prove `JS_α(μ, ν) ≤ 32 α ^ (1 - 2λ) H_{1-λ}(μ, ν)` for `α, λ ∈ (0, 1/2]`,
  a bound of the same form as Corollary 4 with a larger constant.
-/

@[expose] public section

open Real MeasureTheory Filter Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {α : ℝ≥0} {β : ℝ}

section Real

variable {a x : ℝ}

/-- The constant `C = (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β)` of
`jensenShannon_le_hellingerDiv` is nonnegative. -/
private lemma jensenShannonHellinger_const_nonneg (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    0 ≤ (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β) := by
  have h1a : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have h1β : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  positivity

/-- The key inequality between the second derivatives of the functions defining `JS_a` and
`(1 - β) * H_β`: for `x > 0`,
`a * (1 - a) / (x * (a * x + (1 - a))) ≤ C * (1 - β) * (β * x ^ (β - 2))`, where
`C = (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β)`. This is the weighted
arithmetic-geometric mean inequality applied to `a * x / (1 - β)` and `(1 - a) / β` with weights
`1 - β` and `β`. -/
private lemma deriv2_jensenShannonFun_le (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) :
    a * (1 - a) / (x * (a * x + (1 - a)))
      ≤ (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β) * (1 - β) * (β * x ^ (β - 2)) := by
  have h1β : 0 < 1 - β := sub_pos.mpr hβ1
  have hC := jensenShannonHellinger_const_nonneg ha0 ha1 hβ0.le hβ1.le
  have h_rhs_nonneg : 0 ≤ (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β) * (1 - β)
      * (β * x ^ (β - 2)) := by
    positivity
  -- the cases `a = 0` and `a = 1` are trivial
  rcases ha0.eq_or_lt with rfl | ha0
  · simpa using h_rhs_nonneg
  rcases ha1.eq_or_lt with rfl | ha1
  · simpa using h_rhs_nonneg
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  set m := a * x + (1 - a) with hm_def
  have hm : 0 < m := by positivity
  -- weighted AM-GM inequality
  have h_amgm : a ^ (1 - β) * x ^ (1 - β) * (1 - a) ^ β
      ≤ m * ((1 - β) ^ (1 - β) * β ^ β) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - β) (w₂ := β)
      (p₁ := a * x / (1 - β)) (p₂ := (1 - a) / β) h1β.le hβ0.le (by positivity) (by positivity)
      (by ring)
    have h_sum : (1 - β) * (a * x / (1 - β)) + β * ((1 - a) / β) = m := by
      rw [hm_def]
      field_simp
    rw [h_sum, Real.div_rpow (by positivity) h1β.le, Real.div_rpow h1a.le hβ0.le,
      Real.mul_rpow ha0.le hx.le, div_mul_div_comm, div_le_iff₀ (by positivity)] at h
    exact h
  have hP : 0 < a ^ (1 - β) * x ^ (1 - β) * (1 - a) ^ β := by positivity
  have hK : 0 < (1 - β) ^ (1 - β) * β ^ β := by positivity
  calc a * (1 - a) / (x * m)
  _ ≤ a * (1 - a) * ((1 - β) ^ (1 - β) * β ^ β) / (x * (a ^ (1 - β) * x ^ (1 - β) * (1 - a) ^ β))
      := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ a * (1 - a) * x := by positivity
    calc a * (1 - a) * (x * (a ^ (1 - β) * x ^ (1 - β) * (1 - a) ^ β))
    _ = a * (1 - a) * x * (a ^ (1 - β) * x ^ (1 - β) * (1 - a) ^ β) := by ring
    _ ≤ a * (1 - a) * x * (m * ((1 - β) ^ (1 - β) * β ^ β)) := by gcongr
    _ = a * (1 - a) * ((1 - β) ^ (1 - β) * β ^ β) * (x * m) := by ring
  _ = (1 - a) ^ (1 - β) * a ^ β / (β ^ (1 - β) * (1 - β) ^ β) * (1 - β) * (β * x ^ (β - 2)) := by
    rw [Real.rpow_sub ha0 1 β, Real.rpow_sub h1a 1 β,
      Real.rpow_sub h1β 1 β, Real.rpow_sub hβ0 1 β, Real.rpow_sub hx 1 β, Real.rpow_sub hx β 2,
      Real.rpow_one, Real.rpow_one, Real.rpow_one, Real.rpow_one, Real.rpow_one, Real.rpow_two]
    have : 0 < a ^ β := by positivity
    have : 0 < (1 - a) ^ β := by positivity
    have : 0 < (1 - β) ^ β := by positivity
    have : 0 < β ^ β := by positivity
    have : 0 < x ^ β := by positivity
    field_simp

end Real

section JensenShannonHellinger

/-- **Inequality between the Jensen-Shannon and the Hellinger divergences.**
For `α ∈ [0, 1]` and `β ∈ (0, 1)`,
`JS_α(μ, ν) ≤ (1 - α) ^ (1 - β) * α ^ β / (β ^ (1 - β) * (1 - β) ^ β) * ((1 - β) * H_β(μ, ν))`. -/
theorem jensenShannon_le_hellingerDiv (hα : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    jensenShannon α μ ν
      ≤ ENNReal.ofReal ((1 - α) ^ (1 - β) * α ^ β / (β ^ (1 - β) * (1 - β) ^ β))
        * (ENNReal.ofReal (1 - β) * hellingerDiv β μ ν) := by
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have hC : 0 ≤ (1 - (α : ℝ)) ^ (1 - β) * (α : ℝ) ^ β / (β ^ (1 - β) * (1 - β) ^ β) :=
    jensenShannonHellinger_const_nonneg α.coe_nonneg hα1 hβ0.le hβ1.le
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC, jensenShannon_eq_fDiv hα, hellingerDiv,
    jensenShannonDivFun_of_le_one hα, hellingerDivFun_of_pos hβ0]
  refine fDiv_ofReal_le_of_deriv2_le
    (c := ((1 - α) ^ (1 - β) * α ^ β / (β ^ (1 - β) * (1 - β) ^ β) * (1 - β)).toNNReal) _ _ _ _
    (fun x hx ↦ hasDerivAt_jensenShannonFun α.coe_nonneg hα1 hx)
    (fun x hx ↦ hasDerivAt_deriv_jensenShannonFun α.coe_nonneg hα1 hx)
    (fun x hx ↦ hasDerivAt_hellingerFun_of_ne_one hβ1.ne hx.ne')
    (fun x hx ↦ hasDerivAt_deriv_hellingerFun hβ1.ne hx.ne') (by simp) (fun x hx ↦ ?_) μ ν
  rw [Real.coe_toNNReal _ (mul_nonneg hC (sub_nonneg.mpr hβ1.le))]
  exact deriv2_jensenShannonFun_le α.coe_nonneg hα1 hβ0 hβ1 hx

/-- The case `β = α` of `jensenShannon_le_hellingerDiv`:
`JS_α(μ, ν) ≤ ((1 - α) / α) ^ (1 - 2 * α) * ((1 - α) * H_α(μ, ν))`. -/
theorem jensenShannon_le_hellingerDiv_self (hα : α ≤ 1) (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    jensenShannon α μ ν
      ≤ ENNReal.ofReal (((1 - α) / α) ^ (1 - 2 * (α : ℝ)))
        * (ENNReal.ofReal (1 - α) * hellingerDiv α μ ν) := by
  rcases eq_zero_or_pos α with rfl | hα0
  · simp
  rcases hα.eq_or_lt with rfl | hα1
  · simp
  have hα0' : (0 : ℝ) < α := by exact_mod_cast hα0
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have h1α : (0 : ℝ) < 1 - α := sub_pos.mpr hα1'
  convert jensenShannon_le_hellingerDiv hα1.le hα0' hα1' μ ν using 3
  rw [Real.div_rpow h1α.le hα0'.le, show 1 - 2 * (α : ℝ) = (1 - α) - α by ring,
    Real.rpow_sub h1α, Real.rpow_sub hα0']
  have : 0 < (1 - (α : ℝ)) ^ (α : ℝ) := by positivity
  have : 0 < (α : ℝ) ^ (α : ℝ) := by positivity
  have : 0 < (α : ℝ) ^ (1 - (α : ℝ)) := by positivity
  field_simp

/-- The case `β = 1 - α` of `jensenShannon_le_hellingerDiv`: `JS_α(μ, ν) ≤ α * H_{1 - α}(μ, ν)`.
-/
theorem jensenShannon_le_mul_hellingerDiv_one_sub (hα : α ≤ 1) (μ ν : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    jensenShannon α μ ν ≤ α * hellingerDiv (1 - α) μ ν := by
  rcases eq_zero_or_pos α with rfl | hα0
  · simp
  rcases hα.eq_or_lt with rfl | hα1
  · simp
  have hα0' : (0 : ℝ) < α := by exact_mod_cast hα0
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have h1α : (0 : ℝ) < 1 - α := sub_pos.mpr hα1'
  convert jensenShannon_le_hellingerDiv hα1.le h1α (by linarith) μ ν using 1
  rw [sub_sub_cancel, ENNReal.ofReal_coe_nnreal, ← mul_assoc, div_self (by positivity),
    ENNReal.ofReal_one, one_mul]

/-- The limiting case `β = 1` of `jensenShannon_le_hellingerDiv`: `JS_α(μ, ν) ≤ α * KL(μ, ν)`. -/
theorem jensenShannon_le_mul_klDiv (hα : α ≤ 1) (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    jensenShannon α μ ν ≤ α * klDiv μ ν := by
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  rw [jensenShannon_eq_fDiv hα, klDiv_eq_fDiv, jensenShannonDivFun_of_le_one hα, klDivFun]
  refine fDiv_ofReal_le_of_deriv2_le _ _ _ _
    (fun x hx ↦ hasDerivAt_jensenShannonFun α.coe_nonneg hα1 hx)
    (fun x hx ↦ hasDerivAt_deriv_jensenShannonFun α.coe_nonneg hα1 hx)
    (fun x hx ↦ hasDerivAt_klFun hx.ne') (fun x hx ↦ Real.hasDerivAt_log hx.ne') (by simp)
    (fun x hx ↦ ?_) μ ν
  -- `α * (1 - α) / (x * (α * x + (1 - α))) ≤ α / x` since `1 - α ≤ α * x + (1 - α)`
  have h1α : 0 ≤ 1 - (α : ℝ) := sub_nonneg.mpr hα1
  have h_le : 1 - (α : ℝ) ≤ α * x + (1 - α) := le_add_of_nonneg_left (by positivity)
  rw [mul_div_mul_comm, ← div_eq_mul_inv]
  exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ h_le (h1α.trans h_le))

/-- For `β ∈ [0, 1/2]`, `JS_α(μ, ν) ≤ α ^ (1 - β) * H_{1 - β}(μ, ν)`. This is the form of the
inequality that enters bounds on the sample complexity of simple binary hypothesis testing with
the prior `(α, 1 - α)`, as in the work of Pensia, Jog and Loh cited in the module docstring. -/
theorem jensenShannon_le_rpow_mul_hellingerDiv_one_sub (hα : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2) (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    jensenShannon α μ ν ≤ ENNReal.ofReal ((α : ℝ) ^ (1 - β)) * hellingerDiv (1 - β) μ ν := by
  rcases hβ0.eq_or_lt with rfl | hβ0
  · simpa using jensenShannon_le_mul_klDiv hα μ ν
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have h1β : 0 < 1 - β := by linarith
  refine (jensenShannon_le_hellingerDiv hα h1β (by linarith) μ ν).trans ?_
  have hC : 0 ≤ (1 - (α : ℝ)) ^ (1 - (1 - β)) * (α : ℝ) ^ (1 - β)
      / ((1 - β) ^ (1 - (1 - β)) * (1 - (1 - β)) ^ (1 - β)) :=
    jensenShannonHellinger_const_nonneg α.coe_nonneg hα1 h1β.le (by linarith)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
  gcongr
  rw [sub_sub_cancel]
  -- `C * β = α ^ (1 - β) * (1 - α) ^ β * (β / (1 - β)) ^ β ≤ α ^ (1 - β)`
  have h_eq : (1 - (α : ℝ)) ^ β * (α : ℝ) ^ (1 - β) / ((1 - β) ^ β * β ^ (1 - β)) * β
      = (α : ℝ) ^ (1 - β) * ((1 - α) ^ β * (β ^ β / (1 - β) ^ β)) := by
    rw [Real.rpow_sub hβ0, Real.rpow_one]
    have : 0 < β ^ β := by positivity
    have : 0 < (1 - β) ^ β := by positivity
    field_simp
  rw [h_eq]
  refine mul_le_of_le_one_right (by positivity) ?_
  have h_ratio : β ^ β / (1 - β) ^ β ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact Real.rpow_le_rpow hβ0.le (by linarith) hβ0.le
  exact (mul_le_of_le_one_left (by positivity)
    (Real.rpow_le_one (sub_nonneg.mpr hα1) (by simp) hβ0.le)).trans h_ratio

end JensenShannonHellinger

end ProbabilityTheory
