/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.Conj
public import Statlib.Divergence.KullbackLeibler.Basic

/-!
# The Jensen-Shannon divergence

For `α ∈ [0, 1]`, the Jensen-Shannon divergence of weight `α` between two finite measures `μ`
and `ν` is
`JS_α(μ, ν) = α * KL(μ, α • μ + (1 - α) • ν) + (1 - α) * KL(ν, α • μ + (1 - α) • ν)`.
It is the f-divergence for the function
`x ↦ α * x * log x - (α * x + 1 - α) * log (α * x + 1 - α)`.

## Main definitions

* `jensenShannon α μ ν`: the Jensen-Shannon divergence of weight `α` between `μ` and `ν`.
* `jensenShannonFun α`: the real function
  `x ↦ α * (x * log x) - (α * x + (1 - α)) * log (α * x + (1 - α))`.
* `jensenShannonDivFun α`: the divergence function built from `jensenShannonFun α`.

## Main statements

* `jensenShannon_eq_fDiv`: the Jensen-Shannon divergence is the f-divergence for
  `jensenShannonDivFun α`.
* `jensenShannon_symm`: `JS_α(μ, ν) = JS_{1 - α}(ν, μ)`.
* `jensenShannon_eq_zero_iff`: for `0 < α < 1`, `JS_α(μ, ν) = 0` if and only if `μ = ν`.
* `jensenShannon_comp_right_le`, `jensenShannon_map_le`: data processing inequalities.
* `hasDerivAt_jensenShannonFun`, `hasDerivAt_deriv_jensenShannonFun`: the first two derivatives of
  `jensenShannonFun α`, which are `α * log x - α * log (α * x + (1 - α))` and
  `α * (1 - α) / (x * (α * x + (1 - α)))`.

## Implementation notes

The weight `α` is an element of `ℝ≥0`, as in the lemmas about mixtures of measures
`fDiv_smul_add_smul_right` and `fDiv_smul_add_smul_right_self`. The definition is meant for
`α ≤ 1`; for `α > 1`, the truncated subtraction gives `1 - α = 0`.

## References

* J. Lin, *Divergence measures based on the Shannon entropy*, IEEE Transactions on Information
  Theory 37(1) (1991).
-/

@[expose] public section

open Real MeasureTheory Filter Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}
  {α : ℝ≥0}

section JensenShannonFun

variable {a x : ℝ}

/-- The function `x ↦ a * (x * log x) - (a * x + (1 - a)) * log (a * x + (1 - a))`, whose
f-divergence is the Jensen-Shannon divergence of weight `a`. -/
noncomputable def jensenShannonFun (a : ℝ) (x : ℝ) : ℝ :=
  a * (x * log x) - (a * x + (1 - a)) * log (a * x + (1 - a))

@[simp]
lemma jensenShannonFun_one (a : ℝ) : jensenShannonFun a 1 = 0 := by
  simp [jensenShannonFun]

private lemma mul_add_one_sub_pos (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) :
    0 < a * x + (1 - a) := by
  rcases ha0.eq_or_lt with rfl | ha0
  · simp
  · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hx) (sub_nonneg.mpr ha1)

lemma hasDerivAt_jensenShannonFun (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) :
    HasDerivAt (jensenShannonFun a) (a * log x - a * log (a * x + (1 - a))) x := by
  have hm := mul_add_one_sub_pos ha0 ha1 hx
  have h_aff : HasDerivAt (fun x ↦ a * x + (1 - a)) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const (1 - a)
  have h1 : HasDerivAt (fun x ↦ a * (x * log x)) (a * (log x + 1)) x :=
    (Real.hasDerivAt_mul_log hx.ne').const_mul a
  have h2 : HasDerivAt (fun y ↦ (a * y + (1 - a)) * log (a * y + (1 - a)))
      (a * log (a * x + (1 - a)) + (a * x + (1 - a)) * (a / (a * x + (1 - a)))) x :=
    h_aff.mul (h_aff.log hm.ne')
  refine (h1.sub h2).congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_deriv_jensenShannonFun (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) :
    HasDerivAt (fun x ↦ a * log x - a * log (a * x + (1 - a)))
      (a * (1 - a) / (x * (a * x + (1 - a)))) x := by
  have hm := mul_add_one_sub_pos ha0 ha1 hx
  have h_aff : HasDerivAt (fun x ↦ a * x + (1 - a)) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const (1 - a)
  convert ((Real.hasDerivAt_log hx.ne').const_mul a).sub ((h_aff.log hm.ne').const_mul a) using 1
  field_simp
  ring

lemma convexOn_jensenShannonFun (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ConvexOn ℝ (Ioi 0) (jensenShannonFun a) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (f' := fun x ↦ a * log x - a * log (a * x + (1 - a)))
    (f'' := fun x ↦ a * (1 - a) / (x * (a * x + (1 - a))))
    (fun x hx ↦ (hasDerivAt_jensenShannonFun ha0 ha1 hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_jensenShannonFun ha0 ha1 hx).hasDerivWithinAt
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_deriv_jensenShannonFun ha0 ha1 hx).hasDerivWithinAt
  · rw [interior_Ioi] at hx
    have hm := mul_add_one_sub_pos ha0 ha1 hx
    exact div_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha1)) (mul_pos hx hm).le

/-- `jensenShannonFun a` is the weighted sum of the functions of the f-divergence representations
of `KL(μ, a • μ + (1 - a) • ν)` and `KL(ν, a • μ + (1 - a) • ν)`. -/
lemma jensenShannonFun_eq_add (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) :
    jensenShannonFun a x
      = a * ((a * x + (1 - a)) * klFun (x / (a * x + (1 - a))))
        + (1 - a) * ((a * x + (1 - a)) * klFun (a * x + (1 - a))⁻¹) := by
  have hm := mul_add_one_sub_pos ha0 ha1 hx
  simp only [jensenShannonFun, klFun_apply, Real.log_div hx.ne' hm.ne', Real.log_inv]
  field_simp
  ring

end JensenShannonFun

/-- The divergence function of the Jensen-Shannon divergence of weight `α`: for `α ≤ 1`, it is
the `DivFunction` built from `jensenShannonFun α`. It is `0` for `α > 1`. -/
noncomputable def jensenShannonDivFun (α : ℝ≥0) : DivFunction :=
  if hα : α ≤ 1 then
    DivFunction.ofReal (jensenShannonFun α)
      (convexOn_jensenShannonFun α.coe_nonneg (by exact_mod_cast hα)) (jensenShannonFun_one α)
  else 0

lemma jensenShannonDivFun_of_le_one (hα : α ≤ 1) :
    jensenShannonDivFun α = DivFunction.ofReal (jensenShannonFun α)
      (convexOn_jensenShannonFun α.coe_nonneg (by exact_mod_cast hα)) (jensenShannonFun_one α) :=
  dite_eq_left hα

lemma jensenShannonDivFun_apply (hα : α ≤ 1) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    jensenShannonDivFun α x = ENNReal.ofReal (jensenShannonFun α x.toReal) := by
  rw [jensenShannonDivFun_of_le_one hα, DivFunction.ofReal_apply hx0 hx_top]

/-- The Jensen-Shannon divergence of weight `α` between two measures `μ` and `ν`:
`α * KL(μ, α • μ + (1 - α) • ν) + (1 - α) * KL(ν, α • μ + (1 - α) • ν)`.
It is meant to be used for `α ≤ 1`. -/
noncomputable def jensenShannon (α : ℝ≥0) (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  α * klDiv μ (α • μ + (1 - α) • ν) + (1 - α : ℝ≥0) * klDiv ν (α • μ + (1 - α) • ν)

/-- `JS_α(μ, ν) = JS_{1 - α}(ν, μ)`. -/
lemma jensenShannon_symm (hα : α ≤ 1) (μ ν : Measure 𝓧) :
    jensenShannon α μ ν = jensenShannon (1 - α) ν μ := by
  rw [jensenShannon, jensenShannon, tsub_tsub_cancel_of_le hα, add_comm (α • μ), add_comm]

@[simp]
lemma jensenShannon_zero (μ ν : Measure 𝓧) [SigmaFinite ν] : jensenShannon 0 μ ν = 0 := by
  simp [jensenShannon]

@[simp]
lemma jensenShannon_one (μ ν : Measure 𝓧) [SigmaFinite μ] : jensenShannon 1 μ ν = 0 := by
  simp [jensenShannon]

@[simp]
lemma jensenShannon_self (hα : α ≤ 1) (μ : Measure 𝓧) [SigmaFinite μ] :
    jensenShannon α μ μ = 0 := by
  rw [jensenShannon, ← add_smul, add_tsub_cancel_of_le hα, one_smul]
  simp

/-- For `0 < α < 1`, the Jensen-Shannon divergence between two finite measures vanishes if and only
if the two measures are equal. -/
lemma jensenShannon_eq_zero_iff (hα0 : α ≠ 0) (hα1 : α < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    jensenShannon α μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ jensenShannon_self hα1.le μ⟩
  have h1α : (1 - α : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hα1).ne'
  simp only [jensenShannon, add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero, hα0, h1α, false_or,
    klDiv_eq_zero_iff] at h
  exact h.1.trans h.2.symm

section FDiv

/-- The divergence function of the Jensen-Shannon divergence is the weighted sum of the
divergence functions of `KL(μ, α • μ + (1 - α) • ν)` and `KL(ν, α • μ + (1 - α) • ν)`, given by
`fDiv_smul_add_smul_right` and `fDiv_smul_add_smul_right_self`. -/
lemma jensenShannonDivFun_eq_add (hα : α ≤ 1) :
    jensenShannonDivFun α
      = α • (klDivFun.conj.compAffine (1 - α) α (tsub_add_cancel_of_le hα)).conj
        + (1 - α) • klDivFun.conj.compAffine α (1 - α) (add_tsub_cancel_of_le hα) := by
  have hab : α + (1 - α) = 1 := add_tsub_cancel_of_le hα
  -- away from `0` and `∞`, both sides are `ENNReal.ofReal` of the two sides of
  -- `jensenShannonFun_eq_add` at `r = x.toReal`
  refine DivFunction.eq_of_forall_ne_zero_ne_top fun x hx0 hx_top ↦ ?_
  rw [DivFunction.add_apply, DivFunction.smul_apply, DivFunction.smul_apply,
    DivFunction.conj_compAffine_conj_apply hab hx0 hx_top,
    DivFunction.conj_compAffine_apply hab hx0, jensenShannonDivFun_apply hα hx0 hx_top]
  set r := x.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos hx0 hx_top
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have h_sub : ((1 - α : ℝ≥0) : ℝ) = 1 - α := NNReal.coe_sub hα
  set m := (α : ℝ) * r + (1 - α) with hm_def
  have hm : 0 < m := mul_add_one_sub_pos α.coe_nonneg hα1 hr
  have h_mix : (α * x + (1 - α : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal m := by
    rw [hm_def, ENNReal.ofReal_add (mul_nonneg α.coe_nonneg hr.le) (sub_nonneg.mpr hα1),
      ENNReal.ofReal_mul α.coe_nonneg, ENNReal.ofReal_toReal hx_top, ← h_sub,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have h_div : x / (α * x + (1 - α : ℝ≥0)) = ENNReal.ofReal (r / m) := by
    rw [h_mix, ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_toReal hx_top]
  have h_inv : (α * x + (1 - α : ℝ≥0) : ℝ≥0∞)⁻¹ = ENNReal.ofReal m⁻¹ := by
    rw [h_mix, ENNReal.ofReal_inv_of_pos hm]
  have h_kl : ∀ t : ℝ, 0 ≤ t → klDivFun (ENNReal.ofReal t) = ENNReal.ofReal (klFun t) := by
    intro t ht
    rw [klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ht, klFun_apply]
  have h1 : 0 ≤ klFun (r / m) := klFun_nonneg (div_nonneg hr.le hm.le)
  have h2 : 0 ≤ klFun m⁻¹ := klFun_nonneg (inv_nonneg.mpr hm.le)
  rw [h_div, h_inv, h_mix, h_kl _ (div_nonneg hr.le hm.le), h_kl _ (inv_nonneg.mpr hm.le),
    ← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul α.coe_nonneg, ← ENNReal.ofReal_coe_nnreal (p := 1 - α), h_sub,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hα1),
    ← ENNReal.ofReal_add (mul_nonneg α.coe_nonneg (mul_nonneg hm.le h1))
      (mul_nonneg (sub_nonneg.mpr hα1) (mul_nonneg hm.le h2)),
    jensenShannonFun_eq_add α.coe_nonneg hα1 hr]

/-- The Jensen-Shannon divergence is an f-divergence, for the function
`x ↦ α * x * log x - (α * x + 1 - α) * log (α * x + 1 - α)`. -/
theorem jensenShannon_eq_fDiv (hα : α ≤ 1) (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    jensenShannon α μ ν = fDiv (jensenShannonDivFun α) μ ν := by
  have hab : α + (1 - α) = 1 := add_tsub_cancel_of_le hα
  rw [jensenShannon, klDiv_eq_fDiv, klDiv_eq_fDiv, fDiv_smul_add_smul_right hab,
    fDiv_smul_add_smul_right_self hab, jensenShannonDivFun_eq_add hα, fDiv_add, fDiv_smul,
    fDiv_smul]

end FDiv

section DataProcessing

/-- **Data processing inequality** for the Jensen-Shannon divergence and a Markov kernel. -/
theorem jensenShannon_comp_right_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    jensenShannon α (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ jensenShannon α μ ν := by
  have h_mix : α • (κ ∘ₘ μ) + (1 - α) • (κ ∘ₘ ν) = κ ∘ₘ (α • μ + (1 - α) • ν) := by
    simp_rw [Measure.comp_add, ← Measure.coe_nnreal_smul, Measure.comp_smul]
  rw [jensenShannon, jensenShannon, h_mix]
  gcongr <;> exact klDiv_comp_right_le _ _ κ

/-- **Data processing inequality** for the Jensen-Shannon divergence and a measurable map. -/
theorem jensenShannon_map_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : 𝓧 → 𝓨} (hg : Measurable g) :
    jensenShannon α (μ.map g) (ν.map g) ≤ jensenShannon α μ ν := by
  have h_mix : α • μ.map g + (1 - α) • ν.map g = (α • μ + (1 - α) • ν).map g := by
    rw [Measure.map_add _ _ hg, Measure.map_smul _ hg.aemeasurable,
      Measure.map_smul _ hg.aemeasurable]
  rw [jensenShannon, jensenShannon, h_mix]
  gcongr <;> exact klDiv_map_le _ _ hg

end DataProcessing

end ProbabilityTheory
