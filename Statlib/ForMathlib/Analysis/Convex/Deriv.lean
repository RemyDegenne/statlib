/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Deriv

/-!
# Comparison of functions from a comparison of their second derivatives

## Main statements

* `le_mul_of_deriv2_le`: let `φ, ψ : ℝ → ℝ` be twice differentiable on a convex set `D` and let
  `x₀` be an interior point of `D` with `φ x₀ = c * ψ x₀` and `φ' x₀ = c * ψ' x₀`.
  If `φ'' ≤ c * ψ''` on `D`, then `φ ≤ c * ψ` on `D`.
-/

@[expose] public section

open Set

/-- Let `φ, ψ : ℝ → ℝ` be twice differentiable on a convex set `D` and let `x₀` be an interior
point of `D` with `φ x₀ = c * ψ x₀` and `φ' x₀ = c * ψ' x₀`. If `φ'' ≤ c * ψ''` on `D`, then
`φ ≤ c * ψ` on `D`.

The function `c * ψ - φ` is convex on `D` since its second derivative is nonnegative, and its
derivative vanishes at `x₀`: it attains its minimum `0` at `x₀`. -/
lemma le_mul_of_deriv2_le {φ ψ φ' ψ' φ'' ψ'' : ℝ → ℝ} {c : ℝ} {D : Set ℝ} {x₀ : ℝ}
    (hD : Convex ℝ D) (hx₀ : x₀ ∈ interior D)
    (hφ : ∀ x ∈ D, HasDerivAt φ (φ' x) x) (hφ' : ∀ x ∈ D, HasDerivAt φ' (φ'' x) x)
    (hψ : ∀ x ∈ D, HasDerivAt ψ (ψ' x) x) (hψ' : ∀ x ∈ D, HasDerivAt ψ' (ψ'' x) x)
    (h_eq : φ x₀ = c * ψ x₀) (h_deriv_eq : φ' x₀ = c * ψ' x₀)
    (h : ∀ x ∈ D, φ'' x ≤ c * ψ'' x) {x : ℝ} (hx : x ∈ D) :
    φ x ≤ c * ψ x := by
  have hu (y : ℝ) (hy : y ∈ D) : HasDerivAt (fun y ↦ c * ψ y - φ y) (c * ψ' y - φ' y) y :=
    ((hψ y hy).const_mul c).sub (hφ y hy)
  have hu' (y : ℝ) (hy : y ∈ D) :
      HasDerivAt (fun y ↦ c * ψ' y - φ' y) (c * ψ'' y - φ'' y) y :=
    ((hψ' y hy).const_mul c).sub (hφ' y hy)
  have h_cvx : ConvexOn ℝ D (fun y ↦ c * ψ y - φ y) :=
    convexOn_of_hasDerivWithinAt2_nonneg (f' := fun y ↦ c * ψ' y - φ' y)
      (f'' := fun y ↦ c * ψ'' y - φ'' y) hD
      (fun y hy ↦ (hu y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hu y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy ↦ (hu' y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy ↦ sub_nonneg.mpr (h y (interior_subset hy)))
  have h_min : IsMinOn (fun y ↦ c * ψ y - φ y) D x₀ := by
    refine h_cvx.isMinOn_of_rightDeriv_eq_zero hx₀ ?_
    rw [(hu x₀ (interior_subset hx₀)).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x₀),
      h_deriv_eq, sub_self]
  have := isMinOn_iff.mp h_min x hx
  simp only [h_eq, sub_self] at this
  linarith
