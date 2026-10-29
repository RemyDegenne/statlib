/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Complements on finite products of measures

## Main statements

* `MeasureTheory.Measure.pi.instNeZero`: a finite product of nonzero σ-finite measures is nonzero.
* `MeasureTheory.Measure.pi_map_comp_of_injective`: the image of a product of probability measures
  `Measure.pi μ` by the restriction of the coordinates along an injective map `f` is
  `Measure.pi (fun i ↦ μ (f i))`.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

instance pi.instNeZero {ι : Type*} [Fintype ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] [∀ i, NeZero (μ i)] :
    NeZero (Measure.pi μ) :=
  ⟨fun h ↦ by simpa [pi_univ, Finset.prod_eq_zero_iff, NeZero.ne] using congr($h .univ)⟩

/-- The image of a product of probability measures by the restriction of the coordinates along an
injective map `f` is the product of the measures indexed by `f`. -/
lemma pi_map_comp_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] {X : κ → Type*}
    {mX : ∀ k, MeasurableSpace (X k)} (μ : (k : κ) → Measure (X k))
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → κ} (hf : f.Injective) :
    (Measure.pi μ).map (fun x i ↦ x (f i)) = Measure.pi fun i ↦ μ (f i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  -- the preimage of the box `univ.pi s` is the box with side `s i` at `f i` and `univ` elsewhere
  let t (k : κ) : Set (X k) := {y | ∀ i (h : f i = k), cast (congrArg X h.symm) y ∈ s i}
  have ht (i : ι) : t (f i) = s i := by
    ext y
    refine ⟨fun hy ↦ hy i rfl, fun hy j hj ↦ ?_⟩
    obtain rfl := hf hj
    exact hy
  have h_pre : (fun x i ↦ x (f i)) ⁻¹' univ.pi s = univ.pi t := by
    ext x
    simp only [mem_preimage, mem_univ_pi]
    refine ⟨fun hx k i hik ↦ ?_, fun hx i ↦ ht i ▸ hx (f i)⟩
    subst hik
    exact hx i
  rw [h_pre, Measure.pi_pi]
  refine (Fintype.prod_of_injective f hf _ _ (fun k hk ↦ ?_) fun i ↦ by rw [ht]).symm
  rw [show t k = univ from eq_univ_of_forall fun y i hik ↦ absurd ⟨i, hik⟩ hk, measure_univ]

end MeasureTheory.Measure
