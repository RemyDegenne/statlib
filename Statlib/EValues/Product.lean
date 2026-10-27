/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Statlib.EValues.NumeraireExistence

/-!
# Numeraire of a product

The product of e-variables for two sets of measures `S` and `T` is an e-variable for the set of
product measures `Set.image2 Measure.prod S T`, and the product of the numeraires is the numeraire
for the product measure. As a consequence, the maximal logarithmic utility is additive on products
of probability measures.

## Main statements

* `IsEVar.prod`: the product of two e-variables is an e-variable for the product measures.
* `IsNumeraire.prod`: the product of two numeraires is a numeraire for the product measure.
* `eintegral_log_numeraire_prod`: the expected logarithm of the numeraire of a product.
* `maxUtility_prod`: the maximal logarithmic utility of a product is a weighted sum of the maximal
  logarithmic utilities, and `maxUtility_prod_eq_add` is the case of probability measures.
* `isNumeraire_pi_numeraire`: the product of the numeraires is the numeraire for a finite product
  of finite measures.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} {Q : Measure 𝓨} {S : Set (Measure 𝓧)} {T : Set (Measure 𝓨)}

/-- The product of two e-variables is an e-variable for the product measures. -/
lemma IsEVar.prod {X : 𝓧 → ℝ≥0∞} {Y : 𝓨 → ℝ≥0∞} (hX : IsEVar X S) (hY : IsEVar Y T)
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    IsEVar (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2) (Set.image2 Measure.prod S T) := by
  have hX_meas := hX.measurable
  have hY_meas := hY.measurable
  refine .of_lintegral_le_measure_univ ?_ (by fun_prop) ?_
  · rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    have := hS μ hμS
    have := hT ν hνT
    infer_instance
  · rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    have := hT ν hνT
    rw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    grw [hX.lintegral_le_measure_univ μ hμS, hY.lintegral_le_measure_univ ν hνT]
    rw [Measure.prod_apply .univ, mul_comm]
    simp

/-- The product of two numeraires is a numeraire for the product measure, with respect to the set
of product measures. -/
theorem IsNumeraire.prod [IsFiniteMeasure P] [IsFiniteMeasure Q] {X : 𝓧 → ℝ≥0∞}
    {Y : 𝓨 → ℝ≥0∞} (hX : IsNumeraire X S P) (hY : IsNumeraire Y T Q)
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2) (Set.image2 Measure.prod S T) (P.prod Q) := by
  have hX_meas := hX.measurable
  have hY_meas := hY.measurable
  refine isNumeraire_of_lintegral_div_le (hX.isEVar.prod hY.isEVar hS hT) (measure_ne_top _ _)
    fun Z hZ_evar ↦ ?_
  have hZ_meas := hZ_evar.measurable
  rw [Function.fsupport_mul_prod, Measure.prod_prod, lintegral_prod _ (by fun_prop)]
  simp_rw [mul_comm (X _)]
  -- integrate first over `y`
  have h_eq : ∫⁻ x, ∫⁻ y, Z (x, y) / (Y y * X x) ∂Q ∂P
      = ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX.ae_ne_zero] with x hx
    simp_rw [div_eq_mul_inv]
    rw [← lintegral_mul_const _ (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [hY.ae_ne_zero] with y hy
    rw [ENNReal.mul_inv (.inl hy) (.inr hx), mul_assoc]
  rw [h_eq]
  -- if `Y` is almost everywhere infinite, both sides vanish
  by_cases hY_top : Y =ᵐ[Q] fun _ ↦ ∞
  · have hQY : Q Y.fsupport = 0 := measure_fsupport_eq_zero_of_ae_eq_top hY_top
    refine le_of_eq ?_
    calc ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P
    _ = ∫⁻ x, 0 / X x ∂P := by
      congr with x
      congr
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hY_top] with y hy
      simp [hy]
    _ = 0 := by simp
    _ = P X.fsupport * Q Y.fsupport := by simp [hQY]
  -- otherwise, `x ↦ (Q Y.fsupport)⁻¹ * ∫⁻ y, Z (x, y) / Y y ∂Q` is an e-variable for `S`, and we
  -- conclude with the numeraire property of `X`
  suffices IsEVar (fun x ↦ (Q Y.fsupport)⁻¹ * ∫⁻ y, Z (x, y) / Y y ∂Q) S by
    have h_le := hX.lintegral_div_le_measure_fsupport this
    simp_rw [mul_div_assoc] at h_le
    rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp), mul_comm] at h_le
    swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top
    exact h_le
  refine .of_lintegral_le_measure_univ hS (by fun_prop) ?_
  · intro μ hμS
    have := hS μ hμS
    by_cases hμ : μ = 0
    · simp [hμ]
    have h_top : μ .univ ≠ ∞ := measure_ne_top _ _
    -- this follows from the numeraire property of `Y`, applied to the e-variable
    -- `y ↦ (μ univ)⁻¹ * ∫⁻ x, Z (x, y) ∂μ` for `T`
    suffices IsEVar (fun y ↦ (μ .univ)⁻¹ * ∫⁻ x, Z (x, y) ∂μ) T by
      have hY' := hY.lintegral_div_le_measure_fsupport this
      rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp)]
      swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top
      simp_rw [mul_div_assoc] at hY'
      rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ h_top, mul_comm] at hY'
      swap; · simp [hμ]
      refine le_trans (le_of_eq ?_) hY'
      rw [lintegral_lintegral_swap (by fun_prop)]
      congr with y
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (by fun_prop)]
    refine .of_lintegral_le_measure_univ hT (by fun_prop) ?_
    intro ν hνT
    have := hT ν hνT
    rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ h_top]
    swap; · simp [hμ]
    rw [lintegral_lintegral_symm (by fun_prop), mul_comm]
    refine (hZ_evar.lintegral_le_measure_univ (μ.prod ν) ⟨μ, hμS, ν, hνT, rfl⟩).trans ?_
    rw [Measure.prod_apply .univ]
    simp

/-- The product of the numeraires is the numeraire for the product measure. -/
theorem isNumeraire_prod_numeraire (P : Measure 𝓧) [IsFiniteMeasure P] (Q : Measure 𝓨)
    [IsFiniteMeasure Q] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ numeraire P S x.1 * numeraire Q T x.2)
      (Set.image2 Measure.prod S T) (P.prod Q) :=
  (isNumeraire_numeraire P hS).prod (isNumeraire_numeraire Q hT) hS hT

/-- The expected logarithm of the numeraire of a product is a weighted sum of the expected
logarithms of the numeraires of the factors. -/
theorem eintegral_log_numeraire_prod [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    ∫ᵉ x, ENNReal.log (numeraire (P.prod Q) (Set.image2 Measure.prod S T) x) ∂(P.prod Q)
      = Q .univ * ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P +
        P .univ * ∫ᵉ x, ENNReal.log (numeraire Q T x) ∂Q := by
  have h_fst : ∫ᵉ p, ENNReal.log (numeraire P S p.1) ∂(P.prod Q)
      = Q .univ * ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P := by
    rw [← eintegral_map (f := fun x ↦ ENNReal.log (numeraire P S x)) (by fun_prop) measurable_fst,
      Measure.map_fst_prod, eintegral_smul_measure (by simp)]
  have h_snd : ∫ᵉ p, ENNReal.log (numeraire Q T p.2) ∂(P.prod Q)
      = P .univ * ∫ᵉ y, ENNReal.log (numeraire Q T y) ∂Q := by
    rw [← eintegral_map (f := fun y ↦ ENNReal.log (numeraire Q T y)) (by fun_prop) measurable_snd,
      Measure.map_snd_prod, eintegral_smul_measure (by simp)]
  have h_int_snd : EIntegrable (fun p ↦ ENNReal.log (numeraire Q T p.2)) (P.prod Q) := by
    refine (eintegrable_map (g := fun y ↦ ENNReal.log (numeraire Q T y))
      measurable_snd.aemeasurable (by fun_prop)).mp ?_
    rw [Measure.map_snd_prod]
    exact (eintegrable_log_numeraire hT).smul_measure (by simp)
  have h_nonneg_fst : 0 ≤ ∫ᵉ p, ENNReal.log (numeraire P S p.1) ∂(P.prod Q) := by
    have := (isNumeraire_numeraire P hS).eintegral_log_nonneg
    rw [h_fst]
    positivity
  have h_nonneg_snd : 0 ≤ ∫ᵉ p, ENNReal.log (numeraire Q T p.2) ∂(P.prod Q) := by
    have := (isNumeraire_numeraire Q hT).eintegral_log_nonneg
    rw [h_snd]
    positivity
  -- the numeraire of the product is the product of the numeraires
  have h_ae_eq : numeraire (P.prod Q) (Set.image2 Measure.prod S T)
      =ᵐ[P.prod Q] (fun x ↦ numeraire P S x.1 * numeraire Q T x.2) := by
    refine ((isNumeraire_prod_numeraire P Q hS hT).ae_eq_numeraire ?_).symm
    rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    have := hS μ hμS
    have := hT ν hνT
    infer_instance
  rw [eintegral_congr_ae (h_ae_eq.mono fun p hp ↦ by rw [hp])]
  simp_rw [ENNReal.log_mul_add]
  rw [eintegral_add (by fun_prop) (by fun_prop) h_int_snd
    (.inl (EReal.ne_bot_of_nonneg h_nonneg_fst)) (.inr (EReal.ne_bot_of_nonneg h_nonneg_snd)),
    h_fst, h_snd]

/-- The maximal logarithmic utility of a product is a weighted sum of the maximal logarithmic
utilities of the factors. -/
lemma maxUtility_prod (P : Measure 𝓧) (Q : Measure 𝓨) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    maxUtility (P.prod Q) (Set.image2 Measure.prod S T) logUtility =
      Q .univ * maxUtility P S logUtility + P .univ * maxUtility Q T logUtility := by
  rw [maxUtility_eq_eintegral_numeraire (P.prod Q), maxUtility_eq_eintegral_numeraire _ hS,
    maxUtility_eq_eintegral_numeraire _ hT]
  · exact eintegral_log_numeraire_prod hS hT
  · rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    have := hS μ hμS
    have := hT ν hνT
    infer_instance

/-- The maximal logarithmic utility of a product of probability measures is the sum of the maximal
logarithmic utilities of the factors. -/
lemma maxUtility_prod_eq_add (P : Measure 𝓧) (Q : Measure 𝓨) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hT : ∀ μ ∈ T, IsFiniteMeasure μ) :
    maxUtility (P.prod Q) (Set.image2 Measure.prod S T) logUtility =
      maxUtility P S logUtility + maxUtility Q T logUtility := by
  simpa using maxUtility_prod P Q hS hT

/-- The product of the numeraires is a numeraire for the product measure, for a family indexed
by `Fin n`. This is the induction that underlies `isNumeraire_pi_numeraire`. -/
private lemma isNumeraire_pi_numeraire_fin : ∀ (n : ℕ) {𝓧 : Fin n → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] (P : (i : Fin n) → Measure (𝓧 i))
    [∀ i, IsFiniteMeasure (P i)] (S : (i : Fin n) → Set (Measure (𝓧 i))),
    (∀ i, ∀ μ ∈ S i, IsFiniteMeasure μ) →
    IsNumeraire (fun x ↦ ∏ i, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ S)) (Measure.pi P) := by
  intro n
  induction n with
  | zero =>
    intro 𝓧 _ P _ S _
    have h1 : (fun x : ∀ i : Fin 0, 𝓧 i ↦ ∏ i, numeraire (P i) (S i) (x i)) = 1 := by
      ext x
      simp
    rw [h1]
    exact isNumeraire_one ⟨P, fun i _ ↦ i.elim0, rfl⟩
  | succ n ih =>
    intro 𝓧 _ P _ S hS
    -- split off the first coordinate
    set e := MeasurableEquiv.piFinSuccAbove 𝓧 0 with he
    set S' : (j : Fin n) → Set (Measure (𝓧 ((0 : Fin (n + 1)).succAbove j))) :=
      fun j ↦ S ((0 : Fin (n + 1)).succAbove j) with hS'
    set P' : (j : Fin n) → Measure (𝓧 ((0 : Fin (n + 1)).succAbove j)) :=
      fun j ↦ P ((0 : Fin (n + 1)).succAbove j) with hP'
    have hS0 : ∀ μ ∈ S 0, IsFiniteMeasure μ := hS 0
    have hT : ∀ ρ ∈ Measure.pi '' (Set.pi Set.univ S'), IsFiniteMeasure ρ := by
      rintro _ ⟨ν, hν, rfl⟩
      have : ∀ j, IsFiniteMeasure (ν j) := fun j ↦ hS _ _ (hν j (Set.mem_univ _))
      infer_instance
    have h_prod := (isNumeraire_numeraire (P 0) hS0).prod (ih P' S' fun j ↦ hS _) hS0 hT
    -- the images of the two sets of measures agree
    have h_map (ν : (i : Fin (n + 1)) → Measure (𝓧 i)) [∀ i, SigmaFinite (ν i)] :
        (Measure.pi ν).map e = (ν 0).prod (Measure.pi fun j ↦ ν ((0 : Fin (n + 1)).succAbove j)) :=
      (measurePreserving_piFinSuccAbove ν 0).map_eq
    have h_eq_set : Measure.map e '' (Measure.pi '' (Set.pi Set.univ S))
        = Set.image2 Measure.prod (S 0) (Measure.pi '' (Set.pi Set.univ S')) := by
      ext ρ
      simp only [Set.mem_image, Set.mem_image2]
      constructor
      · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
        have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS _ _ (hν i (Set.mem_univ _))
        exact ⟨ν 0, hν 0 (Set.mem_univ _), _,
          ⟨fun j ↦ ν ((0 : Fin (n + 1)).succAbove j), fun j _ ↦ hν _ (Set.mem_univ _), rfl⟩,
          (h_map ν).symm⟩
      · rintro ⟨μ, hμ, _, ⟨ν', hν', rfl⟩, rfl⟩
        set ν : (i : Fin (n + 1)) → Measure (𝓧 i) :=
          Fin.insertNth (α := fun i ↦ Measure (𝓧 i)) 0 μ ν' with hν_def
        have hν0 : ν 0 = μ := Fin.insertNth_apply_same _ _ _
        have hνs (j : Fin n) : ν ((0 : Fin (n + 1)).succAbove j) = ν' j :=
          Fin.insertNth_apply_succAbove _ _ _ _
        have hν_mem : ∀ i, ν i ∈ S i := by
          refine Fin.succAboveCases 0 ?_ ?_
          · rw [hν0]; exact hμ
          · intro j
            rw [hνs]
            exact hν' j (Set.mem_univ _)
        have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS i _ (hν_mem i)
        refine ⟨Measure.pi ν, ⟨ν, fun i _ ↦ hν_mem i, rfl⟩, ?_⟩
        rw [h_map ν, hν0]
        congr 1
    rw [← h_eq_set, ← h_map P] at h_prod
    have h := h_prod.comp_measurableEquiv e
    convert h using 1
    ext x
    rw [Fin.prod_univ_succAbove _ 0]
    rfl

/-- The product of the numeraires is the numeraire for a finite product of finite measures. -/
lemma isNumeraire_pi_numeraire {ι : Type*} {𝓧 : ι → Type*} [Fintype ι]
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i, IsFiniteMeasure (P i)]
    (hS : ∀ i, ∀ μ ∈ S i, IsFiniteMeasure μ) :
    IsNumeraire (fun x ↦ ∏ i, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ S)) (Measure.pi P) := by
  -- reindex the family by `Fin (card ι)`
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let e : ((i : ι) → 𝓧 i) ≃ᵐ ((j : Fin (Fintype.card ι)) → 𝓧 (f j)) :=
    (MeasurableEquiv.piCongrLeft 𝓧 f).symm
  have h_map (ν : (i : ι) → Measure (𝓧 i)) [∀ i, SigmaFinite (ν i)] :
      (Measure.pi ν).map e = Measure.pi fun j ↦ ν (f j) :=
    (MeasurePreserving.symm _ (measurePreserving_piCongrLeft ν f)).map_eq
  have h_fin := isNumeraire_pi_numeraire_fin _ (fun j ↦ P (f j)) (fun j ↦ S (f j))
    fun j ↦ hS (f j)
  have h_set : Measure.map e '' (Measure.pi '' (Set.pi Set.univ S))
      = Measure.pi '' (Set.pi Set.univ fun j ↦ S (f j)) := by
    ext ρ
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
      have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS _ _ (hν i (Set.mem_univ _))
      exact ⟨fun j ↦ ν (f j), fun j _ ↦ hν _ (Set.mem_univ _), (h_map ν).symm⟩
    · rintro ⟨ν', hν', rfl⟩
      set ν : (i : ι) → Measure (𝓧 i) :=
        Equiv.piCongrLeft (fun i ↦ Measure (𝓧 i)) f ν' with hν_def
      have hν_apply (j : Fin (Fintype.card ι)) : ν (f j) = ν' j :=
        Equiv.piCongrLeft_apply_apply (fun i ↦ Measure (𝓧 i)) f ν' j
      have hν_mem (i : ι) : ν i ∈ S i := by
        obtain ⟨j, rfl⟩ := f.surjective i
        rw [hν_apply]
        exact hν' j (Set.mem_univ _)
      have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS i _ (hν_mem i)
      refine ⟨Measure.pi ν, ⟨ν, fun i _ ↦ hν_mem i, rfl⟩, ?_⟩
      rw [h_map ν]
      congr 1
      funext j
      exact hν_apply j
  rw [← h_set, ← h_map P] at h_fin
  have h := h_fin.comp_measurableEquiv e
  convert h using 1
  ext x
  rw [← f.prod_comp fun i ↦ numeraire (P i) (S i) (x i)]
  rfl

/-- The product of the numeraires is the numeraire for the product of finite measures indexed by
a finset. -/
lemma isNumeraire_pi_numeraire_finset {ι : Type*} {𝓧 : ι → Type*} {s : Finset ι}
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i : s, IsFiniteMeasure (P i)]
    (hS : ∀ i ∈ s, ∀ μ ∈ S i, IsFiniteMeasure μ) :
    IsNumeraire (fun x ↦ ∏ i : s, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ fun i : s ↦ S i)) (Measure.pi fun i : s ↦ P i) :=
  isNumeraire_pi_numeraire fun i ↦ hS i i.2

end ProbabilityTheory
