/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Statlib.EValues.EVarClass
public import Statlib.EValues.Utility.Log
public import Statlib.ForMathlib.Jensen

/-!
# Numeraire

-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure 𝓧}
  {S : Set (Measure 𝓧)} {𝓔 : Set (𝓧 → ℝ≥0∞)} {U : Utility} {X Y : 𝓧 → ℝ≥0∞}

lemma measure_fsupport_eq_zero_of_ae_eq_top {μ : Measure 𝓧} {X : 𝓧 → ℝ≥0∞}
    (hX_top : ∀ᵐ ω ∂μ, X ω = ∞) :
    μ X.fsupport = 0 := by
  suffices μ {x | ¬ x ∈ X.fsupportᶜ} = 0 by simpa
  rw [← ae_iff]
  filter_upwards [hX_top] with x hx
  simp [hx]

/-- The integral of `Y / Y` equals the measure of the finite support of `Y`. -/
lemma lintegral_div_self_eq_measure_fsupport {Y : 𝓧 → ℝ≥0∞} (hY : Measurable Y) {P : Measure 𝓧} :
    ∫⁻ ω, Y ω / Y ω ∂P = P Y.fsupport := by
  have m_fsupport : MeasurableSet Y.fsupport := hY.measurable_fsupport
  rw [← lintegral_add_compl _ m_fsupport, ← add_zero <| P Y.fsupport]
  congr
  · suffices ∀ x ∈ Y.fsupport, Y x / Y x = 1 by
      rw [setLIntegral_congr_fun m_fsupport this]
      simp
    intro x hx
    exact (ENNReal.div_eq_one_iff hx.2 hx.1).mpr rfl
  · refine (setLIntegral_eq_zero_iff m_fsupport.compl (by fun_prop)).mpr ?_
    filter_upwards with x hx
    rw [Function.fsupport_compl] at hx
    rcases hx with hx_top | hx_zero
    · simp_all
    · simp_all

structure IsAbstractNumeraireFor (U : Utility) (X : 𝓧 → ℝ≥0∞) (𝓔 : Set (𝓧 → ℝ≥0∞)) (P : Measure 𝓧) :
    Prop where
  mem : X ∈ 𝓔
  eintegral_deriv_mul_ne_bot : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊥
  eintegral_deriv_mul_le : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≤ 0

lemma eintegral_deriv_mul_ne_bot_of_zero (h_zero : ∫ᵉ ω, -U.deriv (X ω) * X ω ∂P ≠ ⊥)
    (Y : 𝓧 → ℝ≥0∞) :
    ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊥ := by
  rw [← bot_lt_iff_ne_bot] at h_zero ⊢
  refine h_zero.trans_le ?_
  refine eintegral_mono fun ω ↦ ?_
  rw [neg_mul_comm]
  gcongr
  · exact Utility.deriv_nonneg U (X ω)
  rw [← zero_add (-(X ω : EReal)), ← sub_eq_add_neg]
  exact EReal.sub_le_sub (by positivity) le_rfl

namespace IsAbstractNumeraireFor

lemma congr (hX : IsAbstractNumeraireFor U X 𝓔 P) (hY_mem : Y ∈ 𝓔) (hYX : Y =ᵐ[P] X) :
    IsAbstractNumeraireFor U Y 𝓔 P where
  mem := hY_mem
  eintegral_deriv_mul_ne_bot Z hZ := by
    convert hX.eintegral_deriv_mul_ne_bot hZ using 1
    refine eintegral_congr_ae ?_
    filter_upwards [hYX] with ω hω using by rw [hω]
  eintegral_deriv_mul_le Z hZ := by
    refine le_trans (le_of_eq ?_) (hX.eintegral_deriv_mul_le hZ)
    refine eintegral_congr_ae ?_
    filter_upwards [hYX] with ω hω using by rw [hω]

lemma isAbstractNumeraireFor_one_iff_isEVar (h𝓔 : IsEVarClass 𝓔) :
    IsAbstractNumeraireFor U (1 : 𝓧 → ℝ≥0∞) 𝓔 P ↔
      U.deriv 1 = 0 ∨ ∀ Y ∈ 𝓔, IsEVar Y {P} := by
  have h_nonneg : 0 ≤ U.deriv 1 := Utility.deriv_nonneg U 1
  have h_ne_bot : U.deriv 1 ≠ ⊥ := EReal.ne_bot_of_nonneg h_nonneg
  have h_ne_top : U.deriv 1 ≠ ⊤ := by simp [Utility.deriv]
  have h_int_iff (Y : 𝓧 → ℝ≥0∞) (hY : Y ∈ 𝓔) (hU : U.deriv 1 ≠ 0) :
      EIntegrable (fun ω ↦ (Y ω : EReal) - 1) P ↔
        EIntegrable (fun ω ↦ U.deriv 1 * ((Y ω : EReal) - 1)) P := by
    refine ⟨fun h ↦ h.const_mul h_ne_bot h_ne_top, fun h ↦ ?_⟩
    have h_eq : (fun ω ↦ (Y ω : EReal) - 1) =
        fun ω ↦ (U.deriv 1)⁻¹ * (U.deriv 1 * ((Y ω : EReal) - 1)) := by
      ext ω
      rw [← mul_assoc]
      suffices (U.deriv 1)⁻¹ * U.deriv 1 = 1 by simp [this]
      lift U.deriv 1 to ℝ using ⟨h_ne_top, h_ne_bot⟩ with x
      rw [← EReal.coe_inv]
      norm_cast
      rw [inv_mul_cancel₀]
      simpa using hU
    rw [h_eq]
    refine h.const_mul ?_ EReal.inv_ne_top
    lift U.deriv 1 to ℝ using ⟨h_ne_top, h_ne_bot⟩ with x
    simp [← EReal.coe_inv]
  refine ⟨fun h_one ↦ ?_, fun h_le ↦ ?_⟩
  · by_cases h_zero : U.deriv 1 = 0
    · exact Or.inl h_zero
    refine Or.inr fun Y hY ↦ ?_
    have h_bot := h_one.eintegral_deriv_mul_ne_bot hY
    have h_le := h_one.eintegral_deriv_mul_le hY
    have h_int_mul : EIntegrable (fun ω ↦ U.deriv 1 * ((Y ω : EReal) - 1)) P :=
      eintegrable_of_eintegral_ne_bot h_bot
    have h_int : EIntegrable (fun ω ↦ (Y ω : EReal) - 1) P := by rwa [h_int_iff _ hY h_zero]
    simp only [Pi.one_apply, EReal.coe_ennreal_one] at h_le h_bot
    rw [eintegral_const_mul h_ne_bot h_ne_top h_int] at h_le h_bot
    rw [EReal.mul_nonpos_iff] at h_le
    refine ⟨h𝓔.measurable hY, ?_, ?_⟩
    · simp only [mem_singleton_iff, ne_eq, forall_eq]
      simpa [EReal.mul_ne_bot, h_ne_bot, h_ne_top, h_nonneg,
        not_le.mpr (lt_of_le_of_ne' h_nonneg h_zero)] using h_bot
    · simp only [mem_singleton_iff, forall_eq]
      simpa only [h_nonneg, true_and, not_le.mpr (lt_of_le_of_ne' h_nonneg h_zero), false_and,
        or_false] using h_le
  · refine ⟨h𝓔.one_mem, fun Y hY ↦ ?_, fun Y hY ↦ ?_⟩
    · by_cases h_zero : U.deriv 1 = 0
      · simp [h_zero]
      simp only [h_zero, false_or] at h_le
      specialize h_le Y hY
      have h := h_le.eintegral_ne_bot P (by simp)
      simp only [Pi.one_apply, EReal.coe_ennreal_one, ne_eq]
      rw [eintegral_const_mul h_ne_bot h_ne_top]
      swap; · exact h_le.eintegrable_sub_one P (by simp)
      simpa [EReal.mul_eq_bot, h_ne_bot, h_ne_top, lt_of_le_of_ne' h_nonneg h_zero,
        not_lt.mpr h_nonneg]
    · simp only [Pi.one_apply, EReal.coe_ennreal_one]
      by_cases h_zero : U.deriv 1 = 0
      · simp [h_zero]
      simp only [h_zero, false_or] at h_le
      specialize h_le Y hY
      rw [eintegral_const_mul h_ne_bot h_ne_top (h_le.eintegrable_sub_one P (by simp))]
      rw [EReal.mul_nonpos_iff]
      simp only [h_nonneg, true_and, not_le.mpr (lt_of_le_of_ne' h_nonneg h_zero), false_and,
        or_false]
      exact h_le.eintegral_nonpos P (by simp)

/-- A numeraire `X` maximizes the expected utility over the class `𝓔`. -/
lemma eintegral_utility_le (hX : IsAbstractNumeraireFor U X 𝓔 P) (hY_mem : Y ∈ 𝓔)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∫ᵉ ω, U (Y ω) ∂P ≤ ∫ᵉ ω, U (X ω) ∂P := by
  have h_foc := hX.eintegral_deriv_mul_le hY_mem
  have h_ne_bot : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊥ := hX.eintegral_deriv_mul_ne_bot hY_mem
  have h_ne_top : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) h_foc
  have h_meas : AEMeasurable (fun ω ↦ U.deriv (X ω) * ((Y ω : EReal) - X ω)) P := by fun_prop
  calc ∫ᵉ ω, U (Y ω) ∂P
  _ ≤ ∫ᵉ ω, U (X ω) + U.deriv (X ω) * (Y ω - X ω) ∂P := by
    refine eintegral_mono_ae ?_
    filter_upwards [ae_ne_bot_of_eintegral_ne_bot h_meas h_ne_bot,
      ae_ne_top_of_eintegral_ne_top h_meas (eintegrable_of_eintegral_ne_bot h_ne_bot) h_ne_top]
      with ω h_bot h_top
    exact U.le_add_deriv_mul' h_bot h_top
  _ = ∫ᵉ ω, U (X ω) ∂P + ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P :=
    eintegral_add' (by fun_prop) h_meas h_ne_top h_ne_bot
  _ ≤ ∫ᵉ ω, U (X ω) ∂P := by grw [h_foc]; simp

end IsAbstractNumeraireFor

structure IsAbstractNumeraire (X : 𝓧 → ℝ≥0∞) (𝓔 : Set (𝓧 → ℝ≥0∞)) (μ : Measure 𝓧) : Prop where
  mem : X ∈ 𝓔
  lintegral_div_le_measure_fsupport : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫⁻ ω, Y ω / X ω ∂μ ≤ μ X.fsupport

lemma lintegral_div_self_le_iff_IsAbstractNumeraire {P : Measure 𝓧} (h𝓔 : IsEVarClass 𝓔)
    {Y : 𝓧 → ℝ≥0∞} (hY_evar : Y ∈ 𝓔) :
    (∀ X, X ∈ 𝓔 → ∫⁻ ω, X ω / Y ω ∂P ≤ ∫⁻ ω, Y ω / Y ω ∂P) ↔ IsAbstractNumeraire Y 𝓔 P := by
  simp_rw [lintegral_div_self_eq_measure_fsupport (h𝓔.measurable hY_evar)]
  exact ⟨fun h ↦ ⟨hY_evar, h⟩, fun h ↦ h.lintegral_div_le_measure_fsupport⟩

/-- A random variable `X` is the numeraire for a set of measures `S` and a measure `μ`
if it is an e-variable for `S` and the expectation of the ratio of any e-variable `Y` over `X`
is at most the measure under `μ` of the finite support of `X`. -/
structure IsNumeraire (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) (μ : Measure 𝓧) : Prop
    extends IsEVar X S where
  lintegral_div_le_measure_fsupport : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂μ ≤ μ X.fsupport

/-- For a given e-variable `Y`, the property of being a numeraire is equivalent to the property
that the expectation of the ratio of any e-variable `X` over `Y` is less
than the expectation of the ratio of `Y` over itself. -/
lemma lintegral_div_self_le_iff_IsNumeraire {P : Measure 𝓧} {S : Set (Measure 𝓧)}
    {Y : 𝓧 → ℝ≥0∞} (hY_evar : IsEVar Y S) :
    (∀ X, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ ∫⁻ ω, Y ω / Y ω ∂P) ↔ IsNumeraire Y S P := by
  simp_rw [lintegral_div_self_eq_measure_fsupport hY_evar.measurable]
  exact ⟨fun h ↦ ⟨hY_evar, h⟩, fun h ↦ h.lintegral_div_le_measure_fsupport⟩

namespace IsNumeraire

variable {μ : Measure 𝓧}

protected lemma smul (hX : IsNumeraire X S μ) (c : ℝ≥0∞) :
    IsNumeraire X S (c • μ) where
  measurable := hX.measurable
  eintegral_ne_bot := hX.eintegral_ne_bot
  eintegral_nonpos := hX.eintegral_nonpos
  lintegral_div_le_measure_fsupport Y hY := by
    rw [lintegral_smul_measure, Measure.smul_apply]
    grw [hX.lintegral_div_le_measure_fsupport hY]

lemma lintegral_inv_le_measure_fsupport (hX : IsNumeraire X S μ) :
    ∫⁻ ω, (X ω)⁻¹ ∂μ ≤ μ X.fsupport := by
  simpa using hX.lintegral_div_le_measure_fsupport (isEVar_one S)

lemma lintegral_div_le_measure_univ (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ ≤ μ univ := by
  calc ∫⁻ ω, Y ω / X ω ∂μ
    _ ≤ μ X.fsupport := hX.lintegral_div_le_measure_fsupport hY
    _ ≤ μ univ := measure_mono (by simp)

lemma lintegral_div_le_one [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ ≤ 1 := by
  calc ∫⁻ ω, Y ω / X ω ∂μ
    _ ≤ μ univ := lintegral_div_le_measure_univ hX hY
    _ = 1 := by simp

lemma ae_pos [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) : ∀ᵐ ω ∂μ, 0 < X ω := by
  suffices ∀ᵐ ω ∂μ, (X ω)⁻¹ < ∞ by
    simp only [pos_iff_ne_zero]
    filter_upwards [this] with ω hω using by simpa using hω.ne
  refine ae_lt_top ?_ ?_
  · have := hX.measurable
    fun_prop
  · exact ne_top_of_le_ne_top (measure_ne_top _ _) hX.lintegral_inv_le_measure_fsupport

lemma ae_ne_zero [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  filter_upwards [hX.ae_pos] with ω hω using hω.ne'

/-- The constant function `1` is a numeraire for `S` at any `μ ∈ S`. -/
lemma _root_.ProbabilityTheory.isNumeraire_one {μ : Measure 𝓧} {S : Set (Measure 𝓧)} (hμS : μ ∈ S) :
    IsNumeraire (fun _ ↦ (1 : ℝ≥0∞)) S μ where
  toIsEVar := isEVar_fun_one S
  lintegral_div_le_measure_fsupport Y hY := by
    have h : (fun _ : 𝓧 ↦ (1 : ℝ≥0∞)).fsupport = Set.univ := by
      ext x
      simp [Function.fsupport]
    simp only [div_one, h]
    exact hY.lintegral_le_measure_univ μ hμS

/-- The numeraire property transports along a measurable equivalence. -/
lemma comp_measurableEquiv (e : 𝓧 ≃ᵐ 𝓨) {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)}
    {μ : Measure 𝓧} (hY : IsNumeraire Y (Measure.map e '' S) (μ.map e)) :
    IsNumeraire (Y ∘ e) S μ := by
  have hY_meas := hY.measurable
  have h_image : Measure.map e.symm '' (Measure.map e '' S) = S := by
    rw [← Set.image_comp]
    have h : (Measure.map e.symm ∘ Measure.map e) = id := by
      funext σ
      simp only [Function.comp_apply, id]
      rw [Measure.map_map e.symm.measurable e.measurable]
      simp
    rw [h, Set.image_id]
  refine ⟨hY.toIsEVar.comp e.measurable, fun Z hZ ↦ ?_⟩
  have hZ_meas := hZ.measurable
  have hZ' : IsEVar (Z ∘ e.symm) (Measure.map e '' S) :=
    IsEVar.comp e.symm.measurable (by rwa [show {ρ.map e.symm | ρ ∈ Measure.map e '' S}
      = Measure.map e.symm '' (Measure.map e '' S) from rfl, h_image])
  have h := hY.lintegral_div_le_measure_fsupport hZ'
  rw [lintegral_map (by fun_prop) e.measurable, e.map_apply] at h
  refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
  · refine lintegral_congr fun x ↦ ?_
    simp
  · rfl

lemma _root_.ProbabilityTheory.isNumeraire_of_isEmpty {f : 𝓧 → ℝ≥0∞}
    (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ, f x = ∞)
    (hS : IsEmpty S) : IsNumeraire f S μ where
  measurable := hf
  eintegral_ne_bot := by simp_all
  eintegral_nonpos := by simp_all
  lintegral_div_le_measure_fsupport := by
    by_contra! h
    obtain ⟨Y, hY, h⟩ := h
    have : μ f.fsupport = 0 := measure_fsupport_eq_zero_of_ae_eq_top hf_top
    rw [this] at h
    have : ∀ᵐ ω ∂μ, Y ω / f ω = 0 := by
      filter_upwards [hf_top] with ω hω
      simp_all
    rw [lintegral_congr_ae this, lintegral_zero] at h
    simp_all

set_option backward.isDefEq.respectTransparency false in
lemma lintegral_eq_setLIntegral_fsupport [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in X.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hX.measurable_fsupport]
  suffices ∫⁻ ω in X.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff]
  rotate_left
  · exact (hX.measurable_fsupport).compl
  · exact hY.measurable.div hX.measurable
  filter_upwards [hX.ae_ne_zero] with ω hω hω₂
  simp only [Function.fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, hω,
    not_false_eq_true, and_true, Decidable.not_not] at hω₂
  simp [hω₂]

/-- If an e-variable `Y` is ae-infinite at a point, then the numeraire `X` must also be
ae-infinite. -/
lemma ae_top_implies_numeraire_top [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∀ᵐ ω ∂μ, Y ω = ∞ → X ω = ∞ := by
  by_contra h
  simp only [ae_iff, Classical.not_imp] at h
  have m : MeasurableSet {ω | Y ω = ∞ ∧ X ω ≠ ∞} :=
    MeasurableSet.inter ((measurableSet_singleton ∞).preimage hY.measurable)
      ((measurableSet_singleton ∞).compl.preimage hX.measurable)
  have lintegral_div_le_measure_fsupport := hX.lintegral_div_le_measure_fsupport hY
  rw [← lintegral_add_compl _ m] at lintegral_div_le_measure_fsupport
  suffices ∀ ω ∈ {ω | Y ω = ∞ ∧ X ω ≠ ∞}, Y ω / X ω = ∞ by
    rw [setLIntegral_congr_fun m this] at lintegral_div_le_measure_fsupport
    simp [ENNReal.top_mul h] at lintegral_div_le_measure_fsupport
  intro ω hω
  simp [hω.1, ENNReal.top_div, hω.2]

lemma lintegral_eq_setLIntegral_fsupport' [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in Y.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hY.measurable_fsupport]
  suffices ∫⁻ ω in Y.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff]
  rotate_left
  · exact (hY.measurable_fsupport).compl
  · exact hY.measurable.div hX.measurable
  filter_upwards [hX.ae_top_implies_numeraire_top hY] with ω hω hω₂
  simp only [ENNReal.div_eq_zero_iff]
  by_cases hω_top : Y ω = ∞
  · simp [hω_top, hω hω_top]
  · simp only [Function.fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, not_and,
      Decidable.not_not] at hω₂
    simp [hω_top, hω₂]

lemma measure_fsupport_ne_zero_or_ae_top [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) :
    μ X.fsupport ≠ 0 ∨ X =ᵐ[μ] fun _ ↦ ∞ := by
  by_contra! h
  rcases h with ⟨h, h_top⟩
  rw [← compl_compl X.fsupport] at h
  have h' : ∀ᵐ x ∂μ, x ∈ X.fsupportᶜ := by rwa [ae_iff]
  refine h_top ?_
  filter_upwards [h', ae_ne_zero hX] with ω hω_mem hω_ne_zero
  simpa [hω_ne_zero] using hω_mem

/-- Two numeraires have equal finite support measures. -/
lemma measure_fsupport_eq_measure_fsupport [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsNumeraire Y S μ) : μ X.fsupport = μ Y.fsupport := by
  refine measure_congr ?_
  filter_upwards [hX.ae_ne_zero, hY.ae_top_implies_numeraire_top hX.toIsEVar,
      hY.ae_ne_zero, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hXω₀ hωXY hYω₀ hωYX
  rw [eq_iff_iff]
  constructor
  · rintro ⟨hXω_ne_top, _⟩
    refine ⟨?_, hYω₀⟩
    by_contra! h
    simp only [ne_eq, mem_ofPred_eq, Decidable.not_not] at h
    exact hXω_ne_top <| hωYX h
  · rintro ⟨hYω_ne_top, _⟩
    refine ⟨?_, hXω₀⟩
    by_contra! h
    simp only [ne_eq, mem_ofPred_eq, Decidable.not_not] at h
    exact hYω_ne_top <| hωXY h

lemma setLIntegral_fsupport_inv_le_measure [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsNumeraire Y S μ) : ∫⁻ ω in X.fsupport, (Y ω / X ω)⁻¹ ∂μ ≤ μ X.fsupport := by
  suffices ∫⁻ ω in X.fsupport, ((Y / X) ω)⁻¹ ∂μ ≤ μ X.fsupport from this
  rw [setLIntegral_congr_fun hX.measurable_fsupport <| ENNReal.inv_div_fsupport Y X,
    ← hY.lintegral_eq_setLIntegral_fsupport' hX.toIsEVar]
  rw [hX.measure_fsupport_eq_measure_fsupport hY]
  exact hY.lintegral_div_le_measure_fsupport hX.toIsEVar

lemma measure_fsupport_mul_inv_lintegral_div_eq_one [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsNumeraire Y S μ) (h : μ X.fsupport ≠ 0) :
    (μ X.fsupport) * (∫⁻ ω in X.fsupport, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  refine le_antisymm ?_ ?_
  · calc
    _ ≤ (μ X.fsupport)⁻¹ * ∫⁻ x in X.fsupport, (W x)⁻¹ ∂μ := by
      refine Inv.map_set_lintegral_le hX.measurable_fsupport ?_ h ?_ ?_
      · have := hX.measurable
        have := hY.measurable
        fun_prop
      · simp
      · filter_upwards [hX.ae_ne_zero, hX.ae_top_implies_numeraire_top hY.toIsEVar]
          with ω hXω₀ hXYω hω
        by_cases hY : Y ω = ⊤
        · simp_all
        · exact ENNReal.div_ne_top hY hXω₀
    _ ≤ (μ X.fsupport)⁻¹ * μ X.fsupport := by
      gcongr
      exact setLIntegral_fsupport_inv_le_measure hX hY
    _ = 1 := by
      refine ENNReal.inv_mul_cancel h ?_
      simp
  · rw [← inv_inv (μ X.fsupport), ← ENNReal.mul_inv]
    rotate_left
    · left
      simp
    · left
      simp [h]
    · simp only [ENNReal.le_inv_iff_mul_le, one_mul]
      calc
      _ ≤ (μ X.fsupport)⁻¹ * μ X.fsupport := by
        rw [← hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar]
        gcongr
        exact hX.lintegral_div_le_measure_fsupport hY.toIsEVar
      _ = 1 := by
        refine ENNReal.inv_mul_cancel h (by simp)

lemma inv_measure_fsupport_mul_lintegral_div_eq_one [IsFiniteMeasure μ] (hX : IsNumeraire X S μ)
    (hY : IsNumeraire Y S μ) (h : μ X.fsupport ≠ 0) :
    (μ X.fsupport)⁻¹ * ∫⁻ ω in X.fsupport, Y ω / X ω ∂μ = 1 := by
  rw [← inv_inv (∫⁻ ω in X.fsupport, Y ω / X ω ∂μ), ← ENNReal.mul_inv,
    ← ENNReal.inv_eq_one, inv_inv]
  · exact hX.measure_fsupport_mul_inv_lintegral_div_eq_one hY h
  · exact .inl h
  · left
    simp

/-- **Uniqueness Theorem**: The numeraire is almost-everywhere unique under finite measures. -/
theorem ae_unique [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) :
    X =ᵐ[μ] Y := by
  rcases hY.measure_fsupport_ne_zero_or_ae_top with μ_fsupport | hYₜ
  swap
  · filter_upwards [hYₜ, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω hω₂
    simp_all
  let W := X / Y
  have h_str_cvx := Inv.ae_eq_const_or_map_set_lintegral_lt (f := W) (μ := μ)
      (hY.measurable_fsupport) ?_ μ_fsupport ?_ ?_
  rotate_left
  · have := hX.measurable
    have := hY.measurable
    fun_prop
  · simp
  · filter_upwards [hY.ae_ne_zero, hY.ae_top_implies_numeraire_top hX.toIsEVar]
      with ω hYω₀ hYXω hω
    by_cases hX : X ω = ⊤
    · simp_all
    · exact ENNReal.div_ne_top hX hYω₀
  simp only [Pi.div_apply, W] at h_str_cvx
  rw [hY.measure_fsupport_mul_inv_lintegral_div_eq_one hX μ_fsupport] at h_str_cvx
  rcases h_str_cvx with h_eq | h_lt
  · rw [hY.inv_measure_fsupport_mul_lintegral_div_eq_one hX μ_fsupport] at h_eq
    unfold Filter.EventuallyEq at h_eq ⊢
    rw [ae_restrict_iff] at h_eq
    · filter_upwards [h_eq, hX.ae_ne_zero, hY.ae_ne_zero,
        hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω_support hωY₀ hωX₀ hωXY
      by_cases hω : ω ∈ Y.fsupport
      · simp_all [ENNReal.eq_of_div_eq_one (hω_support hω)]
      · rw [Function.not_mem_fsupport_iff] at hω
        rcases hω with hω_top | hω_zero
        · simp_all
        · contradiction
    · simp only [Pi.div_apply, Function.const_apply]
      refine measurableSet_eq_fun ?_ measurable_const
      have := hX.measurable
      have := hY.measurable
      fun_prop
  · have : (μ Y.fsupport)⁻¹ * ∫⁻ x in Y.fsupport, (X x / Y x)⁻¹ ∂μ ≤ 1 := by
      rw [← ENNReal.inv_mul_cancel μ_fsupport (by simp)]
      gcongr
      exact hY.setLIntegral_fsupport_inv_le_measure hX
    have := h_lt.trans_le this
    simp_all

lemma congr (hX : IsNumeraire X S μ) (hY_evar : IsEVar Y S) (hY : Y =ᵐ[μ] X) :
    IsNumeraire Y S μ := by
  refine ⟨hY_evar, fun Z hZ_evar ↦ ?_⟩
  calc ∫⁻ ω, Z ω / Y ω ∂μ
    _ = ∫⁻ ω, Z ω / X ω ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hY] with ω hω
      rw [hω]
    _ ≤ μ X.fsupport := hX.lintegral_div_le_measure_fsupport hZ_evar
    _ = μ Y.fsupport := by
      refine measure_congr ?_
      filter_upwards [hY] with ω hω
      rw [eq_iff_iff]
      constructor
      · rintro ⟨(h_top : X ω ≠ ⊤), (h_zero : X ω ≠ 0)⟩
        rw [← hω] at h_top h_zero
        exact ⟨h_top, h_zero⟩
      · rintro ⟨(h_top : Y ω ≠ ⊤), (h_zero : Y ω ≠ 0)⟩
        rw [hω] at h_top h_zero
        exact ⟨h_top, h_zero⟩

section LogOptimal

-- todo: prove that log-optimal implies numeraire
/-- A Numeraire is log-optimal. -/
theorem eintegral_log_div_nonpos [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0 := by
  calc ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ
  _ ≤ ENNReal.log (∫⁻ ω, Y ω / X ω ∂μ) := by
    refine Utility.eintegral_le_map logUtility ?_
    exact hY.measurable.aemeasurable.div hX.measurable.aemeasurable
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_div_le_one hX hY

/-- A Numeraire is log-optimal. -/
theorem eintegral_log_div_nonpos' [IsFiniteMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  suffices ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ[|univ] ≤ 0 by
    -- todo lemma about eintegral_cond?
    rw [cond, eintegral_smul_measure (by simpa), Measure.restrict_univ, EReal.mul_nonpos_iff]
      at this
    cases this with
    | inl h => exact h.2
    | inr h =>
      norm_cast at h
      simp at h
  have : IsProbabilityMeasure μ[|univ] := cond_isProbabilityMeasure_of_finite (by simpa) (by simp)
  refine eintegral_log_div_nonpos ?_ hY (S := S)
  rw [cond, Measure.restrict_univ]
  exact hX.smul _

lemma eintegral_eq_setEIntegral_of_eq_zero {f : 𝓧 → EReal}
    {s : Set 𝓧} (hs : MeasurableSet s) (h_zero : ∀ᵐ ω ∂μ, ω ∈ sᶜ → f ω = 0) :
    ∫ᵉ ω, f ω ∂μ = ∫ᵉ ω in s, f ω ∂μ := by
  unfold eintegral
  simp_rw [← lintegral_indicator hs]
  congr 2 <;>
  · refine lintegral_congr_ae ?_
    filter_upwards [h_zero] with ω hω
    by_cases hωs : ω ∈ s
    · simp [hωs]
    · simp [hω hωs, hωs]

lemma eintegral_div_le_measure_univ [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, Y ω / X ω ∂μ ≤ μ univ := by
  rw [eintegral_eq_lintegral_of_nonneg (fun _ ↦ by positivity)]
  norm_cast
  refine le_trans (le_of_eq ?_) (hX.lintegral_div_le_measure_univ hY)
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_ne_zero] with ω hω
  rw [← EReal.coe_ennreal_div hω, EReal.toENNReal_coe]

lemma eintegral_div_le_one [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, Y ω / X ω ∂μ ≤ 1 := by
  simpa using eintegral_div_le_measure_univ hX hY

lemma setEIntegral_le_eintegral_of_nonneg {f : 𝓧 → EReal} (hf_nonneg : ∀ ω, 0 ≤ f ω) (s : Set 𝓧) :
    ∫ᵉ ω in s, f ω ∂μ ≤ ∫ᵉ ω, f ω ∂μ := by
  rw [eintegral_eq_lintegral_of_nonneg hf_nonneg, eintegral_eq_lintegral_of_nonneg]
  · norm_cast
    exact setLIntegral_le_lintegral s fun x ↦ (f x).toENNReal
  · exact hf_nonneg

lemma setEIntegral_le_eintegral_of_ae_nonneg {f : 𝓧 → EReal} (hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (s : Set 𝓧) :
    ∫ᵉ ω in s, f ω ∂μ ≤ ∫ᵉ ω, f ω ∂μ := by
  rw [eintegral_eq_lintegral_of_nonneg_ae hf_nonneg,
    eintegral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf_nonneg)]
  norm_cast
  exact setLIntegral_le_lintegral s fun x ↦ (f x).toENNReal

-- todo: it should really be ≤ 0 instead, but this weaker result will be useful to prove that a
-- numeraire is `eintegrable`
lemma eintegral_sub_div_le_measure_univ [IsFiniteMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ ≤ μ univ := by
  have h_eq : ∀ᵐ ω ∂μ, X ω ≠ ⊤ → ((Y ω : EReal) - X ω) / X ω = Y ω / X ω - 1 := by
    filter_upwards [hX.ae_ne_zero, ae_top_implies_numeraire_top hX hY] with ω hX0 h_imp_top hX_top
    have hY_top : Y ω ≠ ∞ := fun h_false ↦ hX_top <| h_imp_top h_false
    have hX_eq : (X ω : EReal) = (X ω).toReal := by rw [EReal.coe_ennreal_toReal hX_top]
    have hY_eq : (Y ω : EReal) = (Y ω).toReal := by rw [EReal.coe_ennreal_toReal hY_top]
    rw [hX_eq, hY_eq]
    norm_cast
    rw [← EReal.coe_div, ← EReal.coe_div]
    have hX_ne_zero : (X ω).toReal ≠ 0 := by simp [ENNReal.toReal_eq_zero_iff, hX0, hX_top]
    simp [sub_div, div_self hX_ne_zero]
  have h_int_restrict : ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ
      = ∫ᵉ ω in {ω | X ω ≠ ⊤}, (Y ω - X ω) / X ω ∂μ := by
    refine eintegral_eq_setEIntegral_of_eq_zero ?_ ?_
    · exact ((measurableSet_singleton _).preimage hX.measurable).compl
    · filter_upwards [] with ω hω_top
      simp only [ne_eq, mem_compl_iff, mem_ofPred_eq, Decidable.not_not] at hω_top
      simp [hω_top]
  have h_int_restrict' : ∫ᵉ ω, Y ω / X ω ∂μ = ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω ∂μ := by
    refine eintegral_eq_setEIntegral_of_eq_zero ?_ ?_
    · exact ((measurableSet_singleton _).preimage hX.measurable).compl
    · filter_upwards [] with ω hω_top
      simp only [ne_eq, mem_compl_iff, mem_ofPred_eq, Decidable.not_not] at hω_top
      simp [hω_top]
  rw [h_int_restrict]
  calc ∫ᵉ ω in {ω | X ω ≠ ⊤}, (Y ω - X ω) / X ω ∂μ
  _ = ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω - 1 ∂μ := by
    refine eintegral_congr_ae ?_
    rwa [ae_restrict_iff']
    exact ((measurableSet_singleton _).preimage hX.measurable).compl
  _ ≤ ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω ∂μ := by
    gcongr with ω
    rw [sub_eq_add_neg]
    conv_rhs => rw [← add_zero ((Y ω : EReal) / X ω)]
    gcongr
    simp
  _ ≤ ∫ᵉ ω, Y ω / X ω ∂μ := by
    refine setEIntegral_le_eintegral_of_nonneg (fun _ ↦ ?_) _
    positivity
  _ ≤ μ univ := hX.eintegral_div_le_measure_univ hY

-- todo: it should really be ≤ 0 instead, but this weaker result will be useful to prove that a
-- numeraire is `eintegrable`
lemma eintegral_sub_div_le_one [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ ≤ 1 := by
  simpa using eintegral_sub_div_le_measure_univ hX hY

theorem eintegral_log_ge_neg_measure_univ [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) :
    - μ univ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  have hX_meas := hX.measurable
  have hY : IsEVar (fun _ ↦ 1) S := isEVar_one S
  suffices 0 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ + μ univ by
    conv_lhs => rw [← zero_add (- (μ univ : EReal)), ← sub_eq_add_neg]
    rwa [EReal.sub_le_iff_le_add]
    · left; simp
    · left; simp
  calc 0
  _ = ∫ᵉ ω, ENNReal.log 1 ∂μ := by simp
  _ ≤ ∫ᵉ ω, ENNReal.log (X ω) + (1 - X ω) * (if X ω = 0 then ⊤ else 1 / X ω) ∂μ := by
    refine eintegral_mono_ae ?_
    filter_upwards [hX.ae_ne_zero] with ω hω
    by_cases hX_top : X ω = ∞
    · simp [hX_top]
    simp only [ENNReal.log_one, hω, ↓reduceIte, one_div]
    have : X ω = ENNReal.ofReal (X ω).toReal := by rw [ENNReal.ofReal_toReal hX_top]
    have h_pos : 0 < (X ω).toReal := ENNReal.toReal_pos hω hX_top
    rw [this, ENNReal.log_ofReal, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_inv,
      EReal.coe_ennreal_ofReal, ← EReal.coe_inv]
    swap; · rwa [ENNReal.ofReal_toReal hX_top]
    simp only [not_le.mpr h_pos, ↓reduceIte, ENNReal.toReal_nonneg, sup_of_le_left, ge_iff_le]
    norm_cast
    have h := Real.one_sub_inv_le_log_of_pos h_pos
    field_simp at h ⊢
    linarith
  _ = ∫ᵉ ω, ENNReal.log (X ω) + (1 - X ω) / X ω ∂μ := by
    refine eintegral_congr_ae ?_
    filter_upwards [hX.ae_ne_zero] with ω hω
    congr
    simp only [hω, ↓reduceIte, one_div]
    rw [← EReal.inv_coe_ennreal hω]
    rfl
  _ = ∫ᵉ ω, ENNReal.log (X ω) ∂μ + ∫ᵉ ω, (1 - X ω) / X ω ∂μ := by
    rw [eintegral_add']
    · fun_prop
    · fun_prop
    · refine ne_top_of_le_ne_top (by simp : (μ univ : EReal) ≠ ⊤) ?_
      calc ∫ᵉ ω, (1 - X ω) / X ω ∂μ
      _ ≤ ∫ᵉ ω, 1 / X ω ∂μ := by
        refine eintegral_mono fun ω ↦ ?_
        gcongr
        rw [sub_eq_add_neg]
        conv_rhs => rw [← add_zero 1]
        gcongr
        simp only [EReal.neg_le_zero]
        positivity
      _ = ∫⁻ ω, 1 / X ω ∂μ := by
        rw [eintegral_eq_lintegral_of_nonneg]
        · congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [hX.ae_ne_zero] with ω hω
          rw [div_eq_mul_inv, EReal.toENNReal_mul, EReal.toENNReal_one, EReal.toENNReal_inv,
            EReal.toENNReal_coe, div_eq_mul_inv]
          · positivity
          · positivity
        · intro x
          positivity
      _ ≤ μ univ := mod_cast hX.lintegral_div_le_measure_univ hY
    · refine ne_bot_of_le_ne_bot (by simp : (- (μ univ : EReal)) ≠ ⊥) ?_
      calc - (μ univ : EReal)
      _ = ∫ᵉ ω, - 1 ∂μ := by simp
      _ ≤ ∫ᵉ ω, - X ω / X ω ∂μ := by
        gcongr with ω
        by_cases hX0 : X ω = 0
        · simp [hX0]
        by_cases hX_top : X ω = ∞
        · simp [hX_top]
        rw [EReal.neg_div, EReal.div_self (by simp) (by simp [hX_top]) (by simp [hX0])]
      _ ≤ ∫ᵉ ω, (1 - X ω) / X ω ∂μ := by
        gcongr with ω
        rw [sub_eq_add_neg]
        conv_lhs => rw [← zero_add (- (X ω : EReal))]
        gcongr
        simp
  _ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ + μ univ := by
    gcongr
    convert hX.eintegral_sub_div_le_measure_univ hY
    rfl

theorem eintegral_log_ge_neg_one [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) :
    -1 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  simpa using eintegral_log_ge_neg_measure_univ hX

lemma eintegral_log_ne_bot [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) :
    ∫ᵉ ω, ENNReal.log (X ω) ∂μ ≠ ⊥ := by
  have h_le := eintegral_log_ge_neg_measure_univ hX
  by_contra h
  simp only [h, le_bot_iff, EReal.neg_eq_bot_iff] at h_le
  simp at h_le

/-- The logarithm of the numeraire is integrable. -/
protected lemma eintegrable_log [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) :
    EIntegrable (fun ω ↦ ENNReal.log (X ω)) μ := by
  by_contra h_false
  refine hX.eintegral_log_ne_bot ?_
  exact eintegral_of_not_eintegrable h_false

/-- A Numeraire maximizes the integral of the logarithm. -/
theorem eintegral_log_le [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂μ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  by_cases hY_bot : ∫ᵉ ω, ENNReal.log (Y ω) ∂μ = ⊥
  · simp [hY_bot]
  by_cases hX_top : ∫ᵉ ω, ENNReal.log (X ω) ∂μ = ⊤
  · simp [hX_top]
  have h_nonpos := eintegral_log_div_nonpos' hX hY
  simp_rw [ENNReal.log_div] at h_nonpos
  rwa [eintegral_sub (by have := hY.measurable; fun_prop) (by have := hX.measurable; fun_prop)
    hX.eintegrable_log, EReal.sub_nonpos] at h_nonpos
  · simp [hX_top]
  · simp [hY_bot]

lemma eintegral_log_nonneg [IsFiniteMeasure μ] (hX : IsNumeraire X S μ) :
    0 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  simpa using eintegral_log_le hX (isEVar_one S)

end LogOptimal

end IsNumeraire

end ProbabilityTheory
