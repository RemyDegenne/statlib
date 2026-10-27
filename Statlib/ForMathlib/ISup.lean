/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Order.CompleteLattice.Basic

/-! # Indexed suprema as suprema of sets

A supremum over the elements satisfying a predicate, written as `sSup` of a set.
-/

@[expose] public section

lemma iSup₂_eq_sSup {α ι : Type*} [CompleteLattice ι] {P : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P x), g x = sSup {y | ∃ x, P x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_ofPred_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

lemma iSup₃_eq_sSup {α ι : Type*} [CompleteLattice ι] {P₁ P₂ : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P₁ x) (_ : P₂ x), g x = sSup {y | ∃ x, P₁ x ∧ P₂ x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_ofPred_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
