/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Limits at infinity of functions monotone on a final segment

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Filter Set Topology

/-- A function to a complete linear order which is monotone on `[x, ∞)` has a limit at `atTop`. -/
lemma MonotoneOn.exists_tendsto_atTop {ι α : Type*} [SemilatticeSup ι] [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {x : ι} {f : ι → α} (hf : MonotoneOn f (Ici x)) :
    ∃ y, Tendsto f atTop (𝓝 y) :=
  ⟨_, (tendsto_atTop_iSup fun _ _ hyz ↦ hf le_sup_left le_sup_left (sup_le_sup_left hyz x)).congr'
    ((eventually_ge_atTop x).mono fun _ hz ↦ by simp [sup_of_le_right hz])⟩
