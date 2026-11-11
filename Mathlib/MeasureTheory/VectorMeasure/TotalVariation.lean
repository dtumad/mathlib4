/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance of vector measures

We define the total variation distance between two vector measures `μ, ν` as
`(μ - ν).variation Set.univ`.

## Main definitions

* `VectorMeasure.etvDist μ ν`: total variation distance between two vector measures,
  defined as the value on the universal set of the variation of `μ - ν`.

## Main statements

* `etvDist_self`, `etvDist_eq_zero_iff`, `etvDist_comm`, `etvDist_triangle`: the total
  variation distance between vector measures is a distance.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace VectorMeasure

variable {𝓧 𝓨 M : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} [NormedAddCommGroup M]
  {μ ν : VectorMeasure 𝓧 M}

/-- Total variation distance between two vector measures, with value in `ℝ≥0∞`. -/
noncomputable def etvDist (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

lemma etvDist_eq_iSup_finPartition_eNorm :
    etvDist μ ν = ⨆ P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧))),
      ∑ x ∈ P.parts, ‖μ x - ν x‖ₑ := by
  simp [etvDist, variation, preVariation, ennrealPreVariation,
    ennrealToMeasure_apply .univ, preVariationFun]

@[deprecated (since := "2026-11-06")]
alias etvDist_eq_iSup_finPartition_enorm := etvDist_eq_iSup_finPartition_eNorm

@[simp]
lemma etvDist_self (μ : VectorMeasure 𝓧 M) : etvDist μ μ = 0 := by simp [etvDist]

@[simp]
lemma etvDist_eq_zero_iff (μ ν : VectorMeasure 𝓧 M) : etvDist μ ν = 0 ↔ μ = ν := by
  simp [etvDist, sub_eq_zero]

lemma etvDist_comm (μ ν : VectorMeasure 𝓧 M) : etvDist μ ν = etvDist ν μ := by
  rw [etvDist, etvDist, ← neg_sub, variation_neg]

lemma etvDist_triangle (μ ν ξ : VectorMeasure 𝓧 M) :
    etvDist μ ξ ≤ etvDist μ ν + etvDist ν ξ := by
  calc etvDist μ ξ
  _ = ((μ - ν) + (ν - ξ)).variation Set.univ := by simp [etvDist]
  _ ≤ etvDist μ ν + etvDist ν ξ := variation_add_le _

@[simp]
lemma etvDist_zero_right (μ : VectorMeasure 𝓧 M) : etvDist μ 0 = μ.variation Set.univ := by
  simp only [etvDist, sub_zero]

@[simp]
lemma etvDist_zero_left (ν : VectorMeasure 𝓧 M) : etvDist 0 ν = ν.variation Set.univ := by
  rw [etvDist_comm, etvDist_zero_right]

lemma etvDist_eq_etvDist_sub_zero : etvDist μ ν = etvDist (μ - ν) 0 := by simp [etvDist]

lemma etvDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    etvDist (μ.restrict s) (ν.restrict s) + etvDist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      etvDist μ ν := by
  simp [etvDist, ← restrict_sub, variation_restrict hs, variation_restrict hs.compl,
    MeasurableSet.univ, Measure.restrict_apply, ← measure_union disjoint_compl_right hs.compl]

/-- **Data processing inequality** for the total variation distance of vector measures:
pushing forward along a function does not increase the distance. -/
theorem etvDist_map_le (μ ν : VectorMeasure 𝓧 M) (f : 𝓧 → 𝓨) :
    etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν := by
  by_cases hf : Measurable f
  · calc etvDist (μ.map f) (ν.map f)
    _ = ((μ - ν).map f).variation Set.univ := by simp [etvDist, ← mapGm_apply, map_sub]
    _ ≤ (μ - ν).variation.map f Set.univ := variation_map_le _
    _ = etvDist μ ν := by rw [Measure.map_apply hf .univ, Set.preimage_univ, etvDist]
  · simp [map_not_measurable _ hf]

end VectorMeasure

end MeasureTheory
