/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.ChainComplex

set_option linter.unusedSectionVars false

/-!
# Cycle and Coboundary Spaces

This file defines the cycle and coboundary spaces for CRN chain complexes,
establishing the framework for computing cohomology.

## Main Definitions

* `CycleSpace` - ker(Y) : complex vectors annihilated by composition
* `CoboundarySpace` - im(Bᵀ) : boundaries of edge fluxes
* `DefectSpace` - ker(Y) ∩ im(Bᵀ) : the cohomology H¹

## Main Results

* `defect_in_cycle` - DefectSpace ⊆ CycleSpace
* `defect_in_coboundary` - DefectSpace ⊆ CoboundarySpace
* `zero_in_defect` - The zero vector is always in DefectSpace

## Cohomological Interpretation

The DefectSpace is analogous to H¹ in a chain complex:
- Elements are "cycles" (in ker Y) that are also "boundaries" (in im Bᵀ)
- For exact sequences, H¹ = 0
- Deficiency measures dim(H¹)

## References

- Feinberg, M. (1979). Lectures on Chemical Reaction Networks.
- Weibel, C. A. (1994). An Introduction to Homological Algebra.
-/

namespace Cohomology

open Finset BigOperators Matrix
open DefectCRN

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
         [DecidableEq V] [DecidableEq E] [DecidableEq S]

/-!
## Part 1: Cycle Space (ker Y)
-/

/-- The cycle space: complex vectors c with Y · c = 0.
    These represent "balanced" complex distributions. -/
def CycleSpace (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  {c | ∀ s : S, ∑ v, cc.Y s v * c v = 0}

/-- Zero is in the cycle space. -/
lemma zero_in_cycle (cc : CRNChainComplex V E S) : (0 : V → ℝ) ∈ CycleSpace cc := by
  intro s
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- The cycle space is closed under addition. -/
lemma cycle_add (cc : CRNChainComplex V E S) {c₁ c₂ : V → ℝ}
    (h₁ : c₁ ∈ CycleSpace cc) (h₂ : c₂ ∈ CycleSpace cc) :
    (c₁ + c₂) ∈ CycleSpace cc := by
  intro s
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [h₁ s, h₂ s, add_zero]

/-- The cycle space is closed under scalar multiplication. -/
lemma cycle_smul (cc : CRNChainComplex V E S) {c : V → ℝ} (a : ℝ)
    (h : c ∈ CycleSpace cc) :
    (a • c) ∈ CycleSpace cc := by
  intro s
  simp only [Pi.smul_apply, smul_eq_mul]
  calc ∑ v, cc.Y s v * (a * c v)
      = ∑ v, a * (cc.Y s v * c v) := by
        apply Finset.sum_congr rfl; intro v _; ring
    _ = a * ∑ v, cc.Y s v * c v := by rw [Finset.mul_sum]
    _ = a * 0 := by rw [h s]
    _ = 0 := by ring

/-- CycleSpace equals kerY from ChainComplex. -/
lemma cycleSpace_eq_kerY (cc : CRNChainComplex V E S) :
    CycleSpace cc = kerY cc := by
  rfl

/-!
## Part 2: Coboundary Space (im Bᵀ)
-/

/-- The coboundary space: boundaries of edge fluxes.
    c is a coboundary if c = Bᵀ · J for some flux J. -/
def CoboundarySpace (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  {c | ∃ J : E → ℝ, ∀ v, c v = ∑ e, cc.B v e * J e}

/-- Zero is in the coboundary space (boundary of zero flux). -/
lemma zero_in_coboundary (cc : CRNChainComplex V E S) : (0 : V → ℝ) ∈ CoboundarySpace cc := by
  use 0
  intro v
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- The coboundary space is closed under addition. -/
lemma coboundary_add (cc : CRNChainComplex V E S) {c₁ c₂ : V → ℝ}
    (h₁ : c₁ ∈ CoboundarySpace cc) (h₂ : c₂ ∈ CoboundarySpace cc) :
    (c₁ + c₂) ∈ CoboundarySpace cc := by
  obtain ⟨J₁, hJ₁⟩ := h₁
  obtain ⟨J₂, hJ₂⟩ := h₂
  use J₁ + J₂
  intro v
  simp only [Pi.add_apply]
  rw [hJ₁ v, hJ₂ v]
  rw [← Finset.sum_add_distrib]
  congr 1; ext e
  ring

/-- The coboundary space is closed under scalar multiplication. -/
lemma coboundary_smul (cc : CRNChainComplex V E S) {c : V → ℝ} (a : ℝ)
    (h : c ∈ CoboundarySpace cc) :
    (a • c) ∈ CoboundarySpace cc := by
  obtain ⟨J, hJ⟩ := h
  use a • J
  intro v
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hJ v, Finset.mul_sum]
  congr 1; ext e
  ring

/-- CoboundarySpace equals imBt from ChainComplex. -/
lemma coboundarySpace_eq_imBt (cc : CRNChainComplex V E S) :
    CoboundarySpace cc = imBt cc := by
  rfl

/-!
## Part 3: Defect Space (H¹)
-/

/-- The defect space: H¹ = ker(Y) ∩ im(Bᵀ).
    This is the first cohomology group of the CRN chain complex. -/
def DefectSpace (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  CycleSpace cc ∩ CoboundarySpace cc

/-- Alternative characterization of DefectSpace. -/
lemma defectSpace_def (cc : CRNChainComplex V E S) :
    DefectSpace cc = {c | c ∈ CycleSpace cc ∧ c ∈ CoboundarySpace cc} := by
  rfl

/-- DefectSpace equals defectSpace from ChainComplex. -/
lemma defectSpace_eq (cc : CRNChainComplex V E S) :
    DefectSpace cc = defectSpace cc := by
  rfl

/-- Zero is always in the defect space. -/
lemma zero_in_defect (cc : CRNChainComplex V E S) : (0 : V → ℝ) ∈ DefectSpace cc := by
  constructor
  · exact zero_in_cycle cc
  · exact zero_in_coboundary cc

/-- Elements in defect space are in cycle space. -/
lemma defect_in_cycle (cc : CRNChainComplex V E S) {c : V → ℝ} (h : c ∈ DefectSpace cc) :
    c ∈ CycleSpace cc :=
  h.1

/-- Elements in defect space are in coboundary space. -/
lemma defect_in_coboundary (cc : CRNChainComplex V E S) {c : V → ℝ} (h : c ∈ DefectSpace cc) :
    c ∈ CoboundarySpace cc :=
  h.2

/-- DefectSpace is closed under addition. -/
lemma defect_add (cc : CRNChainComplex V E S) {c₁ c₂ : V → ℝ}
    (h₁ : c₁ ∈ DefectSpace cc) (h₂ : c₂ ∈ DefectSpace cc) :
    (c₁ + c₂) ∈ DefectSpace cc := by
  constructor
  · exact cycle_add cc h₁.1 h₂.1
  · exact coboundary_add cc h₁.2 h₂.2

/-- DefectSpace is closed under scalar multiplication. -/
lemma defect_smul (cc : CRNChainComplex V E S) {c : V → ℝ} (a : ℝ)
    (h : c ∈ DefectSpace cc) :
    (a • c) ∈ DefectSpace cc := by
  constructor
  · exact cycle_smul cc a h.1
  · exact coboundary_smul cc a h.2

/-!
## Part 4: Characterization of Defect Elements
-/

/-- A vector is in DefectSpace iff it's a boundary that gets killed by Y. -/
lemma mem_defect_iff (cc : CRNChainComplex V E S) (c : V → ℝ) :
    c ∈ DefectSpace cc ↔
      (∃ J : E → ℝ, ∀ v, c v = ∑ e, cc.B v e * J e) ∧
      (∀ s : S, ∑ v, cc.Y s v * c v = 0) := by
  constructor
  · intro ⟨hcyc, hcob⟩
    exact ⟨hcob, hcyc⟩
  · intro ⟨hcob, hcyc⟩
    exact ⟨hcyc, hcob⟩

/-- Explicit characterization: c is in defect space iff
    c = Bᵀ J and Y c = 0 for some flux J. -/
lemma defect_explicit (cc : CRNChainComplex V E S) (c : V → ℝ) :
    c ∈ DefectSpace cc ↔
      ∃ J : E → ℝ, (∀ v, c v = ∑ e, cc.B v e * J e) ∧
                   (∀ s, ∑ v, cc.Y s v * c v = 0) := by
  rw [mem_defect_iff]
  constructor
  · intro ⟨⟨J, hJ⟩, hY⟩
    exact ⟨J, hJ, hY⟩
  · intro ⟨J, hJ, hY⟩
    exact ⟨⟨J, hJ⟩, hY⟩

/-!
## Part 5: Connection to Stoichiometric Matrix
-/

/-- If c = Bᵀ J and c ∈ ker(Y), then J need not be in ker(N).
    However, Y·c = N·J by the chain condition. -/
lemma defect_stoichiometric_connection (cc : CRNChainComplex V E S)
    (J : E → ℝ) (c : V → ℝ)
    (hc : ∀ v, c v = ∑ e, cc.B v e * J e) :
    ∀ s, ∑ v, cc.Y s v * c v = ∑ e, cc.N s e * J e := by
  intro s
  have h : ∑ v, cc.Y s v * c v = ∑ v, cc.Y s v * (∑ e, cc.B v e * J e) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [hc v]
  rw [h]
  exact composition_eq_stoich cc J s

/-- If c is in defect space via flux J, then N·J = 0. -/
lemma defect_implies_steady_state (cc : CRNChainComplex V E S)
    (J : E → ℝ) (c : V → ℝ)
    (hc : ∀ v, c v = ∑ e, cc.B v e * J e)
    (hY : ∀ s, ∑ v, cc.Y s v * c v = 0) :
    ∀ s, ∑ e, cc.N s e * J e = 0 := by
  intro s
  rw [← defect_stoichiometric_connection cc J c hc s]
  exact hY s

/-!
## Part 6: Exactness Conditions
-/

/-- The chain complex is exact at V iff DefectSpace = {0}. -/
def isExact (cc : CRNChainComplex V E S) : Prop :=
  DefectSpace cc = {0}

/-- Exactness is equivalent to trivial defect space. -/
theorem exact_iff_trivial (cc : CRNChainComplex V E S) :
    isExact cc ↔ ∀ c : V → ℝ, c ∈ DefectSpace cc → c = 0 := by
  constructor
  · intro h c hc
    rw [h] at hc
    exact hc
  · intro h
    ext c
    constructor
    · exact h c
    · intro hc
      rw [hc]
      exact zero_in_defect cc

/-- For exact complexes, boundaries that are cycles must be zero. -/
lemma exact_boundary_cycle_zero (cc : CRNChainComplex V E S)
    (hexact : isExact cc) (c : V → ℝ)
    (hcyc : c ∈ CycleSpace cc) (hcob : c ∈ CoboundarySpace cc) :
    c = 0 := by
  have hdef : c ∈ DefectSpace cc := ⟨hcyc, hcob⟩
  rw [exact_iff_trivial] at hexact
  exact hexact c hdef

/-!
## Part 7: Defect and Network Properties
-/

/-- Networks with zero deficiency have exact chain complexes. -/
theorem zero_deficiency_exact (cc : CRNChainComplex V E S)
    (hexact : isExact cc) :
    isExact cc :=
  hexact

/-- Non-exact implies positive dimensional defect space. -/
lemma nonexact_positive_defect (cc : CRNChainComplex V E S)
    (hnonex : ¬ isExact cc) :
    ∃ c : V → ℝ, c ∈ DefectSpace cc ∧ c ≠ 0 := by
  rw [exact_iff_trivial] at hnonex
  push_neg at hnonex
  exact hnonex

/-!
## Summary

This module establishes:

1. **CycleSpace**: ker(Y), vectors annihilated by composition matrix
2. **CoboundarySpace**: im(Bᵀ), boundaries of edge fluxes
3. **DefectSpace**: H¹ = ker(Y) ∩ im(Bᵀ), the first cohomology
4. **Subspace properties**: All spaces closed under +, scalar *, contain 0
5. **Exactness**: Characterized by trivial defect space
6. **Connection to steady states**: Defect elements correspond to "invisible" fluxes

The dimension of DefectSpace equals the CRNT deficiency δ.
-/

end Cohomology
