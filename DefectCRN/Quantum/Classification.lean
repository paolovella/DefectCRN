/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.InteractionAlgebra
import DefectCRN.Quantum.Deficiency
import DefectCRN.Quantum.StructuralDeficiency

/-!
# The Main Classification Theorem: δ_Q = δ_cen

This file proves the central result connecting quantum dynamics to algebraic structure:

**Theorem**: Under a faithful stationary state, the quantum deficiency equals
the central deficiency:
  δ_Q = δ_cen

This means:
  dim(ker L) - 1 = dim(Z(A_int)) - 1

## Main Results

* `quantum_deficiency_eq_central_deficiency`: δ_Q = δ_cen under faithful state
* `deficiency_hierarchy`: δ_struct ≤ δ_cen = δ_Q under appropriate conditions

## Proof Strategy

1. Evans-Høegh-Krohn: dim(commutant) = dim(stationary) under faithful state
2. Multiplicity-free: dim(center) = dim(commutant) for interaction algebras
3. Combine: dim(center) = dim(stationary)

## References

* Evans, D.E. & Høegh-Krohn, R. "Spectral properties of positive maps on C*-algebras"
* Frigerio, A. "Stationary states of quantum dynamical semigroups"
-/

set_option linter.unusedVariables false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-! ## The Main Theorem: δ_Q = δ_cen -/

/-- **The Main Classification Theorem**: δ_Q = δ_cen under faithful stationary state.

    This connects the dynamical invariant (stationary space dimension) to the
    algebraic invariant (center dimension of interaction algebra).

    Proof:
    1. dim(stationary) = dim(center) by `stationary_dim_eq_center_dim`
    2. Subtracting 1 from both sides gives δ_Q = δ_cen -/
theorem quantum_deficiency_eq_central_deficiency (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    quantumDeficiency L = centralDeficiency L := by
  unfold quantumDeficiency centralDeficiency
  have h := stationary_dim_eq_center_dim L hFaith
  omega

/-- Corollary: δ_cen = 0 iff δ_Q = 0 (assuming faithful stationary state). -/
theorem central_deficiency_zero_iff_quantum_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    centralDeficiency L = 0 ↔ quantumDeficiency L = 0 := by
  rw [quantum_deficiency_eq_central_deficiency L hFaith]

/-- Corollary: Ergodic iff central deficiency is zero (under faithful state). -/
theorem ergodic_iff_central_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    IsErgodic L ↔ centralDeficiency L = 0 := by
  rw [← quantum_deficiency_eq_central_deficiency L hFaith]
  exact (deficiency_zero_iff_ergodic L hFaith).symm

/-! ## The Deficiency Hierarchy -/

/-- **The Deficiency Hierarchy**: δ_struct ≤ δ_cen = δ_Q.

    Under appropriate conditions (faithful state, non-degenerate graph, support),
    we have the full hierarchy of deficiencies.

    This shows:
    1. Structural deficiency (from graph) is a lower bound
    2. Central deficiency (algebraic) equals quantum deficiency (dynamical) -/
theorem deficiency_hierarchy (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    structuralDeficiency G ≤ centralDeficiency L ∧
    centralDeficiency L = quantumDeficiency L := by
  constructor
  · -- δ_struct ≤ δ_cen
    -- Use the chain: structuralCommutant ⊆ commutant = interactionCommutant
    have hStructComm := structuralCommutant_le_commutant L G hND hSupp
    -- commutant = interactionCommutant
    have hCommEq := commutantSubmodule_eq_interactionCommutantSubmodule L
    rw [hCommEq] at hStructComm
    -- finrank is monotonic under inclusion
    have hDimLe := Submodule.finrank_mono hStructComm
    -- center dim = commutant dim for multiplicity-free algebras
    have hCenterComm := center_dim_eq_commutant_dim L
    -- So finrank(structuralCommutant) ≤ centerDimension L
    rw [← hCenterComm] at hDimLe
    -- Subtracting 1 from both sides preserves the inequality
    unfold structuralDeficiency centralDeficiency
    exact Nat.sub_le_sub_right hDimLe 1
  · -- δ_cen = δ_Q
    exact (quantum_deficiency_eq_central_deficiency L hFaith).symm

/-- Summary of the classification:

    For a Lindbladian L with faithful stationary state σ:
    * δ_Q = δ_cen (quantum = algebraic deficiency)
    * δ_struct ≤ δ_cen (structural is a lower bound)
    * δ_cen = k - 1 where k = number of Wedderburn blocks in A_int

    The Wedderburn type Type(L) = {(d_α, 1)} gives complete algebraic information.
    Together with the peripheral spectrum Phase(L), this should classify QMS. -/
theorem classification_summary (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    -- δ_Q = δ_cen
    quantumDeficiency L = centralDeficiency L ∧
    -- δ_cen = (number of Wedderburn blocks) - 1
    centralDeficiency L = centerDimFromType (wedderburnType L) - 1 := by
  constructor
  · exact quantum_deficiency_eq_central_deficiency L hFaith
  · unfold centralDeficiency
    have h := center_dim_eq_wedderburn L
    omega

end DefectCRN.Quantum
