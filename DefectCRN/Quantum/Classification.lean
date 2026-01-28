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

/-! ## The Deficiency Gap -/

/-- The deficiency gap δ_cen - δ_struct measures "accidental" symmetry.

    The gap is positive when the interaction algebra A_int is "smaller"
    (more abelian) than what the graph structure suggests.

    Examples with positive gap:
    * Coherent evolution with σx: A_int = span{I, σx} is abelian,
      but σx has off-diagonal entries so graph is connected
    * Projective jump L = |+⟩⟨+|: Full support but abelian algebra

    Examples with zero gap:
    * Amplitude damping: A_int = M_n(ℂ), both deficiencies are 0
    * Pure dephasing: A_int = diagonals, graph has no off-diagonal edges -/
noncomputable def deficiencyGap (L : Lindbladian n) (G : QuantumNetworkGraph n) : ℕ :=
  centralDeficiency L - structuralDeficiency G

/-- The gap is non-negative by the deficiency hierarchy. -/
theorem deficiencyGap_nonneg (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    0 ≤ deficiencyGap L G := by
  unfold deficiencyGap
  have h := (deficiency_hierarchy L G hND hSupp hFaith).1
  omega

/-- Zero gap characterization: δ_cen = δ_struct iff the structural commutant
    has the same dimension as the center.

    This happens when:
    * The graph perfectly captures the algebra's block structure
    * No "accidental" symmetries beyond graph-enforced ones -/
theorem zero_gap_iff_structural_eq_center_dim (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    deficiencyGap L G = 0 ↔
    structuralDeficiency G = centralDeficiency L := by
  unfold deficiencyGap
  have h := (deficiency_hierarchy L G hND hSupp hFaith).1
  omega

/-- Positive gap implies the interaction algebra has "hidden" block structure
    not visible from the graph alone. -/
theorem positive_gap_implies_hidden_blocks {n : ℕ} (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hGap : 0 < deficiencyGap L G) :
    structuralDeficiency G < centralDeficiency L := by
  unfold deficiencyGap at hGap
  omega

/-- For ergodic systems (δ_Q = 0), all three deficiencies coincide. -/
theorem ergodic_all_deficiencies_zero (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L)
    (hErg : IsErgodic L) :
    structuralDeficiency G = 0 ∧ centralDeficiency L = 0 ∧ quantumDeficiency L = 0 := by
  have hQZero := ergodic_implies_deficiency_zero L hErg hFaith
  have hCZero := (ergodic_iff_central_deficiency_zero L hFaith).mp hErg
  have hHier := (deficiency_hierarchy L G hND hSupp hFaith).1
  constructor
  · omega
  constructor
  · exact hCZero
  · exact hQZero

/-! ## Classification Conjecture -/

/-- **Classification Conjecture** (informal):

    Two Lindbladians L₁, L₂ with faithful stationary states are equivalent
    (in an appropriate sense) iff:

    1. Type(L₁) = Type(L₂): Same Wedderburn signature {(d_α, m_α)}
    2. Phase(L₁) ≅ Phase(L₂): Isomorphic peripheral spectrum groups

    Note: δ_cen is redundant given Type (it equals the number of blocks - 1).

    The deficiency alone does NOT classify:
    * Same δ_Q = 0 but different Type: M₂(ℂ) vs M₃(ℂ)
    * Same δ_Q = 1 but different Type: ℂ² vs M₂ ⊕ M₂

    This is captured by the separation examples in the computational investigation. -/
theorem deficiency_does_not_classify :
    ∃ (n m : ℕ) (_ : NeZero n) (_ : NeZero m) (L₁ : Lindbladian n) (L₂ : Lindbladian m),
    -- Same quantum deficiency
    quantumDeficiency L₁ = quantumDeficiency L₂ ∧
    -- But different dimension (hence inequivalent)
    n ≠ m := by
  -- 2-level vs 3-level ergodic systems both have δ_Q = 0
  use 2, 3, ⟨by omega⟩, ⟨by omega⟩
  -- The existence is trivial by the type system
  sorry -- Would need to construct specific Lindbladians

/-! ## Peripheral Spectrum -/

/-- The peripheral spectrum is the set of eigenvalues on the imaginary axis.
    These correspond to stationary or oscillatory modes. -/
def peripheralSpectrum (L : Lindbladian n) : Set ℂ :=
  {μ ∈ L.dualSpectrum | μ.re = 0}

/-- For ergodic systems, the peripheral spectrum consists only of 0.
    This is because dim(ker L) = 1, so 0 has multiplicity 1 and
    all other eigenvalues have negative real part. -/
theorem ergodic_peripheral_trivial (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hErg : IsErgodic L) :
    peripheralSpectrum L = {0} := by
  -- Ergodic means unique stationary state, so dim(ker L*) = 1
  -- All other eigenvalues have Re < 0 (Perron-Frobenius type result)
  sorry -- Requires spectral theory not yet in Mathlib

/-- The phases of the peripheral spectrum form an additive group.
    This is because if μ, ν are peripheral eigenvalues, so is μ + ν
    (when the corresponding operators can be composed). -/
def peripheralPhases (L : Lindbladian n) : Set ℝ :=
  {ω : ℝ | (Complex.I * ω) ∈ peripheralSpectrum L}

/-- **Conjecture**: The peripheral phases form a finitely generated abelian group.

    For finite-dimensional systems, this should be ℤᵏ for some k.
    The generators correspond to fundamental frequencies of the dynamics. -/
axiom peripheral_phases_finitely_generated (L : Lindbladian n) :
    ∃ (k : ℕ) (gens : Fin k → ℝ), ∀ ω ∈ peripheralPhases L,
      ∃ coeffs : Fin k → ℤ, ω = ∑ i, (coeffs i : ℝ) * gens i

/-- For ergodic systems, the only phase is 0 (no oscillations). -/
theorem ergodic_no_oscillations (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hErg : IsErgodic L) :
    peripheralPhases L ⊆ {0} := by
  intro ω hω
  simp only [peripheralPhases, Set.mem_setOf_eq] at hω
  have hTriv := ergodic_peripheral_trivial L hFaith hErg
  simp only [peripheralSpectrum] at hω hTriv
  rw [hTriv] at hω
  simp only [Set.mem_singleton_iff] at hω
  simp only [Set.mem_singleton_iff]
  have h : Complex.I * ω = 0 := hω
  simp only [mul_eq_zero, Complex.I_ne_zero, false_or] at h
  exact_mod_cast h

end DefectCRN.Quantum
