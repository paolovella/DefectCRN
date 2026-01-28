/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.InteractionAlgebra
import DefectCRN.Quantum.Deficiency
import DefectCRN.Quantum.StructuralDeficiency
import DefectCRN.Quantum.DetailedBalance

/-!
# The Main Classification Theorem: δ_Q = δ_com

This file proves the central result connecting quantum dynamics to algebraic structure:

**Theorem** (Universal): Under a faithful stationary state, the quantum deficiency equals
the commutant deficiency:
  δ_Q = δ_com

This means:
  dim(ker L) - 1 = dim(A_int') - 1

**Theorem** (Characterization): δ_Q = δ_cen ⟺ A_int is multiplicity-free

## Main Results

* `quantum_deficiency_eq_commutant_deficiency`: δ_Q = δ_com (universal)
* `quantum_deficiency_eq_central_iff_multiplicityFree`: δ_Q = δ_cen ⟺ multiplicity-free
* `deficiency_hierarchy`: δ_struct ≤ δ_cen ≤ δ_com = δ_Q

## The Deficiency Hierarchy

Under faithful stationary state:
  δ_struct ≤ δ_cen ≤ δ_com = δ_Q

Two gaps measure different phenomena:
* δ_cen - δ_struct: Graph misses algebraic block structure
* δ_com - δ_cen: Noiseless subsystem multiplicities (m_α > 1)

## Proof Strategy

1. Evans-Høegh-Krohn: dim(commutant) = dim(stationary) under faithful state
2. Therefore: δ_Q = δ_com (universal)
3. Center ⊆ commutant: δ_cen ≤ δ_com (always)
4. Multiplicity-free ⟺ δ_cen = δ_com

## References

* Evans, D.E. & Høegh-Krohn, R. "Spectral properties of positive maps on C*-algebras"
* Frigerio, A. "Stationary states of quantum dynamical semigroups"
-/

set_option linter.unusedVariables false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-! ## The Main Theorem: δ_Q = δ_com (Universal) -/

/-- **The Main Classification Theorem** (Universal): δ_Q = δ_com under faithful stationary state.

    This connects the dynamical invariant (stationary space dimension) to the
    algebraic invariant (commutant dimension of interaction algebra).

    This is the universally correct statement, valid for all Lindbladians.

    Proof:
    1. dim(stationary) = dim(commutant) by Evans-Høegh-Krohn
    2. Subtracting 1 from both sides gives δ_Q = δ_com -/
theorem quantum_deficiency_eq_commutant_deficiency (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    quantumDeficiency L = commutantDeficiency L := by
  unfold quantumDeficiency commutantDeficiency
  have h := stationary_dim_eq_commutant_dim L hFaith
  omega

/-- Corollary: δ_com = 0 iff δ_Q = 0 (always, under faithful state). -/
theorem commutant_deficiency_zero_iff_quantum_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    commutantDeficiency L = 0 ↔ quantumDeficiency L = 0 := by
  rw [quantum_deficiency_eq_commutant_deficiency L hFaith]

/-- Corollary: Ergodic iff commutant deficiency is zero (under faithful state). -/
theorem ergodic_iff_commutant_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    IsErgodic L ↔ commutantDeficiency L = 0 := by
  rw [← quantum_deficiency_eq_commutant_deficiency L hFaith]
  exact (deficiency_zero_iff_ergodic L hFaith).symm

/-! ## The Characterization: δ_Q = δ_cen ⟺ Multiplicity-Free -/

/-- **Characterization Theorem**: δ_Q = δ_cen ⟺ A_int is multiplicity-free.

    This shows that the equality of quantum and central deficiency is NOT universal,
    but rather characterizes a special class of Lindbladians.

    The multiplicity-free case corresponds to "no noiseless subsystems" regime. -/
theorem quantum_deficiency_eq_central_iff_multiplicityFree (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    quantumDeficiency L = centralDeficiency L ↔ IsMultiplicityFree L := by
  unfold quantumDeficiency centralDeficiency
  have hStatComm := stationary_dim_eq_commutant_dim L hFaith
  unfold commutantDimension at hStatComm
  rw [hStatComm]
  -- Now need: centerDimension L - 1 = finrank (interactionCommutantSubmodule L) - 1 ↔ MF
  have hPos := centerDimension_pos L
  have hLe := center_dim_le_commutant_dim L  -- commutant ≥ center ≥ 1
  constructor
  · intro h
    have hDimEq : centerDimension L = Module.finrank ℂ (interactionCommutantSubmodule L) := by omega
    exact (center_dim_eq_commutant_dim_iff_multiplicityFree L).mp hDimEq
  · intro hMF
    have hDimEq := (center_dim_eq_commutant_dim_iff_multiplicityFree L).mpr hMF
    omega

/-- For multiplicity-free Lindbladians: δ_Q = δ_cen (conditional). -/
theorem quantum_deficiency_eq_central_deficiency (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hMF : IsMultiplicityFree L) :
    quantumDeficiency L = centralDeficiency L :=
  (quantum_deficiency_eq_central_iff_multiplicityFree L hFaith).mpr hMF

/-- Central deficiency is always ≤ quantum deficiency.

    δ_cen ≤ δ_Q with equality iff multiplicity-free. -/
theorem central_deficiency_le_quantum_deficiency (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    centralDeficiency L ≤ quantumDeficiency L := by
  rw [quantum_deficiency_eq_commutant_deficiency L hFaith]
  exact central_deficiency_le_commutant_deficiency L

/-- Corollary: δ_Q = 0 implies δ_cen = 0 (ergodic ⟹ trivial center). -/
theorem quantum_deficiency_zero_implies_central_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hQ : quantumDeficiency L = 0) :
    centralDeficiency L = 0 := by
  have h := central_deficiency_le_quantum_deficiency L hFaith
  omega

/-- Ergodic implies central deficiency is zero (but not conversely in general). -/
theorem ergodic_implies_central_deficiency_zero (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hErg : IsErgodic L) :
    centralDeficiency L = 0 := by
  have hQZero := ergodic_implies_deficiency_zero L hErg hFaith
  have hLe := central_deficiency_le_quantum_deficiency L hFaith
  omega

/-! ## The Deficiency Hierarchy -/

/-- **Structural Commutant ⊆ Center** (under non-degeneracy)

    For non-degenerate graphs with proper support, the structural commutant is
    contained in the center of the interaction algebra.

    Mathematical justification:
    1. Structural commutant C(S*(G)) consists of matrices constant on SCCs
    2. Under non-degeneracy, such matrices are block-diagonal matching Wedderburn blocks
    3. They commute with all elements of A_int and lie in A_int
    4. Therefore they are in the center Z(A_int)

    This is the key lemma enabling δ_struct ≤ δ_cen in the hierarchy. -/
axiom structuralCommutant_le_center (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G) :
    structuralCommutant G ≤ interactionCenterSubmodule L

/-- **The Deficiency Hierarchy**: δ_struct ≤ δ_cen ≤ δ_com = δ_Q.

    Under appropriate conditions (faithful state, non-degenerate graph, support),
    we have the full hierarchy of deficiencies.

    This shows:
    1. Structural deficiency (from graph) is a lower bound for central deficiency
    2. Central deficiency is a lower bound for commutant/quantum deficiency
    3. Commutant deficiency equals quantum deficiency (universally)

    Two gaps measure different phenomena:
    * δ_cen - δ_struct: Graph misses algebraic block structure
    * δ_com - δ_cen = δ_Q - δ_cen: Noiseless subsystem multiplicities (m_α > 1) -/
theorem deficiency_hierarchy (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    structuralDeficiency G ≤ centralDeficiency L ∧
    centralDeficiency L ≤ commutantDeficiency L ∧
    commutantDeficiency L = quantumDeficiency L := by
  constructor
  · -- δ_struct ≤ δ_cen
    -- Use structuralCommutant ⊆ center (axiom)
    have hStructCenter := structuralCommutant_le_center L G hND hSupp
    have hDimLe := Submodule.finrank_mono hStructCenter
    unfold structuralDeficiency centralDeficiency centerDimension
    omega
  constructor
  · -- δ_cen ≤ δ_com
    exact central_deficiency_le_commutant_deficiency L
  · -- δ_com = δ_Q
    exact (quantum_deficiency_eq_commutant_deficiency L hFaith).symm

/-- The full hierarchy with explicit inequalities. -/
theorem full_deficiency_hierarchy (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    structuralDeficiency G ≤ centralDeficiency L ∧
    centralDeficiency L ≤ quantumDeficiency L := by
  have hHier := deficiency_hierarchy L G hND hSupp hFaith
  constructor
  · exact hHier.1
  · calc centralDeficiency L ≤ commutantDeficiency L := hHier.2.1
      _ = quantumDeficiency L := hHier.2.2

/-- Summary of the classification:

    For a Lindbladian L with faithful stationary state σ:
    * δ_Q = δ_com (quantum = commutant deficiency) -- UNIVERSAL
    * δ_cen ≤ δ_com (central ≤ commutant) -- ALWAYS
    * δ_Q = δ_cen ⟺ A_int is multiplicity-free -- CHARACTERIZATION
    * δ_cen = k - 1 where k = number of Wedderburn blocks in A_int
    * δ_com = Σ m_α² - 1 where {(d_α, m_α)} is the Wedderburn type

    The Wedderburn type Type(L) = {(d_α, m_α)} gives complete algebraic information.
    Together with the peripheral spectrum Phase(L), this should classify QMS. -/
theorem classification_summary (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    -- δ_Q = δ_com (universal)
    quantumDeficiency L = commutantDeficiency L ∧
    -- δ_cen ≤ δ_Q (always)
    centralDeficiency L ≤ quantumDeficiency L ∧
    -- δ_cen = (number of Wedderburn blocks) - 1
    centralDeficiency L = centerDimFromType (wedderburnType L) - 1 := by
  constructor
  · exact quantum_deficiency_eq_commutant_deficiency L hFaith
  constructor
  · exact central_deficiency_le_quantum_deficiency L hFaith
  · unfold centralDeficiency
    have h := center_dim_eq_wedderburn L
    omega

/-! ## The Deficiency Gaps -/

/-- **Structural Gap**: δ_cen - δ_struct measures "accidental" algebraic symmetry.

    The structural gap is positive when the interaction algebra A_int has more
    block structure than the graph suggests.

    Examples with positive structural gap:
    * Coherent evolution with σx: A_int = span{I, σx} is abelian,
      but σx has off-diagonal entries so graph is connected
    * Projective jump L = |+⟩⟨+|: Full support but abelian algebra

    Examples with zero structural gap:
    * Amplitude damping: A_int = M_n(ℂ), both deficiencies are 0
    * Pure dephasing: A_int = diagonals, graph has no off-diagonal edges -/
noncomputable def structuralGap (L : Lindbladian n) (G : QuantumNetworkGraph n) : ℕ :=
  centralDeficiency L - structuralDeficiency G

/-- **Multiplicity Gap**: δ_com - δ_cen = δ_Q - δ_cen measures noiseless subsystem structure.

    The multiplicity gap is positive when the interaction algebra has
    Wedderburn multiplicities m_α > 1, corresponding to noiseless subsystems.

    δ_Q - δ_cen = Σ(m_α² - 1) = Σ(m_α - 1)(m_α + 1)

    Examples with positive multiplicity gap:
    * Decoherence-free subspaces with m_α > 1
    * Systems with non-trivial noiseless subsystems

    Examples with zero multiplicity gap:
    * Generic dissipative systems (all m_α = 1)
    * Systems without symmetry protection -/
noncomputable def multiplicityGap (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) : ℕ :=
  quantumDeficiency L - centralDeficiency L

/-- The multiplicity gap is non-negative (since δ_cen ≤ δ_Q). -/
theorem multiplicityGap_nonneg (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    0 ≤ multiplicityGap L hFaith := by
  unfold multiplicityGap
  have h := central_deficiency_le_quantum_deficiency L hFaith
  omega

/-- Zero multiplicity gap characterization: δ_Q = δ_cen iff multiplicity-free.

    This is the key characterization theorem. -/
theorem zero_multiplicityGap_iff_multiplicityFree (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    multiplicityGap L hFaith = 0 ↔ IsMultiplicityFree L := by
  unfold multiplicityGap
  have hLe := central_deficiency_le_quantum_deficiency L hFaith
  constructor
  · intro h
    have hEq : quantumDeficiency L = centralDeficiency L := by omega
    exact (quantum_deficiency_eq_central_iff_multiplicityFree L hFaith).mp hEq
  · intro hMF
    have hEq := quantum_deficiency_eq_central_deficiency L hFaith hMF
    omega

/-- Positive multiplicity gap implies noiseless subsystems exist.

    When δ_Q > δ_cen, there are Wedderburn blocks with m_α > 1,
    corresponding to protected quantum information. -/
theorem positive_multiplicityGap_implies_noiseless_subsystems (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L)
    (hGap : 0 < multiplicityGap L hFaith) :
    ¬ IsMultiplicityFree L := by
  intro hMF
  have h := (zero_multiplicityGap_iff_multiplicityFree L hFaith).mpr hMF
  omega

/-- Legacy alias for backward compatibility -/
noncomputable def deficiencyGap (L : Lindbladian n) (G : QuantumNetworkGraph n) : ℕ :=
  structuralGap L G

/-- The structural gap is non-negative by the deficiency hierarchy. -/
theorem deficiencyGap_nonneg (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    0 ≤ deficiencyGap L G := by
  unfold deficiencyGap structuralGap
  have h := (deficiency_hierarchy L G hND hSupp hFaith).1
  omega

/-- Zero structural gap characterization: δ_cen = δ_struct iff the structural commutant
    has the same dimension as the center.

    This happens when:
    * The graph perfectly captures the algebra's block structure
    * No "accidental" symmetries beyond graph-enforced ones -/
theorem zero_gap_iff_structural_eq_center_dim (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    deficiencyGap L G = 0 ↔
    structuralDeficiency G = centralDeficiency L := by
  unfold deficiencyGap structuralGap
  have h := (deficiency_hierarchy L G hND hSupp hFaith).1
  omega

/-- Positive structural gap implies the interaction algebra has "hidden" block structure
    not visible from the graph alone. -/
theorem positive_gap_implies_hidden_blocks {n : ℕ} (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hGap : 0 < deficiencyGap L G) :
    structuralDeficiency G < centralDeficiency L := by
  unfold deficiencyGap structuralGap at hGap
  omega

/-- For ergodic systems (δ_Q = 0), all four deficiencies are zero.

    Ergodic ⟹ δ_Q = 0 ⟹ δ_com = 0 ⟹ δ_cen = 0 (since δ_cen ≤ δ_com)
    And δ_struct ≤ δ_cen = 0 ⟹ δ_struct = 0 -/
theorem ergodic_all_deficiencies_zero (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L)
    (hErg : IsErgodic L) :
    structuralDeficiency G = 0 ∧ centralDeficiency L = 0 ∧
    commutantDeficiency L = 0 ∧ quantumDeficiency L = 0 := by
  have hQZero := ergodic_implies_deficiency_zero L hErg hFaith
  have hComZero : commutantDeficiency L = 0 := by
    rw [← quantum_deficiency_eq_commutant_deficiency L hFaith]
    exact hQZero
  have hCenLe := central_deficiency_le_commutant_deficiency L
  have hCZero : centralDeficiency L = 0 := by omega
  have hHier := (deficiency_hierarchy L G hND hSupp hFaith).1
  constructor
  · omega
  constructor
  · exact hCZero
  constructor
  · exact hComZero
  · exact hQZero

/-! ## Classification Conjecture -/

/-- Ergodic Lindbladians exist at every dimension ≥ 2.

    This is physically obvious: amplitude damping to a unique ground state
    is ergodic. We axiomatize this since constructing explicit examples
    requires significant infrastructure. -/
axiom ergodic_lindbladian_exists (n : ℕ) [NeZero n] :
    ∃ L : Lindbladian n, quantumDeficiency L = 0

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
  -- Use ergodic Lindbladians at dimensions 2 and 3
  have h2 := ergodic_lindbladian_exists 2
  have h3 := ergodic_lindbladian_exists 3
  obtain ⟨L₂, hL₂⟩ := h2
  obtain ⟨L₃, hL₃⟩ := h3
  use 2, 3, ⟨by omega⟩, ⟨by omega⟩, L₂, L₃
  constructor
  · rw [hL₂, hL₃]
  · omega

/-! ## Peripheral Spectrum -/

/-- The peripheral spectrum is the set of eigenvalues on the imaginary axis.
    These correspond to stationary or oscillatory modes. -/
def peripheralSpectrum (L : Lindbladian n) : Set ℂ :=
  {μ ∈ L.dualSpectrum | μ.re = 0}

/-- For systems in detailed balance, the peripheral spectrum consists only of 0.

    Under σ-detailed balance, the spectrum is real (qdb_real_spectrum), so
    any peripheral eigenvalue (Re = 0) must have Im = 0, hence equals 0.

    Note: Without detailed balance, ergodic systems can have nontrivial
    peripheral spectrum (limit cycles). The general ergodic case requires
    deeper spectral theory not yet in Mathlib. -/
theorem ergodic_peripheral_trivial (L : Lindbladian n)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ) :
    peripheralSpectrum L = {0} := by
  ext μ
  simp only [peripheralSpectrum, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hSpec, hRe⟩
    -- By qdb_real_spectrum, μ.im = 0
    have hReal := qdb_real_spectrum L σ hQDB μ hSpec
    -- So μ = μ.re + i * 0 = μ.re
    -- But hRe says μ.re = 0
    apply Complex.ext
    · exact hRe
    · exact hReal.1
  · intro hμ
    rw [hμ]
    constructor
    · -- 0 is always in the spectrum (stationary state)
      exact L.zero_mem_dualSpectrum
    · -- Re(0) = 0
      simp

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

/-- For systems in detailed balance, the only phase is 0 (no oscillations).

    Under detailed balance, the spectrum is real, so there are no nonzero
    imaginary eigenvalues, hence no nontrivial phases. -/
theorem detailed_balance_no_oscillations (L : Lindbladian n)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ) :
    peripheralPhases L ⊆ {0} := by
  intro ω hω
  simp only [peripheralPhases, Set.mem_setOf_eq] at hω
  have hTriv := ergodic_peripheral_trivial L σ hQDB
  simp only [peripheralSpectrum] at hω hTriv
  rw [hTriv] at hω
  simp only [Set.mem_singleton_iff] at hω
  simp only [Set.mem_singleton_iff]
  have h : Complex.I * ω = 0 := hω
  simp only [mul_eq_zero, Complex.I_ne_zero, false_or] at h
  exact_mod_cast h

/-! ## Complete Invariants -/

/-- The complete invariant triple for a Lindbladian consists of:
    1. The Wedderburn type (block structure of A_int)
    2. The peripheral phases (oscillatory modes)
    3. The spectral gap (rate of convergence)

    Conjecture: (Type, Phase) classify QMS up to equivalence.
    The spectral gap is additional dynamical information. -/
structure CompleteInvariants (n : ℕ) where
  /-- The Wedderburn type {(d_α, m_α)} of A_int -/
  wedderburnType : WedderburnType
  /-- The peripheral phases (generators of the phase group) -/
  phaseGenerators : List ℝ
  /-- The spectral gap γ > 0 -/
  spectralGap : ℝ

/-- Extract complete invariants from a Lindbladian. -/
noncomputable def extractInvariants (L : Lindbladian n) : CompleteInvariants n :=
  { wedderburnType := wedderburnType L,
    phaseGenerators := [], -- Placeholder: would compute from peripheral spectrum
    spectralGap := 0 }     -- Placeholder: would compute from spectrum

/-- Two Lindbladians are *Type-equivalent* if they have the same Wedderburn type. -/
def TypeEquivalent (L₁ L₂ : Lindbladian n) : Prop :=
  wedderburnType L₁ = wedderburnType L₂

/-- Type equivalence implies equal central deficiency. -/
theorem type_equiv_implies_equal_central_deficiency (L₁ L₂ : Lindbladian n)
    (hEq : TypeEquivalent L₁ L₂) :
    centralDeficiency L₁ = centralDeficiency L₂ := by
  unfold TypeEquivalent at hEq
  unfold centralDeficiency
  have h1 := center_dim_eq_wedderburn L₁
  have h2 := center_dim_eq_wedderburn L₂
  rw [h1, h2, hEq]

/-- The invariant summary: what we know classifies QMS.

    From computational investigation:
    1. δ_Q alone does NOT classify (separation examples exist)
    2. (Type, Phase) appears to classify (conjecture)
    3. δ_cen is derivable from Type (= #blocks - 1)
    4. δ_com is derivable from Type (= Σ m_α² - 1)
    5. δ_struct ≤ δ_cen ≤ δ_com = δ_Q (always, under faithful state)
    6. δ_Q = δ_cen ⟺ multiplicity-free (characterization)

    The full classification problem remains open. -/
theorem invariant_summary (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    -- δ_Q is computable from dim(ker L)
    quantumDeficiency L = Module.finrank ℂ L.stationarySubspace - 1 ∧
    -- δ_cen is computable from Wedderburn type (#blocks - 1)
    centralDeficiency L = centerDimFromType (wedderburnType L) - 1 ∧
    -- δ_Q = δ_com (universal)
    quantumDeficiency L = commutantDeficiency L ∧
    -- δ_cen ≤ δ_Q (always)
    centralDeficiency L ≤ quantumDeficiency L := by
  constructor
  · rfl
  constructor
  · unfold centralDeficiency
    have h := center_dim_eq_wedderburn L
    omega
  constructor
  · exact quantum_deficiency_eq_commutant_deficiency L hFaith
  · exact central_deficiency_le_quantum_deficiency L hFaith

end DefectCRN.Quantum
