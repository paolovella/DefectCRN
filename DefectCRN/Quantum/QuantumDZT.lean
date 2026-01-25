/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Deficiency
import DefectCRN.Quantum.Irreducibility
import DefectCRN.Quantum.DetailedBalance
import DefectCRN.Quantum.Frigerio

/-!
# The Quantum Deficiency Zero Theorem

This is the MAIN NEW CONTRIBUTION of this library: a quantum analog of the
classical Deficiency Zero Theorem from Chemical Reaction Network Theory.

## Main results

* `quantum_dzt_unique`: δ_Q = 0 implies unique stationary state
* `quantum_dzt_faithful`: δ_Q = 0 + QDB implies unique faithful state
* `quantum_dzt_convergence`: δ_Q = 0 + QDB implies exponential convergence

## Critical Note

The theorem "ergodic implies faithful stationary state" is FALSE.

**Counterexample**: Amplitude damping (see Examples/TwoLevel.lean)
  L = √γ |0⟩⟨1|,  H = ω|1⟩⟨1|

This system:
- IS ergodic (trivial commutant, δ_Q = 0)
- Has unique stationary state |0⟩⟨0| (a PURE state)
- The stationary state is NOT faithful (rank 1, not full rank)
- Does NOT satisfy QDB

Faithfulness requires the additional hypothesis of quantum detailed balance.

## Analogy with Classical CRNT

| Classical CRNT | Quantum CRNT |
|----------------|--------------|
| Deficiency zero | δ_Q = 0 (ergodic) |
| Weak reversibility | Trivial commutant |
| Complex-balanced equilibrium | Unique stationary state |
| Positive equilibrium | Requires QDB for faithful |

## References

* Carlen & Maas (2017) for QDB and convergence
* Fagnola & Umanità (2007) for generator structure
* Frigerio (1978) for uniqueness
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-! ### Part (a): Uniqueness from δ_Q = 0

This part does NOT require QDB and does NOT claim faithfulness. -/

/-- Quantum weak reversibility = irreducibility -/
def IsWeaklyReversible (L : Lindbladian n) : Prop :=
  IsIrreducible L

/-- **Quantum DZT Part (a)**: δ_Q = 0 implies unique stationary state.

    This does NOT require QDB and does NOT claim faithfulness.
    The stationary state may be a pure state (rank 1). -/
theorem quantum_dzt_unique (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ := by
  have hErg : IsErgodic L := deficiency_zero_iff_ergodic L |>.mp hDef
  exact ergodic_unique_stationary_density L hErg

/-- The unique stationary state from Quantum DZT -/
noncomputable def quantumDZTStationaryState (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0) : Matrix (Fin n) (Fin n) ℂ :=
  (quantum_dzt_unique L hDef).choose

/-- The QDZT stationary state is Hermitian -/
theorem quantumDZT_hermitian (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    (quantumDZTStationaryState L hDef).IsHermitian :=
  (quantum_dzt_unique L hDef).choose_spec.1.1

/-- The QDZT stationary state is positive semidefinite -/
theorem quantumDZT_posSemidef (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    IsPosSemidef (quantumDZTStationaryState L hDef) :=
  (quantum_dzt_unique L hDef).choose_spec.1.2.1

/-- The QDZT stationary state has trace 1 -/
theorem quantumDZT_trace (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    (quantumDZTStationaryState L hDef).trace = 1 :=
  (quantum_dzt_unique L hDef).choose_spec.1.2.2.1

/-- The QDZT stationary state is stationary -/
theorem quantumDZT_stationary (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    L.IsStationaryState (quantumDZTStationaryState L hDef) :=
  (quantum_dzt_unique L hDef).choose_spec.1.2.2.2

/-! ### Part (b): Faithfulness from δ_Q = 0 + QDB

This requires quantum detailed balance. -/

/-- **Quantum DZT Part (b)**: Under QDB, the unique stationary state is faithful.

    Proof sketch:
    1. σ is faithful by QDB definition
    2. σ is stationary by QDB definition
    3. By uniqueness (Part a), the unique stationary state equals σ
    4. Therefore the unique stationary state is faithful -/
theorem quantum_dzt_faithful (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ) :
    IsFaithful (quantumDZTStationaryState L hDef) := by
  -- σ is faithful by QDB
  have hσ_faithful := qdb_σ_faithful L σ hQDB
  -- σ is stationary by QDB
  have hσ_stat := qdb_σ_stationary L σ hQDB
  have hσ_trace := qdb_σ_trace L σ hQDB
  have hσ_herm : σ.IsHermitian := hσ_faithful.1
  have hσ_psd : IsPosSemidef σ := IsPositiveDefinite.toPosSemidef hσ_faithful
  -- By uniqueness (δ_Q = 0), the unique state equals σ
  have h_unique := (quantum_dzt_unique L hDef).choose_spec.2
  have h_eq : quantumDZTStationaryState L hDef = σ :=
    (h_unique σ ⟨hσ_herm, hσ_psd, hσ_trace, hσ_stat⟩).symm
  rw [h_eq]
  exact hσ_faithful

/-- Alternative: If ANY faithful stationary state exists, then THE stationary state is faithful -/
theorem quantum_dzt_faithful_of_exists (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (h_exists_faithful : ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      σ.IsHermitian ∧ IsPosSemidef σ ∧ σ.trace = 1 ∧ L.IsStationaryState σ ∧ IsFaithful σ) :
    IsFaithful (quantumDZTStationaryState L hDef) := by
  have hErg : IsErgodic L := deficiency_zero_iff_ergodic L |>.mp hDef
  -- Use Frigerio's result
  obtain ⟨σ, hσHerm, hσPSD, hσTr, hσStat, hσFaith⟩ := h_exists_faithful
  -- By uniqueness, σ = the unique stationary state
  have h_unique := (quantum_dzt_unique L hDef).choose_spec.2
  have h_eq : quantumDZTStationaryState L hDef = σ :=
    (h_unique σ ⟨hσHerm, hσPSD, hσTr, hσStat⟩).symm
  rw [h_eq]
  exact hσFaith

/-! ### Part (c): Exponential convergence from δ_Q = 0 + QDB

The proof uses the Heisenberg picture and duality. -/

/-- Spectral gap: δ_Q = 0 + QDB implies 0 is a simple eigenvalue with gap γ > 0.

    Mathematical justification:
    1. Primitivity (δ_Q = 0) implies dim(ker L*) = 1
    2. QDB implies L* is self-adjoint in ⟨·,·⟩_σ, so spectrum is real
    3. CP-divisibility implies all eigenvalues have Re ≤ 0
    4. Therefore: spectrum ⊆ {0} ∪ (-∞, -γ] for some γ > 0

    Reference: Carlen-Maas 2017 Theorem 4.1 -/
axiom spectral_gap_exists (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ) :
    ∃ γ : ℝ, γ > 0 ∧ ∀ μ ∈ L.dualSpectrum, μ ≠ 0 → Complex.abs μ ≥ γ

/-- Exponential decay in σ-GNS norm for observables (Heisenberg picture).

    For all A: ‖e^{tL*}(A) - Q₀(A)‖_σ ≤ e^{-γt} ‖A - Q₀(A)‖_σ

    This follows from:
    1. Self-adjointness of L* in ⟨·,·⟩_σ (QDB)
    2. Spectral gap γ > 0 (primitivity)
    3. Spectral theorem for self-adjoint operators -/
axiom heisenberg_exponential_decay (L : Lindbladian n)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ)
    (γ : ℝ) (hγ : γ > 0)
    (hgap : ∀ μ ∈ L.dualSpectrum, μ ≠ 0 → Complex.abs μ ≥ γ)
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (ht : t ≥ 0) :
    gnsNorm σ (L.dualEvolve t A - gnsProjection σ A) ≤
      Real.exp (-γ * t) * gnsNorm σ (A - gnsProjection σ A)

/-- **Quantum DZT Part (c)**: Exponential convergence in σ-GNS norm.

    ‖e^{tL}(ρ₀) - σ‖_σ ≤ C e^{-γt}

    where C = 2 λ_min(σ)^{-1/2} and γ > 0 is the spectral gap.

    Proof structure (Heisenberg-Schrödinger duality):
    1. By duality: Tr(A·(ρ(t) - σ)) = Tr((e^{tL*}A - Tr(σA)·I)·ρ₀)
    2. By Heisenberg decay: ‖e^{tL*}A - Q₀A‖_σ ≤ e^{-γt} ‖A - Q₀A‖_σ
    3. By norm comparison: ‖X‖_∞ ≤ λ_min(σ)^{-1/2} ‖X‖_σ
    4. Combining: ‖ρ(t) - σ‖_σ ≤ C e^{-γt}

    The full proof requires trace-norm duality theory not in Mathlib.
    See Carlen-Maas 2017, Theorem 4.3 for the complete argument. -/
axiom quantum_dzt_convergence (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ)
    (ρ₀ : Matrix (Fin n) (Fin n) ℂ)
    (hρ₀ : ρ₀.IsHermitian ∧ IsPosSemidef ρ₀ ∧ ρ₀.trace = 1) :
    ∃ C γ : ℝ, C > 0 ∧ γ > 0 ∧ ∀ t ≥ 0,
      gnsNorm σ (L.evolve t ρ₀ - σ) ≤ C * Real.exp (-γ * t)

/-! ### The Complete Theorem -/

/-- **The Complete Quantum Deficiency Zero Theorem**

    For a Lindbladian L with quantum deficiency δ_Q = 0 and satisfying
    quantum detailed balance w.r.t. σ:

    (a) **Uniqueness**: There exists a unique stationary density matrix
    (b) **Faithfulness**: The unique stationary state is faithful (= σ)
    (c) **Convergence**: All initial states converge exponentially to σ

    This is the quantum analog of the classical Deficiency Zero Theorem:
    - δ_Q = 0 corresponds to deficiency zero
    - QDB corresponds to weak reversibility
    - The result parallels: δ = 0 + weak rev ⟹ unique positive equilibrium -/
theorem quantum_deficiency_zero_theorem (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hQDB : SatisfiesQDB L σ) :
    -- (a) Uniqueness
    (∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ) ∧
    -- (b) Faithfulness
    IsFaithful (quantumDZTStationaryState L hDef) ∧
    -- (c) Convergence
    (∀ ρ₀ : Matrix (Fin n) (Fin n) ℂ,
      ρ₀.IsHermitian → IsPosSemidef ρ₀ → ρ₀.trace = 1 →
      ∃ C γ : ℝ, C > 0 ∧ γ > 0 ∧ ∀ t ≥ 0,
        gnsNorm σ (L.evolve t ρ₀ - σ) ≤ C * Real.exp (-γ * t)) :=
  ⟨quantum_dzt_unique L hDef,
   quantum_dzt_faithful L hDef σ hQDB,
   fun ρ₀ hρ₀_herm hρ₀_psd hρ₀_tr =>
     quantum_dzt_convergence L hDef σ hQDB ρ₀ ⟨hρ₀_herm, hρ₀_psd, hρ₀_tr⟩⟩

end DefectCRN.Quantum
