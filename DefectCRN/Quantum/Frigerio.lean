/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Deficiency

/-!
# Frigerio's Uniqueness Theorem (Corrected)

For primitive quantum Markov semigroups, there exists a **unique** stationary state.

## IMPORTANT CORRECTION

The original claim that "primitive implies faithful stationary state" is **FALSE**.

**Counterexample**: Two-level amplitude damping
  L = √γ |0⟩⟨1|,  H = ω|1⟩⟨1|

This system:
- IS primitive (commutant = ℂI, so δ_Q = 0)
- Has unique stationary state ρ = |0⟩⟨0| (a pure state, rank 1)
- The stationary state is NOT faithful (it has a zero eigenvalue)

## Correct Statement

**Theorem**: If L is primitive, then there exists a unique stationary density matrix.
The stationary state may or may not be faithful depending on the specific dynamics.

## When IS the stationary state faithful?

The stationary state is faithful when:
1. The system satisfies quantum detailed balance, OR
2. There exists at least one faithful stationary state (then by uniqueness, THE stationary state is faithful)

## Reference

Frigerio, A. "Stationary states of quantum dynamical semigroups"
Comm. Math. Phys. 63 (1978), 269-276

Note: Frigerio's paper proves results about the STRUCTURE of stationary states,
not that all stationary states are faithful.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- Frigerio's Uniqueness Theorem (1978) - CORRECTED VERSION

    For a primitive Lindbladian, there exists a unique stationary density matrix.

    NOTE: We do NOT claim the stationary state is faithful. It may be a pure state
    (rank 1) as in the amplitude damping example. -/
theorem frigerio_uniqueness (L : Lindbladian n) (hPrim : IsPrimitive L) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ :=
  primitive_unique_stationary_density L hPrim

/-- The unique stationary state of a primitive Lindbladian -/
noncomputable def uniqueStationaryState (L : Lindbladian n) (hPrim : IsPrimitive L) :
    Matrix (Fin n) (Fin n) ℂ :=
  (frigerio_uniqueness L hPrim).choose

/-- The unique stationary state is Hermitian -/
theorem uniqueStationaryState_hermitian (L : Lindbladian n) (hPrim : IsPrimitive L) :
    (uniqueStationaryState L hPrim).IsHermitian :=
  (frigerio_uniqueness L hPrim).choose_spec.1.1

/-- The unique stationary state is positive semidefinite -/
theorem uniqueStationaryState_posSemidef (L : Lindbladian n) (hPrim : IsPrimitive L) :
    IsPosSemidef (uniqueStationaryState L hPrim) :=
  (frigerio_uniqueness L hPrim).choose_spec.1.2.1

/-- The unique stationary state has trace 1 -/
theorem uniqueStationaryState_trace (L : Lindbladian n) (hPrim : IsPrimitive L) :
    (uniqueStationaryState L hPrim).trace = 1 :=
  (frigerio_uniqueness L hPrim).choose_spec.1.2.2.1

/-- The unique stationary state is stationary -/
theorem uniqueStationaryState_stationary (L : Lindbladian n) (hPrim : IsPrimitive L) :
    L.IsStationaryState (uniqueStationaryState L hPrim) :=
  (frigerio_uniqueness L hPrim).choose_spec.1.2.2.2

/-- If a faithful stationary state exists for a primitive Lindbladian,
    then THE unique stationary state is that faithful state.

    This is the correct version of the "primitive implies faithful" claim:
    it requires the ADDITIONAL hypothesis that a faithful state exists. -/
theorem primitive_faithful_of_exists_faithful (L : Lindbladian n) (hPrim : IsPrimitive L)
    (h_exists : ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      σ.IsHermitian ∧ IsPosSemidef σ ∧ σ.trace = 1 ∧ L.IsStationaryState σ ∧ IsFaithful σ) :
    IsFaithful (uniqueStationaryState L hPrim) := by
  obtain ⟨σ, hσHerm, hσPSD, hσTr, hσStat, hσFaith⟩ := h_exists
  -- By uniqueness, σ = uniqueStationaryState L hPrim
  have hUniq := (frigerio_uniqueness L hPrim).choose_spec.2
  have hEq : σ = uniqueStationaryState L hPrim :=
    hUniq σ ⟨hσHerm, hσPSD, hσTr, hσStat⟩
  rw [← hEq]
  exact hσFaith

/-- The quantum dynamical semigroup e^{tL} applied to a density matrix.
    This requires matrix exponential infrastructure not yet in Mathlib.

    Mathematical definition: For Lindbladian L and density matrix ρ₀,
    ρ(t) = e^{tL}(ρ₀) is the unique solution to dρ/dt = L(ρ) with ρ(0) = ρ₀. -/
axiom quantumSemigroup (L : Lindbladian n) (t : ℝ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ

/-- Convergence to stationary state for primitive Lindbladians.

    For a primitive Lindbladian L with unique stationary state ρ_∞,
    any initial density matrix ρ₀ evolves as:
        ρ(t) = e^{tL}(ρ₀) → ρ_∞ as t → ∞

    Mathematical justification:
    1. Primitivity implies the spectrum of L has 0 as a simple eigenvalue
       and all other eigenvalues have strictly negative real part.
    2. The spectral gap γ = min{-Re(λ) : λ ∈ σ(L), λ ≠ 0} > 0 determines
       the exponential convergence rate.
    3. Therefore ‖e^{tL}(ρ₀) - ρ_∞‖ ≤ C·e^{-γt} → 0 as t → ∞.

    NOTE: The limit ρ_∞ may or may not be faithful. For amplitude damping,
    all states converge to |0⟩⟨0|, which is a pure (non-faithful) state.

    References:
    - Frigerio, A. "Stationary states of quantum dynamical semigroups" (1978)
    - Spohn, H. "An algebraic condition for the approach to equilibrium" (1977) -/
axiom convergence_to_stationary (L : Lindbladian n) (hPrim : IsPrimitive L)
    (ρ₀ : Matrix (Fin n) (Fin n) ℂ)
    (hρ₀ : ρ₀.IsHermitian ∧ IsPosSemidef ρ₀ ∧ ρ₀.trace = 1) :
    Filter.Tendsto
      (fun t : ℝ => quantumSemigroup L t ρ₀)
      Filter.atTop
      (nhds (uniqueStationaryState L hPrim))

end DefectCRN.Quantum
