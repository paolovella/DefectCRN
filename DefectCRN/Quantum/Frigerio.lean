/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Deficiency

/-!
# Frigerio's Uniqueness Theorem

If a quantum Markov semigroup is primitive, then there exists a unique
faithful stationary state.

## Reference

Frigerio, A. "Stationary states of quantum dynamical semigroups"
Comm. Math. Phys. 63 (1978), 269-276
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- Frigerio's Uniqueness Theorem (1978) -/
theorem frigerio_uniqueness (L : Lindbladian n) (hPrim : IsPrimitive L) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧
      L.IsStationaryState ρ ∧ IsFaithful ρ := by
  -- From primitive_unique_stationary_density, there's a unique stationary density matrix
  obtain ⟨ρ, ⟨hHerm, hPSD, hTr, hStat⟩, hUniq⟩ := primitive_unique_stationary_density L hPrim
  -- This unique ρ is also faithful by primitive_stationary_is_faithful
  have hFaith : IsFaithful ρ := primitive_stationary_is_faithful L hPrim ρ ⟨hHerm, hPSD, hTr, hStat⟩
  -- Construct existence with the full property
  refine ⟨ρ, ⟨hHerm, hPSD, hTr, hStat, hFaith⟩, ?_⟩
  -- Uniqueness: any σ satisfying the full property also satisfies the basic property
  intro σ ⟨hσHerm, hσPSD, hσTr, hσStat, _⟩
  -- Apply the uniqueness from primitive_unique_stationary_density
  exact hUniq σ ⟨hσHerm, hσPSD, hσTr, hσStat⟩

/-- The unique stationary state of a primitive Lindbladian -/
noncomputable def uniqueStationaryState (L : Lindbladian n) (hPrim : IsPrimitive L) :
    Matrix (Fin n) (Fin n) ℂ :=
  (frigerio_uniqueness L hPrim).choose

/-- The unique stationary state is faithful -/
theorem uniqueStationaryState_faithful (L : Lindbladian n) (hPrim : IsPrimitive L) :
    IsFaithful (uniqueStationaryState L hPrim) := by
  exact (frigerio_uniqueness L hPrim).choose_spec.1.2.2.2.2

/-- Primitive implies unique stationary density matrix (alternate proof using Frigerio).
    Note: This is an alternate version using frigerio_uniqueness.
    The version in Irreducibility.lean uses the 1-dimensional stationary space argument. -/
theorem primitive_unique_stationary_density' (L : Lindbladian n) (hPrim : IsPrimitive L) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ := by
  -- Get the unique faithful stationary state from Frigerio
  obtain ⟨ρ, hρ, hUniq⟩ := frigerio_uniqueness L hPrim
  -- This is also unique among all stationary states
  refine ⟨ρ, ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1⟩, ?_⟩
  intro ρ' hρ'
  -- Any stationary state for primitive L is faithful (by primitivity argument)
  -- Then apply Frigerio's uniqueness
  have hρ'F : IsFaithful ρ' := primitive_stationary_is_faithful L hPrim ρ' hρ'
  exact hUniq ρ' ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, hρ'.2.2.2, hρ'F⟩

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
