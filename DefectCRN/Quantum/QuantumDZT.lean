/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Frigerio

/-!
# Quantum Deficiency Zero Theorem

This is the MAIN NEW CONTRIBUTION of this library.

## Main result

**Quantum Deficiency Zero Theorem:** If a quantum Markov semigroup has
quantum deficiency δ_Q = 0, then it has a unique, globally attracting,
faithful stationary state.

This is the quantum analog of the classical Deficiency Zero Theorem
of Horn-Jackson-Feinberg.

## Novelty

This theorem is NEW - it unifies:
- Frigerio's result on primitive semigroups
- Classical CRNT deficiency theory
- The algebraic characterization via commutants
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- Quantum weak reversibility = irreducibility -/
def IsWeaklyReversible (L : Lindbladian n) : Prop :=
  IsIrreducible L

/-- **Quantum Deficiency Zero Theorem** -/
theorem quantum_deficiency_zero_theorem (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧
      L.IsStationaryState ρ ∧ IsFaithful ρ := by
  have hPrim : IsPrimitive L := deficiency_zero_iff_primitive L |>.mp hDef
  exact frigerio_uniqueness L hPrim

/-- The unique stationary state from Quantum DZT -/
noncomputable def quantumDZTStationaryState (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0) : Matrix (Fin n) (Fin n) ℂ :=
  (quantum_deficiency_zero_theorem L hDef).choose

/-- The QDZT stationary state is faithful -/
theorem quantumDZT_faithful (L : Lindbladian n) (hDef : quantumDeficiency L = 0) :
    IsFaithful (quantumDZTStationaryState L hDef) :=
  (quantum_deficiency_zero_theorem L hDef).choose_spec.1.2.2.2.2

/-- QDZT Convergence: For deficiency zero Lindbladians, all initial states
    converge to the unique stationary state.

    This is the quantum analog of the classical result that deficiency zero
    reaction networks with weak reversibility have globally attracting
    complex-balanced equilibria.

    Proof: Direct corollary of `convergence_to_stationary` via definitional unfolding. -/
theorem quantum_dzt_convergence (L : Lindbladian n)
    (hDef : quantumDeficiency L = 0)
    (ρ₀ : Matrix (Fin n) (Fin n) ℂ)
    (hρ₀ : ρ₀.IsHermitian ∧ IsPosSemidef ρ₀ ∧ ρ₀.trace = 1) :
    Filter.Tendsto
      (fun t : ℝ => quantumSemigroup L t ρ₀)
      Filter.atTop
      (nhds (quantumDZTStationaryState L hDef)) := by
  have hPrim : IsPrimitive L := (deficiency_zero_iff_primitive L).mp hDef
  exact convergence_to_stationary L hPrim ρ₀ hρ₀

end DefectCRN.Quantum
