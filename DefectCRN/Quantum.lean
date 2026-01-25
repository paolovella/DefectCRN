/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Basic
import DefectCRN.Quantum.Lindbladian
import DefectCRN.Quantum.StationaryState
import DefectCRN.Quantum.Algebra
import DefectCRN.Quantum.Irreducibility
import DefectCRN.Quantum.Deficiency
import DefectCRN.Quantum.StructuralDeficiency
import DefectCRN.Quantum.Frigerio
import DefectCRN.Quantum.QuantumDZT
import DefectCRN.Quantum.Examples.TwoLevel
import DefectCRN.Quantum.Examples.AccidentalSymmetry

/-!
# Quantum Chemical Reaction Network Theory

This module extends classical Chemical Reaction Network Theory to quantum systems
using Lindblad master equations.

## Overview

The Lindblad master equation describes the most general form of Markovian dynamics
for open quantum systems:

  dρ/dt = L(ρ) = -i[H, ρ] + Σₖ (Lₖ ρ Lₖ† - ½{Lₖ†Lₖ, ρ})

This is the quantum analog of the classical master equation for chemical kinetics.

## Main Files

* `Basic.lean` - Fundamental definitions (commutator, anticommutator, dagger)
* `Lindbladian.lean` - The Lindblad generator structure
* `StationaryState.lean` - Stationary states and their properties
* `Algebra.lean` - Lindblad algebra and commutant
* `Irreducibility.lean` - Ergodic/irreducible semigroups
* `Deficiency.lean` - Quantum deficiency δ_Q
* `StructuralDeficiency.lean` - Structural deficiency δ_Q^struct (parameter-independent)
* `Frigerio.lean` - Frigerio's uniqueness theorem
* `QuantumDZT.lean` - **Quantum Deficiency Zero Theorem** (main contribution)

## Main Results

1. **Frigerio's Theorem:** Ergodic ⟹ unique stationary state
2. **Quantum DZT:** δ_Q = 0 ⟹ unique stationary state (faithful under QDB)
3. **Equivalence:** δ_Q = 0 ⟺ ergodic ⟺ trivial commutant
4. **Structural Formula:** δ_Q^struct(G) = k - 1 (k = number of SCCs)

## Examples

* `TwoLevel.lean` - Two-level system with spontaneous decay (ergodic, δ_Q = 0)
* `AccidentalSymmetry.lean` - Aligned operators creating hidden symmetry (δ_Q = 1 > δ_Q^struct = 0)

## References

* Lindblad, G. "On the generators of quantum dynamical semigroups" (1976)
* Frigerio, A. "Stationary states of quantum dynamical semigroups" (1978)
* Spohn, H. "Entropy production for quantum dynamical semigroups" (1978)

## Novelty

The **Quantum Deficiency Zero Theorem** is a new contribution that connects:
- Classical CRNT deficiency theory (Horn-Jackson-Feinberg)
- Quantum dynamical semigroup theory (Lindblad-Gorini-Kossakowski-Sudarshan)
- Algebraic characterization (Evans-Frigerio commutant theory)
-/
