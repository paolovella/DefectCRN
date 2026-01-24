/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
-- Foundations: rigorous mathematical framework
import DefectCRN.Cohomology.Foundations.InnerProducts
import DefectCRN.Cohomology.Foundations.CochainComplex
import DefectCRN.Cohomology.Foundations.DeficiencySubspace

-- Main modules
import DefectCRN.Cohomology.ChainComplex
import DefectCRN.Cohomology.Cycles
import DefectCRN.Cohomology.Deficiency
import DefectCRN.Cohomology.Obstruction
import DefectCRN.Cohomology.VariationalDuality

-- Examples
import DefectCRN.Cohomology.Examples.Triangle
import DefectCRN.Cohomology.Examples.MichaelisMenten
import DefectCRN.Cohomology.Examples.DeficiencyOne

/-!
# Cohomological Deficiency Theory

This module provides a cohomological interpretation of CRNT deficiency,
establishing that:

  **δ = dim(DeficiencySubspace) = dim(ker(Y) ∩ im(Bᵀ))**

The DeficiencySubspace is ISOMORPHIC to H¹ of the kernel complex, which
justifies the name "cohomological deficiency theory". We use the term
"DeficiencySubspace" rather than "H¹" to maintain mathematical precision.

## Module Structure

### Foundations (v5.0)
* `Foundations/InnerProducts` - Correct W vs W⁻¹ inner product definitions
* `Foundations/CochainComplex` - Standard graph cochain complex
* `Foundations/DeficiencySubspace` - Core definition: ker(Y) ∩ im(Bᵀ)

### Main Modules
* `ChainComplex` - The CRN chain complex: 0 → ℝᴱ →^{Bᵀ} ℝⱽ →^{Y} ℝˢ → 0
* `Cycles` - Cycle and coboundary spaces, DefectSpace
* `Deficiency` - THE MAIN THEOREM: δ = dim(DeficiencySubspace)
* `Obstruction` - Physical interpretation (degrees of freedom, NOT obstruction)
* `VariationalDuality` - Connection to Onsager-Rayleigh framework

### Examples
* `Triangle` - 3-cycle, δ = 0, exact chain complex
* `MichaelisMenten` - Enzyme kinetics, δ = 0
* `DeficiencyOne` - Network with δ = 1, non-trivial DeficiencySubspace

## Main Results

| Theorem | Description |
|---------|-------------|
| `deficiency_eq_dim_defect_space` | δ = dim(ker(Y) ∩ im(Bᵀ)) |
| `deficiency_subspace_iso_H1` | DeficiencySubspace ≅ H¹(kernel complex) |
| `deficiency_zero_iff_exact` | δ = 0 ⟺ chain complex exact |
| `positive_deficiency_allows_equilibria` | δ > 0 compatible with existence |
| `variational_cohomology_duality` | Onsager-Rayleigh ↔ cohomology |

## Key Clarifications (v5.0)

1. **Terminology**: We use "DeficiencySubspace" not "H¹" directly
2. **Isomorphism**: `deficiency_subspace_iso_H1` provides the connection
3. **Physical meaning**: Deficiency measures degrees of freedom, NOT obstruction
4. **Hodge orthogonality**: W-inner product vs W⁻¹-inner product clarified

## References

- Feinberg, M. (1972). Complex balancing in general kinetic systems.
- Horn, F. & Jackson, R. (1972). General mass action kinetics.
- Feinberg, M. (1995). Existence and uniqueness of steady states.
- Weibel, C. A. (1994). An Introduction to Homological Algebra.
-/
