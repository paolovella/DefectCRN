/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.ChainComplex
import DefectCRN.Cohomology.Cycles
import DefectCRN.Cohomology.Deficiency
import DefectCRN.Cohomology.Obstruction
import DefectCRN.Cohomology.VariationalDuality
import DefectCRN.Cohomology.Examples.Triangle
import DefectCRN.Cohomology.Examples.MichaelisMenten
import DefectCRN.Cohomology.Examples.DeficiencyOne

/-!
# Cohomological Deficiency Theory

This module provides a cohomological interpretation of CRNT deficiency,
establishing that:

  **δ = dim(ker(Y) ∩ im(Bᵀ)) = dim(H¹)**

## Module Structure

* `ChainComplex` - The CRN chain complex: 0 → ℝᴱ →^{Bᵀ} ℝⱽ →^{Y} ℝˢ → 0
* `Cycles` - Cycle and coboundary spaces, DefectSpace = H¹
* `Deficiency` - THE MAIN THEOREM: δ = dim(DefectSpace)
* `Obstruction` - Physical interpretation of defect elements
* `VariationalDuality` - Connection to Onsager-Rayleigh framework

## Examples

* `Triangle` - 3-cycle, δ = 0, exact chain complex
* `MichaelisMenten` - Enzyme kinetics, δ = 0
* `DeficiencyOne` - Network with δ = 1, non-trivial DefectSpace

## Main Results

| Theorem | Description |
|---------|-------------|
| `deficiency_eq_dim_defect_space` | δ = dim(ker(Y) ∩ im(Bᵀ)) |
| `deficiency_zero_iff_exact` | δ = 0 ⟺ chain complex exact |
| `variational_cohomology_duality` | Onsager-Rayleigh ↔ cohomology |

## References

- Feinberg, M. (1972). Complex balancing in general kinetic systems.
- Horn, F. & Jackson, R. (1972). General mass action kinetics.
- Weibel, C. A. (1994). An Introduction to Homological Algebra.
-/
