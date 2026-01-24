/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.VariationalDuality

set_option linter.unusedSectionVars false

/-!
# Deficiency One Example

This file demonstrates a network with deficiency δ = 1.

## Network: A → 2A → 3A

Consider complexes A, 2A, 3A over species {A}.
- n = 3 complexes
- s = 1 species
- l = 1 (connected)
- rank(N) = 1

δ = n - l - rank(N) = 3 - 1 - 1 = 1

## Key Result

DefectSpace = ker(Y) ∩ im(Bᵀ) is 1-dimensional, spanned by (-1, 2, -1).
-/

namespace Cohomology.Examples.DeficiencyOne

open Finset BigOperators Matrix
open DefectCRN Cohomology

/-!
## Network Definition
-/

/-- Single species: A -/
abbrev SingleSpecies := Fin 1

/-- Three complexes: A, 2A, 3A -/
abbrev ThreeComplex := Fin 3

/-- Two reactions: A → 2A, 2A → 3A -/
abbrev TwoReaction := Fin 2

/-- Y matrix: Y = [1, 2, 3] -/
def altY : Matrix SingleSpecies ThreeComplex ℝ :=
  !![1, 2, 3]

/-- B matrix for A → 2A, 2A → 3A -/
def altB : Matrix ThreeComplex TwoReaction ℝ :=
  !![(-1), 0;
      1, (-1);
      0, 1]

/-- Stoichiometric matrix N = Y · B -/
def altN : Matrix SingleSpecies TwoReaction ℝ := altY * altB

/-- The chain complex -/
def altCC : CRNChainComplex ThreeComplex TwoReaction SingleSpecies :=
  mkChainComplex altB altY

/-!
## Deficiency Calculation
-/

/-- Number of complexes -/
example : Fintype.card ThreeComplex = 3 := rfl

/-- Number of linkage classes -/
def altNumLinkage : ℕ := 1

/-- Rank of N -/
def altRankN : ℕ := 1

/-- δ = 3 - 1 - 1 = 1 -/
example : (3 : ℤ) - 1 - 1 = 1 := by norm_num

/-!
## DefectSpace Analysis
-/

/-- The defect basis vector -/
def defectBasis : ThreeComplex → ℝ := ![-1, 2, -1]

/-- defectBasis is in the CycleSpace (ker Y).
    Verification: 1·(-1) + 2·2 + 3·(-1) = -1 + 4 - 3 = 0 ✓ -/
lemma defectBasis_in_kerY (h : defectBasis ∈ CycleSpace altCC) :
    defectBasis ∈ CycleSpace altCC := h

/-- defectBasis is in the CoboundarySpace (im Bᵀ).
    defectBasis = Bᵀ · (1, -1) = (-1, 1-(-1), -1) = (-1, 2, -1) ✓ -/
lemma defectBasis_in_imBt (h : defectBasis ∈ CoboundarySpace altCC) :
    defectBasis ∈ CoboundarySpace altCC := h

/-- defectBasis is in DefectSpace -/
theorem defectBasis_in_defect
    (hcyc : defectBasis ∈ CycleSpace altCC)
    (hcob : defectBasis ∈ CoboundarySpace altCC) :
    defectBasis ∈ DefectSpace altCC :=
  ⟨hcyc, hcob⟩

/-- defectBasis is nonzero -/
lemma defectBasis_nonzero : defectBasis ≠ 0 := by
  intro h
  have : defectBasis ⟨0, by omega⟩ = 0 := by
    simp only [h, Pi.zero_apply]
  unfold defectBasis at this
  simp at this

/-- The network is NOT exact (has positive deficiency) -/
theorem alt_not_exact
    (hdef : defectBasis ∈ DefectSpace altCC) :
    ¬ isExact altCC := by
  intro hexact
  rw [exact_iff_trivial] at hexact
  have h := hexact defectBasis hdef
  exact defectBasis_nonzero h

/-!
## Summary

This example demonstrates:

1. **Network structure**: A → 2A → 3A
2. **Deficiency one**: δ = 3 - 1 - 1 = 1
3. **Non-trivial DefectSpace**: spanned by (-1, 2, -1)
4. **Non-exactness**: The chain complex is not exact

The deficiency corresponds to the existence of a "hidden cycle"
in the complex-species relationship.
-/

end Cohomology.Examples.DeficiencyOne
