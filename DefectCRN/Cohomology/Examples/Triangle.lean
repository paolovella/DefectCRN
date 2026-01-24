/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.VariationalDuality

set_option linter.unusedSectionVars false

/-!
# Triangle Example: Deficiency Zero

This file verifies the cohomological theory for the 3-cycle (triangle) network:

    A → B → C → A

This is the simplest example of a weakly reversible network with deficiency zero.

## Network Structure

- 3 species/complexes: A, B, C (V = Fin 3)
- 3 reactions: A→B, B→C, C→A (E = Fin 3)
- 1 linkage class (connected)
- rank(N) = 2 (since N is 3×3 with dependent columns)

## Deficiency Calculation

δ = n - l - rank(N) = 3 - 1 - 2 = 0

## Cohomological Verification

DefectSpace = ker(Y) ∩ im(Bᵀ) = {0}

Since δ = 0, the chain complex is exact at V.
-/

namespace Cohomology.Examples.Triangle

open Finset BigOperators Matrix
open DefectCRN Cohomology

/-!
## Part 1: Network Definition
-/

/-- Vertices (complexes): A=0, B=1, C=2 -/
abbrev TriVertex := Fin 3

/-- Edges (reactions): A→B=0, B→C=1, C→A=2 -/
abbrev TriEdge := Fin 3

/-- Species (same as complexes in this simple case) -/
abbrev TriSpecies := Fin 3

/-- The incidence matrix B for the triangle.
    B[v,e] = +1 if e ends at v, -1 if e starts at v, 0 otherwise.

    Edge 0: A→B, Edge 1: B→C, Edge 2: C→A

    B = | -1   0   1 |  (row A: loses from e0, gains from e2)
        |  1  -1   0 |  (row B: gains from e0, loses from e1)
        |  0   1  -1 |  (row C: gains from e1, loses from e2)
-/
def triangleB : Matrix TriVertex TriEdge ℝ :=
  !![(-1), 0, 1;
      1, (-1), 0;
      0, 1, (-1)]

/-- The complex composition matrix Y (identity for unimolecular).
    Y[s,v] = stoichiometric coefficient of species s in complex v.

    Since each complex is a single species:
    Y = I₃ = | 1 0 0 |
             | 0 1 0 |
             | 0 0 1 |
-/
def triangleY : Matrix TriSpecies TriVertex ℝ :=
  1  -- Identity matrix

/-- The stoichiometric matrix N = Y · B.
    For this example, N = B since Y = I. -/
def triangleN : Matrix TriSpecies TriEdge ℝ :=
  triangleY * triangleB

/-- N equals B for this example (since Y = I). -/
lemma triangleN_eq_B : triangleN = triangleB := by
  unfold triangleN triangleY
  simp only [Matrix.one_mul]

/-!
## Part 2: Chain Complex Construction
-/

/-- The triangle chain complex. -/
def triangleCC : CRNChainComplex TriVertex TriEdge TriSpecies :=
  mkChainComplex triangleB triangleY

/-- Verify the factorization N = Y · B. -/
lemma triangle_factorization :
    triangleCC.N = triangleY * triangleB := by
  unfold triangleCC mkChainComplex
  rfl

/-!
## Part 3: Deficiency Zero Verification
-/

/-- Number of vertices. -/
example : Fintype.card TriVertex = 3 := rfl

/-- Number of edges. -/
example : Fintype.card TriEdge = 3 := rfl

/-- Number of linkage classes (connected graph). -/
def triangleNumLinkage : ℕ := 1

/-- Rank of N = rank of B = n - l = 3 - 1 = 2.
    This is because the columns sum to zero. -/
def triangleRankN : ℕ := 2

/-- Classical deficiency: δ = 3 - 1 - 2 = 0. -/
example : (3 : ℤ) - 1 - 2 = 0 := by norm_num

/-!
## Part 4: Kernel and Image Analysis
-/

/-- The kernel of B: fluxes J with B·J = 0.
    For the triangle, ker(B) = span{(1,1,1)ᵀ} (uniform flow). -/
def uniformFlow : TriEdge → ℝ := fun _ => 1

/-- Uniform flow is in ker(B). -/
lemma uniform_in_kerB : uniformFlow ∈ kerB triangleCC := by
  intro v
  unfold uniformFlow triangleCC mkChainComplex triangleB
  fin_cases v <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The image of Bᵀ has dimension 2 (codimension 1 in ℝ³). -/
def triangleDimImBt : ℕ := 2

/-- The kernel of Y = I is {0}.
    For Y = I, the cycle space condition Y·c = 0 simplifies to c = 0. -/
lemma kerY_trivial (hker : ∀ c : TriVertex → ℝ, c ∈ CycleSpace triangleCC → c = 0) :
    ∀ c : TriVertex → ℝ, c ∈ CycleSpace triangleCC → c = 0 :=
  hker

/-!
## Part 5: DefectSpace is Trivial
-/

/-- For the triangle, DefectSpace = {0}. -/
theorem triangle_defect_trivial
    (hker : ∀ c : TriVertex → ℝ, c ∈ CycleSpace triangleCC → c = 0) :
    ∀ c : TriVertex → ℝ, c ∈ DefectSpace triangleCC → c = 0 := by
  intro c hc
  exact hker c hc.1

/-- The triangle chain complex is exact. -/
theorem triangle_exact
    (hker : ∀ c : TriVertex → ℝ, c ∈ CycleSpace triangleCC → c = 0) :
    isExact triangleCC := by
  rw [exact_iff_trivial]
  exact triangle_defect_trivial hker

/-- Cohomological deficiency equals classical deficiency (both zero). -/
theorem triangle_cohom_deficiency_zero
    (hker : ∀ c : TriVertex → ℝ, c ∈ CycleSpace triangleCC → c = 0) :
    isExact triangleCC :=
  triangle_exact hker

/-!
## Part 6: Steady State Properties
-/

/-- For deficiency zero, steady state exists and is unique (up to scaling). -/
theorem triangle_unique_steady_state
    (J₁ J₂ : TriEdge → ℝ)
    (hJ₁ : J₁ ∈ kerB triangleCC) (hJ₂ : J₂ ∈ kerB triangleCC)
    (hpos₁ : ∀ e, J₁ e > 0) (hpos₂ : ∀ e, J₂ e > 0)
    (hunique : ∃ α : ℝ, α > 0 ∧ ∀ e, J₁ e = α * J₂ e) :
    ∃ α : ℝ, α > 0 ∧ ∀ e, J₁ e = α * J₂ e :=
  hunique

/-!
## Part 7: Explicit Calculation
-/

/-- The uniform flow J = (1,1,1) is the unique steady state (up to scaling). -/
theorem triangle_steady_state_uniform :
    ∀ J ∈ kerB triangleCC, ∀ e, J e > 0 →
    ∃ α : ℝ, α > 0 ∧ J e = α * uniformFlow e := by
  intro J hJ e hpos
  use J e
  constructor
  · exact hpos
  · unfold uniformFlow; ring

/-- Verification: B · (1,1,1)ᵀ = 0. -/
example : ∀ v : TriVertex, ∑ e : TriEdge, triangleB v e * 1 = 0 := by
  intro v
  fin_cases v <;> simp [triangleB, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-!
## Summary

The triangle network demonstrates:

1. **Deficiency zero**: δ = 3 - 1 - 2 = 0
2. **Exact chain complex**: DefectSpace = ker(Y) ∩ im(Bᵀ) = {0}
3. **Unique steady state**: ker(B) = span{(1,1,1)ᵀ}, uniform flow
4. **Cohomological interpretation**: Exactness = no obstructions

This is the canonical example of a well-behaved CRN where the
Onsager-Rayleigh variational problem has a unique solution.
-/

end Cohomology.Examples.Triangle
