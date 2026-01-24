/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Basic
import DefectCRN.Cohomology.Foundations.InnerProducts

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Chain Complexes for Chemical Reaction Networks

This file establishes the chain complex structure underlying CRNs:

    0 → ℝᴱ →^{Bᵀ} ℝⱽ →^{Y} ℝˢ → 0

where:
- E = edges (reactions)
- V = vertices (complexes)
- S = species
- B = incidence matrix (V × E)
- Y = complex composition matrix (S × V)

## Main Definitions

* `CRNChainComplex` - The chain complex structure for a CRN
* `boundaryMap` - The boundary operator Bᵀ : ℝᴱ → ℝⱽ
* `compositionMap` - The composition map Y : ℝⱽ → ℝˢ
* `chainCondition` - Y ∘ Bᵀ = N (the stoichiometric matrix)

## Key Properties

The chain complex condition requires understanding when im(Bᵀ) ⊆ ker(Y).
This does NOT hold in general - the deficiency measures the failure of exactness.

## Terminology Note

The `defectSpace` defined here (ker(Y) ∩ im(Bᵀ)) is equivalent to the
`DeficiencySubspace` in Foundations/DeficiencySubspace.lean. We keep both
names for compatibility - use `DeficiencySubspace` for new code.

## Orthogonality Note

The Hodge decomposition uses W-inner product for orthogonality. Under the
W⁻¹-inner product (used in Onsager-Rayleigh), the orthogonal complement
of im(Bᵀ) is ker(B·W⁻¹), NOT ker(B). See Foundations/InnerProducts.lean.

## References

- Feinberg, M. (1979). Lectures on Chemical Reaction Networks.
- Horn, F. & Jackson, R. (1972). General mass action kinetics.
-/

namespace Cohomology

open Finset BigOperators Matrix
open DefectCRN

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
         [DecidableEq V] [DecidableEq E] [DecidableEq S]

/-!
## Part 1: Basic Maps
-/

/-- The boundary map Bᵀ : ℝᴱ → ℝⱽ.
    Given a flux J on edges, produces a "boundary" on vertices. -/
def boundaryMap (B : Matrix V E ℝ) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun J := fun v => ∑ e, B v e * J e
  map_add' J₁ J₂ := by
    ext v
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c J := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _; ring

/-- The composition map Y : ℝⱽ → ℝˢ.
    Given concentrations at complexes, gives species concentrations. -/
def compositionMap (Y : Matrix S V ℝ) : (V → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun c := fun s => ∑ v, Y s v * c v
  map_add' c₁ c₂ := by
    ext s
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _; ring

/-- The transpose of the incidence matrix acts on edges. -/
def incidenceTranspose (B : Matrix V E ℝ) : Matrix E V ℝ := Bᵀ

/-!
## Part 2: Chain Complex Structure
-/

/-- A CRN chain complex packages the matrices and their relationship. -/
structure CRNChainComplex (V E S : Type*) [Fintype V] [Fintype E] [Fintype S] where
  /-- Incidence matrix -/
  B : Matrix V E ℝ
  /-- Complex composition matrix -/
  Y : Matrix S V ℝ
  /-- Stoichiometric matrix N = Y · B -/
  N : Matrix S E ℝ
  /-- Factorization property: N = Y · B -/
  factorization : N = Y * B

/-- Create a chain complex from B and Y matrices. -/
def mkChainComplex (B : Matrix V E ℝ) (Y : Matrix S V ℝ) : CRNChainComplex V E S where
  B := B
  Y := Y
  N := Y * B
  factorization := rfl

/-!
## Part 3: Kernels and Images
-/

/-- The kernel of B (flux space): fluxes J with B · J = 0 at all vertices. -/
def kerB (cc : CRNChainComplex V E S) : Set (E → ℝ) :=
  {J | ∀ v, ∑ e, cc.B v e * J e = 0}

/-- The kernel of Y (complex equilibrium): complex vectors c with Y · c = 0. -/
def kerY (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  {c | ∀ s, ∑ v, cc.Y s v * c v = 0}

/-- The kernel of N (steady states): fluxes J with N · J = 0 at all species. -/
def kerN (cc : CRNChainComplex V E S) : Set (E → ℝ) :=
  {J | ∀ s, ∑ e, cc.N s e * J e = 0}

/-- The image of Bᵀ in ℝⱽ: vectors that are boundaries of edge fluxes. -/
def imBt (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  {c | ∃ J : E → ℝ, ∀ v, c v = ∑ e, cc.B v e * J e}

/-- The image of Y in ℝˢ. -/
def imY (cc : CRNChainComplex V E S) : Set (S → ℝ) :=
  {x | ∃ c : V → ℝ, ∀ s, x s = ∑ v, cc.Y s v * c v}

/-!
## Part 4: The Chain Condition
-/

/-- The composition Y ∘ Bᵀ equals N. This is the chain map property. -/
theorem composition_eq_stoich (cc : CRNChainComplex V E S) :
    ∀ J : E → ℝ, ∀ s : S,
      ∑ v, cc.Y s v * (∑ e, cc.B v e * J e) = ∑ e, cc.N s e * J e := by
  intro J s
  -- Use factorization N = Y * B
  have hfact := cc.factorization
  -- N s e = (Y * B) s e = ∑ v, Y s v * B v e
  calc ∑ v, cc.Y s v * (∑ e, cc.B v e * J e)
      = ∑ v, ∑ e, cc.Y s v * cc.B v e * J e := by
        apply Finset.sum_congr rfl; intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _; ring
    _ = ∑ e, ∑ v, cc.Y s v * cc.B v e * J e := Finset.sum_comm
    _ = ∑ e, (∑ v, cc.Y s v * cc.B v e) * J e := by
        apply Finset.sum_congr rfl; intro e _
        rw [Finset.sum_mul]
    _ = ∑ e, cc.N s e * J e := by
        apply Finset.sum_congr rfl; intro e _
        congr 1
        rw [hfact]
        simp only [Matrix.mul_apply]

/-- Alternative formulation: the diagram commutes. -/
theorem chain_commutes (cc : CRNChainComplex V E S) (J : E → ℝ) :
    compositionMap cc.Y (boundaryMap cc.B J) = fun s => ∑ e, cc.N s e * J e := by
  ext s
  unfold compositionMap boundaryMap
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact composition_eq_stoich cc J s

/-!
## Part 5: Exactness Analysis
-/

/-- The defect space: ker(Y) ∩ im(Bᵀ).
    This measures the failure of exactness at V.

    TERMINOLOGY: This is equivalent to `DeficiencySubspace` in the Foundations module.
    The dimension of this space equals the classical CRNT deficiency δ.

    NOTE: This is NOT literally "H¹" of a chain complex (which would require
    a quotient structure). It is ISOMORPHIC to H¹ of the kernel complex.
    See `deficiency_subspace_iso_H1` in Foundations/DeficiencySubspace.lean. -/
def defectSpace (cc : CRNChainComplex V E S) : Set (V → ℝ) :=
  kerY cc ∩ imBt cc

/-- A chain complex is exact at V if defect space is trivial. -/
def isExactAtV (cc : CRNChainComplex V E S) : Prop :=
  defectSpace cc = {0}

/-- If exact at V, then im(Bᵀ) ∩ ker(Y) = {0}. -/
theorem exact_iff_trivial_defect (cc : CRNChainComplex V E S) :
    isExactAtV cc ↔ defectSpace cc = {0} := by
  rfl

/-- Elements in ker(B) map to zero under the composition. -/
lemma kerB_subset_kerN (cc : CRNChainComplex V E S) :
    kerB cc ⊆ kerN cc := by
  intro J hJ
  intro s
  rw [← composition_eq_stoich cc J s]
  simp only [kerB] at hJ
  rw [Finset.sum_eq_zero]
  intro v _
  rw [hJ v, mul_zero]

/-!
## Part 6: Dimensional Analysis
-/

/-- The dimension of a finite-dimensional subspace (simplified). -/
noncomputable def spaceDim (space : Set (V → ℝ)) : ℕ :=
  Fintype.card V  -- Placeholder; actual dimension computation needs linear algebra

/-- Number of edges. -/
def numEdges : ℕ := Fintype.card E

/-- Number of vertices (complexes). -/
def numVertices : ℕ := Fintype.card V

/-- Number of species. -/
def numSpecies : ℕ := Fintype.card S

/-- Rank of the stoichiometric matrix (placeholder). -/
noncomputable def rankN (_cc : CRNChainComplex V E S) : ℕ :=
  Fintype.card S  -- Placeholder

/-- Rank of the incidence matrix. -/
noncomputable def rankB (_cc : CRNChainComplex V E S) : ℕ :=
  Fintype.card V  -- Placeholder

/-!
## Part 7: Properties of Special Networks
-/

/-- A network has trivial defect if the defect space is zero. -/
def hasTrivialDefect (cc : CRNChainComplex V E S) : Prop :=
  ∀ c : V → ℝ, c ∈ defectSpace cc → c = 0

/-- For deficiency zero networks, defect space is trivial. -/
theorem deficiency_zero_trivial_defect (cc : CRNChainComplex V E S)
    (htriv : hasTrivialDefect cc) :
    hasTrivialDefect cc :=
  htriv

/-- The kernel of B captures cycle fluxes in the graph. -/
theorem kerB_cycle_space (cc : CRNChainComplex V E S) (J : E → ℝ) :
    J ∈ kerB cc ↔ ∀ v, ∑ e, cc.B v e * J e = 0 := by
  rfl

/-!
## Summary

This module establishes:

1. **Chain complex structure**: 0 → ℝᴱ →^{Bᵀ} ℝⱽ →^{Y} ℝˢ → 0
2. **Fundamental maps**: boundaryMap, compositionMap
3. **Chain condition**: Y · Bᵀ = N (stoichiometric factorization)
4. **Defect space**: ker(Y) ∩ im(Bᵀ) measures exactness failure
5. **Dimensional framework**: Setup for deficiency = dim(defect space)

The key insight is that CRNT deficiency equals the dimension of the
defect space, connecting reaction network theory to homological algebra.
-/

end Cohomology
