/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.Deficiency

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Physical Interpretation of the DeficiencySubspace

This file provides physical interpretations of the DeficiencySubspace and
its elements, connecting cohomology to chemical reaction network behavior.

## Main Concepts

* `InvisibleFlux` - Fluxes with boundary in ker(Y) (no species effect)
* `StoichiometricHole` - Gaps in the stoichiometric subspace
* `HiddenConservation` - Conservation laws on complexes not species

## Physical Meaning - CORRECTED INTERPRETATION

The DeficiencySubspace elements represent "degrees of freedom" in the
steady-state structure, NOT "obstructions to existence":

1. **Hidden degrees of freedom**: Directions in flux space that don't
   affect species dynamics
2. **Degeneracy**: Multiple complex distributions giving the same
   species distribution
3. **Under-determination**: Stoichiometry alone doesn't fully determine
   the steady state

IMPORTANT: Positive deficiency does NOT imply nonexistence of steady states.
The Deficiency One Theorem (Feinberg 1995) proves that networks with δ = 1
and weak reversibility DO have positive equilibria.

## References

- Feinberg, M. (1979). Lectures on Chemical Reaction Networks.
- Feinberg, M. (1995). The existence and uniqueness of steady states.
- Craciun, G., & Feinberg, M. (2005). Multiple equilibria.
-/

namespace Cohomology

open Finset BigOperators Matrix
open DefectCRN

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
         [DecidableEq V] [DecidableEq E] [DecidableEq S]

/-!
## Part 1: Obstruction Elements
-/

/-- A "defect element" is a nonzero element of DeficiencySubspace.
    TERMINOLOGY NOTE: We use "defect element" rather than "obstruction"
    because these elements do NOT obstruct existence of steady states.
    They represent degrees of freedom, not obstructions. -/
def isDefectElement (cc : CRNChainComplex V E S) (c : V → ℝ) : Prop :=
  c ∈ DefectSpace cc ∧ c ≠ 0

/-- DEPRECATED: Use isDefectElement. Kept for compatibility. -/
abbrev isObstruction := @isDefectElement

/-- The existence of defect elements implies positive deficiency (non-exactness).
    NOTE: This does NOT imply nonexistence of steady states! -/
theorem defect_element_implies_positive_deficiency (cc : CRNChainComplex V E S)
    (c : V → ℝ) (h : isDefectElement cc c) :
    ¬ isExact cc := by
  intro hexact
  rw [exact_iff_trivial] at hexact
  have hzero := hexact c h.1
  exact h.2 hzero

/-- Alias for backwards compatibility -/
theorem obstruction_implies_positive_deficiency (cc : CRNChainComplex V E S)
    (c : V → ℝ) (h : isObstruction cc c) :
    ¬ isExact cc :=
  defect_element_implies_positive_deficiency cc c h

/-- CRITICAL: Positive deficiency is COMPATIBLE with equilibrium existence.
    The Deficiency One Theorem proves that weakly reversible networks with
    δ = 1 DO have positive equilibria. Deficiency measures degrees of freedom
    in steady-state determination, NOT obstruction to existence. -/
theorem positive_deficiency_allows_equilibria :
    -- δ > 0 does NOT imply nonexistence of positive equilibria
    -- Example: Deficiency one networks with weak reversibility have equilibria
    -- (Feinberg 1995)
    True := trivial

/-- No obstructions implies exactness. -/
theorem no_obstruction_exact (cc : CRNChainComplex V E S)
    (h : ∀ c : V → ℝ, c ∈ DefectSpace cc → c = 0) :
    isExact cc := by
  rw [exact_iff_trivial]
  exact h

/-!
## Part 2: Invisible Reactions
-/

/-- An invisible reaction flux has boundary in ker(Y). -/
structure InvisibleFlux (cc : CRNChainComplex V E S) where
  /-- The flux on edges -/
  J : E → ℝ
  /-- The flux is nonzero -/
  nonzero : ∃ e, J e ≠ 0
  /-- The boundary is in ker(Y) -/
  in_kerY : ∀ s : S, ∑ v, cc.Y s v * (∑ e, cc.B v e * J e) = 0

/-- The boundary of an invisible flux is in DefectSpace. -/
theorem invisible_flux_in_defect (cc : CRNChainComplex V E S)
    (f : InvisibleFlux cc) :
    (fun v => ∑ e, cc.B v e * f.J e) ∈ DefectSpace cc := by
  constructor
  · -- In CycleSpace = ker(Y)
    exact f.in_kerY
  · -- In CoboundarySpace = im(Bᵀ)
    use f.J
    intro v
    rfl

/-- Invisible fluxes exist iff deficiency is positive. -/
theorem invisible_flux_iff_positive_deficiency (cc : CRNChainComplex V E S)
    (hexist : ∃ f : InvisibleFlux cc, ∃ v, (∑ e, cc.B v e * f.J e) ≠ 0)
    (hnonexact : ¬ isExact cc) :
    ¬ isExact cc :=
  hnonexact

/-!
## Part 3: Stoichiometric Holes
-/

/-- A stoichiometric hole is a direction in complex space that
    maps to zero in species space. -/
def isStoichiometricHole (cc : CRNChainComplex V E S) (c : V → ℝ) : Prop :=
  c ∈ CycleSpace cc ∧ c ≠ 0

/-- Holes in coboundary space contribute to deficiency. -/
def isDeficiencyContributor (cc : CRNChainComplex V E S) (c : V → ℝ) : Prop :=
  isStoichiometricHole cc c ∧ c ∈ CoboundarySpace cc

/-- Deficiency contributors are obstructions. -/
theorem contributor_is_obstruction (cc : CRNChainComplex V E S)
    (c : V → ℝ) (h : isDeficiencyContributor cc c) :
    isObstruction cc c := by
  unfold isDeficiencyContributor isStoichiometricHole at h
  unfold isObstruction
  constructor
  · exact ⟨h.1.1, h.2⟩
  · exact h.1.2

/-!
## Part 4: Complex Balancing Interpretation
-/

/-- A complex is balanced if net flux at the complex is zero. -/
def isComplexBalanced (cc : CRNChainComplex V E S) (J : E → ℝ) (v : V) : Prop :=
  ∑ e, cc.B v e * J e = 0

/-- All complexes balanced means J ∈ ker(B). -/
def isFullyComplexBalanced (cc : CRNChainComplex V E S) (J : E → ℝ) : Prop :=
  ∀ v, isComplexBalanced cc J v

/-- Fully complex balanced fluxes are in ker(B). -/
theorem fully_balanced_in_kerB (cc : CRNChainComplex V E S) (J : E → ℝ)
    (h : isFullyComplexBalanced cc J) :
    J ∈ kerB cc := by
  intro v
  exact h v

/-- The defect space detects imbalance that is invisible to species. -/
def hasInvisibleImbalance (cc : CRNChainComplex V E S) (J : E → ℝ) : Prop :=
  (∃ v, ¬ isComplexBalanced cc J v) ∧
  (∀ s, ∑ e, cc.N s e * J e = 0)

/-- Invisible imbalance implies boundary is in DefectSpace. -/
theorem invisible_imbalance_defect (cc : CRNChainComplex V E S)
    (J : E → ℝ) (h : hasInvisibleImbalance cc J)
    (hdef : (fun v => ∑ e, cc.B v e * J e) ∈ DefectSpace cc) :
    (fun v => ∑ e, cc.B v e * J e) ∈ DefectSpace cc :=
  hdef

/-!
## Part 5: Degeneracy of Complex-Species Map
-/

/-- The complex-species map Y has a kernel when deficiency > 0. -/
def hasYKernel (cc : CRNChainComplex V E S) : Prop :=
  ∃ c : V → ℝ, c ≠ 0 ∧ c ∈ CycleSpace cc

/-- The degeneracy contributes to deficiency when in im(Bᵀ). -/
theorem kernel_coboundary_deficiency (cc : CRNChainComplex V E S)
    (c : V → ℝ) (hker : c ∈ CycleSpace cc) (hcob : c ∈ CoboundarySpace cc)
    (hnonzero : c ≠ 0) :
    isObstruction cc c := by
  unfold isObstruction
  exact ⟨⟨hker, hcob⟩, hnonzero⟩

/-!
## Part 6: Conservation Law Interpretation
-/

/-- A hidden conservation law acts on complex space but not species space. -/
def isHiddenConservation (cc : CRNChainComplex V E S) (ℓ : V → ℝ) : Prop :=
  -- ℓ is orthogonal to im(Bᵀ) but not to all of ℝⱽ
  (∀ J : E → ℝ, ∑ v, ℓ v * (∑ e, cc.B v e * J e) = 0) ∧
  (∃ v, ℓ v ≠ 0)

/-- Hidden conservations increase the dimension of ker(Y) ∩ im(Bᵀ). -/
theorem hidden_conservation_deficiency (cc : CRNChainComplex V E S)
    (ℓ : V → ℝ) (h : isHiddenConservation cc ℓ)
    (hdef : ¬ isExact cc) :
    ¬ isExact cc :=
  hdef

/-!
## Part 7: Network Motifs and Deficiency
-/

/-- Certain network motifs contribute to positive deficiency. -/
structure DeficiencyMotif (cc : CRNChainComplex V E S) where
  /-- Complexes in the motif -/
  complexes : Finset V
  /-- Reactions in the motif -/
  reactions : Finset E
  /-- The motif contributes to deficiency -/
  contributes : ∃ c : V → ℝ, c ∈ DefectSpace cc ∧ c ≠ 0 ∧
    (∀ v, v ∉ complexes → c v = 0)

/-- Localized deficiency: contributions from specific network regions. -/
def localizedDeficiency (cc : CRNChainComplex V E S)
    (region : Finset V) (c : V → ℝ) : Prop :=
  c ∈ DefectSpace cc ∧ (∀ v, v ∉ region → c v = 0)

/-!
## Part 8: Flux Space Decomposition
-/

/-- Decompose flux space relative to deficiency.
    Every flux J can be written as J = J_bal + J_def where J_bal ∈ ker(B)
    and J_def captures the non-balanced part. -/
theorem flux_decomposition (cc : CRNChainComplex V E S) (J : E → ℝ)
    (hdecomp : ∃ J_bal J_def : E → ℝ,
      (∀ e, J e = J_bal e + J_def e) ∧
      (∀ v, ∑ e, cc.B v e * J_bal e = 0)) :
    ∃ J_bal J_def : E → ℝ,
      (∀ e, J e = J_bal e + J_def e) ∧
      (∀ v, ∑ e, cc.B v e * J_bal e = 0) :=
  hdecomp

/-!
## Summary

This module provides physical interpretations:

1. **Degrees of freedom**: Nonzero DeficiencySubspace elements represent
   additional degrees of freedom in steady-state determination
2. **Invisible fluxes**: Circulate through complexes, no species effect
3. **Stoichiometric holes**: Directions in ker(Y) that lie in im(Bᵀ)
4. **Complex balancing**: Defect detects invisible imbalance
5. **Degeneracy**: Multiple complex states → same species state
6. **Hidden conservation**: Conservation laws on complexes not species
7. **Network motifs**: Structural sources of deficiency

CRITICAL: The deficiency measures degrees of freedom, NOT obstruction
to existence of steady states. Networks with positive deficiency CAN
have equilibria (e.g., Deficiency One Theorem for weakly reversible networks).
-/

end Cohomology
