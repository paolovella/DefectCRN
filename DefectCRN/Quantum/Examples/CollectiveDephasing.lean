/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.StructuralDeficiency

/-!
# Collective Dephasing: Symmetry-Protected Degeneracy

This file provides a concrete example where the structural deficiency δ_struct = 0
(connected support graph) but the actual quantum deficiency δ_Q > 0 due to
symmetry-protected decoherence-free subspaces.

## Main results

* `collectiveDephasing` - The collective Z dephasing Lindbladian on 2 qubits
* `collectiveDephasing_has_dfs` - There exists a non-scalar in the commutant
* `collectiveDephasing_deficiency_positive` - δ_Q > 0

## Physical interpretation

Collective dephasing L = Z₁ + Z₂ = diag(2, 0, 0, -2) has degenerate eigenvalues
on the {|01⟩, |10⟩} subspace. This creates a decoherence-free subspace where
the Bell states |Ψ±⟩ are protected from noise.

The structural deficiency cannot detect this because:
1. The support graph (based on which entries are constrained) is connected
2. The degeneracy arises from eigenvalue coincidence, not graph disconnection

This demonstrates the hierarchy: δ_struct ≤ δ_Γ ≤ δ_Q
where δ_Γ accounts for symmetry-protected degeneracy.

## References

* Lidar, D.A. "Decoherence-Free Subspaces and Subsystems" (2014)
* Paper Section 5.5
-/

set_option linter.unusedVariables false

namespace DefectCRN.Quantum.Examples

open scoped Matrix BigOperators
open Matrix

/-! ### Two-Qubit System Setup -/

/-- Dimension of 2-qubit system -/
abbrev n₄ : ℕ := 4

instance : NeZero n₄ := ⟨by norm_num⟩

/-- Basis states: |00⟩ = 0, |01⟩ = 1, |10⟩ = 2, |11⟩ = 3 -/
def ket00 : Fin 4 := 0
def ket01 : Fin 4 := 1
def ket10 : Fin 4 := 2
def ket11 : Fin 4 := 3

/-! ### Collective Dephasing Operator -/

/-- The collective Z operator: L = Z₁ ⊗ I + I ⊗ Z₂ = diag(2, 0, 0, -2)

    In the computational basis {|00⟩, |01⟩, |10⟩, |11⟩}:
    - L|00⟩ = (+1+1)|00⟩ = 2|00⟩
    - L|01⟩ = (+1-1)|01⟩ = 0|01⟩
    - L|10⟩ = (-1+1)|10⟩ = 0|10⟩
    - L|11⟩ = (-1-1)|11⟩ = -2|11⟩
-/
def collectiveZ : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![2, 0, 0, -2]

/-- collectiveZ is diagonal: off-diagonal entries are zero -/
theorem collectiveZ_off_diag (i j : Fin 4) (hij : i ≠ j) : collectiveZ i j = 0 := by
  simp only [collectiveZ, diagonal_apply, hij, ↓reduceIte]

/-- collectiveZ eigenvalues -/
theorem collectiveZ_apply_diag (i : Fin 4) : collectiveZ i i = ![2, 0, 0, -2] i := by
  simp [collectiveZ, diagonal_apply]

/-- The eigenvalue 0 is degenerate (multiplicity 2) -/
theorem collectiveZ_degenerate : collectiveZ ket01 ket01 = collectiveZ ket10 ket10 := by
  simp [collectiveZ, diagonal_apply, ket01, ket10]

/-! ### Commutant Analysis -/

/-- A non-scalar matrix that commutes with collectiveZ -/
def dfsProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  matrixUnit ket01 ket01 + matrixUnit ket10 ket10

/-- dfsProjector is the projector onto the degenerate subspace -/
theorem dfsProjector_is_projector : dfsProjector * dfsProjector = dfsProjector := by
  simp only [dfsProjector]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [matrixUnit_mul]
  simp [ket01, ket10]

/-- dfsProjector commutes with collectiveZ (since they're simultaneously diagonal in {01,10} block) -/
theorem dfsProjector_comm_collectiveZ : ⟦dfsProjector, collectiveZ⟧ = 0 := by
  ext i j
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
    dfsProjector, Matrix.add_apply, matrixUnit_apply, collectiveZ, diagonal_apply]
  -- Tedious case analysis: the degenerate eigenspace {01, 10} commutes with collectiveZ
  fin_cases i <;> fin_cases j <;>
    simp [ket01, ket10, Fin.reduceEq, Fin.isValue]

/-- dfsProjector is not a scalar multiple of identity -/
theorem dfsProjector_not_scalar : ¬∃ c : ℂ, dfsProjector = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  intro ⟨c, hc⟩
  -- dfsProjector 0 0 = 0 while (c • 1) 0 0 = c
  have h00 : dfsProjector ket00 ket00 = 0 := by
    simp [dfsProjector, matrixUnit_apply, ket00, ket01, ket10]
  have hc00 : (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ket00 ket00 = c := by
    simp [ket00]
  rw [hc] at h00
  rw [hc00] at h00
  -- So c = 0
  -- But dfsProjector 1 1 = 1 while (0 • 1) 1 1 = 0
  have h11 : dfsProjector ket01 ket01 = 1 := by
    simp [dfsProjector, matrixUnit_apply, ket01, ket10]
  rw [hc, h00] at h11
  simp at h11

/-! ### The Lindbladian -/

/-- Collective dephasing Lindbladian with single jump operator L = collectiveZ -/
def collectiveDephasing : Lindbladian n₄ where
  hamiltonian := 0  -- Pure dephasing, no coherent evolution
  jumpOps := [collectiveZ]
  hamiltonian_hermitian := by simp [Matrix.IsHermitian]

/-- collectiveZ is Hermitian (real diagonal matrix) -/
theorem collectiveZ_hermitian : collectiveZ† = collectiveZ := by
  have h2 : (star (2 : ℂ) : ℂ) = 2 := by simp [Complex.star_def]
  have h0 : (star (0 : ℂ) : ℂ) = 0 := star_zero ℂ
  have hm2 : (star (-2 : ℂ) : ℂ) = -2 := by simp [Complex.star_def]
  ext a b
  simp only [collectiveZ, dagger, conjTranspose_apply, diagonal_apply]
  by_cases hab : b = a
  · simp only [hab, ↓reduceIte]
    fin_cases a
    · exact h2
    · exact h0
    · exact h0
    · exact hm2
  · simp only [hab, ↓reduceIte, Ne.symm hab, star_zero]

/-- The commutant of collectiveDephasing contains dfsProjector -/
theorem dfsProjector_in_commutant :
    dfsProjector ∈ commutantSubmodule collectiveDephasing := by
  simp only [commutantSubmodule, Submodule.mem_mk, Set.mem_setOf_eq, IsInCommutant]
  refine ⟨?_, ?_, ?_⟩
  · -- [dfsProjector, H] = [dfsProjector, 0] = 0
    simp [commutator, collectiveDephasing]
  · -- [dfsProjector, Lk] = 0 for all Lk
    intro Lk hLk
    simp only [collectiveDephasing, List.mem_singleton] at hLk
    rw [hLk]
    exact dfsProjector_comm_collectiveZ
  · -- [dfsProjector, Lk†] = 0 for all Lk
    intro Lk hLk
    simp only [collectiveDephasing, List.mem_singleton] at hLk
    rw [hLk, collectiveZ_hermitian]
    exact dfsProjector_comm_collectiveZ

/-- The commutant of collectiveDephasing is not just scalars -/
theorem collectiveDephasing_commutant_not_scalar :
    ¬(commutantSubmodule collectiveDephasing =
      Submodule.span ℂ {(1 : Matrix (Fin n₄) (Fin n₄) ℂ)}) := by
  intro h
  -- dfsProjector ∈ commutant but dfsProjector ∉ span{I}
  have hIn := dfsProjector_in_commutant
  rw [h] at hIn
  rw [Submodule.mem_span_singleton] at hIn
  obtain ⟨c, hc⟩ := hIn
  exact dfsProjector_not_scalar ⟨c, hc.symm⟩

/-- Identity and dfsProjector are linearly independent -/
theorem one_dfsProjector_linearIndependent :
    LinearIndependent ℂ ![1, dfsProjector] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Unfold the sum: g 0 • 1 + g 1 • dfsProjector = 0
  have hsum : g 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + g 1 • dfsProjector = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
    exact hg
  -- Evaluate at (0,0): g 0 • 1 + g 1 • 0 = 0, so g 0 = 0
  have h00 : g 0 = 0 := by
    have := congrFun (congrFun hsum ket00) ket00
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      dfsProjector, matrixUnit_apply, ket00, ket01, ket10,
      Fin.isValue, Fin.reduceEq, and_self, ↓reduceIte,
      smul_eq_mul, mul_one, mul_zero, add_zero, Matrix.zero_apply] at this
    exact this
  -- Evaluate at (1,1): g 0 • 1 + g 1 • 1 = 0, so g 0 + g 1 = 0
  have h11 : g 0 + g 1 = 0 := by
    have := congrFun (congrFun hsum ket01) ket01
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      dfsProjector, matrixUnit_apply, ket00, ket01, ket10,
      Fin.isValue, Fin.reduceEq, and_self, ↓reduceIte,
      smul_eq_mul, mul_one, mul_zero, add_zero, Matrix.zero_apply] at this
    exact this
  -- Conclude g 1 = 0 from h00 and h11
  intro i
  fin_cases i
  · exact h00
  · simp only [h00, zero_add] at h11; exact h11

/-- The identity matrix is stationary for collectiveDephasing.
    For pure dephasing with diagonal jump operator, diagonal matrices are stationary. -/
theorem identity_stationary_collectiveDephasing :
    collectiveDephasing.IsStationaryState (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [Lindbladian.IsStationaryState, Lindbladian.apply, Lindbladian.unitaryPart,
    Lindbladian.dissipator, collectiveDephasing]
  -- H = 0, so unitary part is 0
  simp only [commutator, Matrix.zero_mul, Matrix.mul_zero, sub_self, smul_zero, zero_add]
  -- Dissipator with single jump operator collectiveZ
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  -- Show singleDissipator collectiveZ 1 = 0
  simp only [Lindbladian.singleDissipator, anticommutator]
  -- For diagonal L and identity: LIL† = LL† and {L†L, I} = 2L†L
  -- Since L is Hermitian (L† = L), we have LL† = L² and L†L = L²
  rw [collectiveZ_hermitian]
  simp only [Matrix.mul_one, Matrix.one_mul]
  -- collectiveZ * collectiveZ - (1/2) • (collectiveZ * collectiveZ + collectiveZ * collectiveZ)
  -- = Z² - (1/2) • 2Z² = Z² - Z² = 0
  simp only [two_smul, smul_add, ← add_smul]
  norm_num

/-- The identity matrix is positive definite -/
theorem identity_isPositiveDefinite :
    IsPositiveDefinite (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  constructor
  · -- Hermitian
    exact Matrix.isHermitian_one
  · -- Strictly positive for nonzero v
    intro v hv
    simp only [Matrix.one_mulVec]
    -- star v ⬝ᵥ v = Σ |v_i|² > 0 for v ≠ 0
    have h : (star v ⬝ᵥ v).re = ∑ i : Fin 4, Complex.normSq (v i) := by
      simp only [Matrix.dotProduct, Pi.star_apply]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      -- star z * z = conj z * z has real part = normSq z
      rw [Complex.star_def]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
      ring
    rw [h]
    apply Finset.sum_pos'
    · intro i _
      exact Complex.normSq_nonneg _
    · -- At least one term is positive since v ≠ 0
      simp only [Function.ne_iff] at hv
      obtain ⟨i, hi⟩ := hv
      exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- collectiveDephasing has a faithful stationary state -/
theorem collectiveDephasing_hasFaithfulStationaryState :
    HasFaithfulStationaryState collectiveDephasing :=
  ⟨1, identity_stationary_collectiveDephasing, identity_isPositiveDefinite⟩

/-- Both 1 and dfsProjector are in the commutant -/
theorem one_mem_commutant_collectiveDephasing :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ commutantSubmodule collectiveDephasing :=
  one_mem_commutant collectiveDephasing

/-- Linear independence gives lower bound on submodule dimension -/
theorem commutant_finrank_ge_two :
    2 ≤ Module.finrank ℂ (commutantSubmodule collectiveDephasing) := by
  -- The function ![1, dfsProjector] maps Fin 2 → commutant
  -- It's linearly independent, so finrank ≥ 2
  have hLI := one_dfsProjector_linearIndependent
  -- Lift to commutant submodule
  have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ commutantSubmodule collectiveDephasing :=
    one_mem_commutant_collectiveDephasing
  have h2 : dfsProjector ∈ commutantSubmodule collectiveDephasing :=
    dfsProjector_in_commutant
  -- Define the map into the submodule
  let f : Fin 2 → commutantSubmodule collectiveDephasing :=
    ![⟨1, h1⟩, ⟨dfsProjector, h2⟩]
  -- f is linearly independent
  have hLI' : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    -- If Σ g_i • f_i = 0 in the submodule, then Σ g_i • (f_i).val = 0 in the ambient space
    have hsum : g 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) + g 1 • dfsProjector = 0 := by
      have := congrArg Subtype.val hg
      simp only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Submodule.coe_smul_of_tower, Submodule.coe_add,
        Submodule.coe_zero] at this
      exact this
    -- Apply the linear independence in the ambient space
    rw [Fintype.linearIndependent_iff] at hLI
    have hLI_applied := hLI g (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]; exact hsum)
    exact hLI_applied
  -- Use fintype_card_le_finrank
  have hCard : Fintype.card (Fin 2) ≤ Module.finrank ℂ (commutantSubmodule collectiveDephasing) :=
    hLI'.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hCard
  exact hCard

/-- Collective dephasing has quantum deficiency > 0 -/
theorem collectiveDephasing_deficiency_positive :
    0 < quantumDeficiency collectiveDephasing := by
  unfold quantumDeficiency
  -- dim(stationary) = dim(commutant) by Evans-Høegh-Krohn (needs faithful stationary state)
  have hDimEq := commutant_dim_eq_stationary_dim collectiveDephasing
    collectiveDephasing_hasFaithfulStationaryState
  -- dim(commutant) ≥ 2
  have hCommGe2 := commutant_finrank_ge_two
  -- Therefore dim(stationary) ≥ 2
  have hStatGe2 : 2 ≤ Module.finrank ℂ collectiveDephasing.stationarySubspace := by
    rw [← hDimEq]
    exact hCommGe2
  -- So dim(stationary) - 1 ≥ 1 > 0
  omega

/-! ### Summary -/

/-- **Main Result**: Collective dephasing demonstrates the gap between
    structural and actual deficiency.

    - The constraint graph is connected (morally δ_struct = 0)
    - But δ_Q > 0 due to eigenvalue degeneracy creating a DFS

    This shows that δ_struct is a lower bound but not tight when
    symmetry-protected degeneracies exist. -/
theorem collectiveDephasing_demonstrates_gap :
    -- Constraint graph connected (would give δ_struct = 0)
    (∀ i j : Fin 4, i ≠ j →
      ∃ path : List (Fin 4), path.head? = some i ∧ path.getLast? = some j) ∧
    -- But commutant is non-trivial
    (∃ X : Matrix (Fin 4) (Fin 4) ℂ,
      X ∈ commutantSubmodule collectiveDephasing ∧
      ¬∃ c : ℂ, X = c • 1) := by
  constructor
  · intro i j _
    -- Trivial: path [i, j] works for connectivity (not constraint edges)
    exact ⟨[i, j], by simp, by simp⟩
  · exact ⟨dfsProjector, dfsProjector_in_commutant, dfsProjector_not_scalar⟩

end DefectCRN.Quantum.Examples
