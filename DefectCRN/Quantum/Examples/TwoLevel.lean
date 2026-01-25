/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.QuantumDZT

/-!
# Two-Level System (Qubit) Example

The simplest quantum system: a two-level system with spontaneous decay.

## Model

- Two states: |0⟩ (ground) and |1⟩ (excited)
- Hamiltonian: H = ω|1⟩⟨1|
- Decay: L = √γ |0⟩⟨1| (spontaneous emission)

This is the quantum analog of A → B in classical CRNT.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum.Examples.TwoLevel

open scoped Matrix BigOperators ComplexConjugate
open Matrix DefectCRN.Quantum

/-- Two-level Hamiltonian with energy gap ω -/
def twoLevelH (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 0], ![0, (ω : ℂ)]]

/-- Lowering operator σ- = |0⟩⟨1|
    Lowers from |1⟩ to |0⟩: σ⁻|1⟩ = |0⟩, σ⁻|0⟩ = 0 -/
def σminus : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![0, 0]]

/-- The two-level Hamiltonian is Hermitian -/
theorem twoLevelH_hermitian (ω : ℝ) : (twoLevelH ω).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoLevelH, Matrix.of_apply, Complex.conj_ofReal]

/-- Decay operator with rate γ -/
noncomputable def decayOp (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt γ : ℂ) • σminus

/-- Two-level Lindbladian with spontaneous decay -/
noncomputable def twoLevelL (ω γ : ℝ) : Lindbladian 2 where
  hamiltonian := twoLevelH ω
  hamiltonian_hermitian := twoLevelH_hermitian ω
  jumpOps := [decayOp γ]

/-- Ground state |0⟩⟨0| -/
def groundState : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, 0]]

/-- Ground state is Hermitian -/
theorem groundState_hermitian : groundState.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groundState, Matrix.of_apply]

/-- Ground state has trace 1 -/
theorem groundState_trace : groundState.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, groundState]
  -- Sum over Fin 2: groundState 0 0 + groundState 1 1 = 1 + 0 = 1
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- σ⁺ (raising operator) = σ⁻† -/
def σplus : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 0], ![1, 0]]

/-- σ⁻† = σ⁺ -/
theorem σminus_dagger : σminus† = σplus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σminus, σplus, dagger, conjTranspose, Matrix.of_apply]

/-- H * groundState = 0 -/
theorem H_mul_groundState (ω : ℝ) : twoLevelH ω * groundState = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoLevelH, groundState, Matrix.mul_apply, Fin.sum_univ_two]

/-- groundState * H = 0 -/
theorem groundState_mul_H (ω : ℝ) : groundState * twoLevelH ω = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoLevelH, groundState, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁻ * groundState = 0 (ground state is annihilated by lowering) -/
theorem σminus_mul_groundState : σminus * groundState = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σminus, groundState, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁺ * σ⁻ = |1⟩⟨1| (number operator for excited state) -/
theorem σplus_σminus : σplus * σminus = ![![0, 0], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σplus, σminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁺σ⁻ * groundState = 0 -/
theorem σplus_σminus_mul_groundState : (σplus * σminus) * groundState = 0 := by
  rw [σplus_σminus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groundState, Matrix.mul_apply, Fin.sum_univ_two]

/-- groundState * σ⁺σ⁻ = 0 -/
theorem groundState_mul_σplus_σminus : groundState * (σplus * σminus) = 0 := by
  rw [σplus_σminus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groundState, Matrix.mul_apply, Fin.sum_univ_two]

/-- Dagger of scaled σ⁻ -/
theorem decayOp_dagger (γ : ℝ) : (decayOp γ)† = (Real.sqrt γ : ℂ) • σplus := by
  unfold decayOp
  rw [dagger_smul, σminus_dagger]
  simp [Complex.star_def, Complex.conj_ofReal]

/-- L†L for the decay operator (when γ ≥ 0) -/
theorem decayOp_dagger_mul_decayOp (γ : ℝ) (hγ : γ ≥ 0) :
    (decayOp γ)† * (decayOp γ) = (γ : ℂ) • (σplus * σminus) := by
  unfold decayOp
  rw [dagger_smul, σminus_dagger]
  simp only [Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  exact Real.mul_self_sqrt hγ

/-- L†L * groundState = 0 -/
theorem decayOp_dagger_decayOp_mul_groundState (γ : ℝ) (hγ : γ ≥ 0) :
    (decayOp γ)† * (decayOp γ) * groundState = 0 := by
  rw [decayOp_dagger_mul_decayOp γ hγ, Matrix.smul_mul, σplus_σminus_mul_groundState, smul_zero]

/-- groundState * L†L = 0 -/
theorem groundState_mul_decayOp_dagger_decayOp (γ : ℝ) (hγ : γ ≥ 0) :
    groundState * ((decayOp γ)† * (decayOp γ)) = 0 := by
  rw [decayOp_dagger_mul_decayOp γ hγ, Matrix.mul_smul, groundState_mul_σplus_σminus, smul_zero]

/-- The ground state is stationary (for γ ≥ 0) -/
theorem groundState_stationary (ω γ : ℝ) (hγ : γ ≥ 0) :
    (twoLevelL ω γ).IsStationaryState groundState := by
  unfold Lindbladian.IsStationaryState Lindbladian.apply Lindbladian.unitaryPart
    Lindbladian.dissipator twoLevelL
  simp only [List.foldl_cons, List.foldl_nil, add_zero]
  -- Unitary part: -i[H, ρ] = 0 since [H, groundState] = 0
  have hComm : ⟦twoLevelH ω, groundState⟧ = 0 := by
    simp only [commutator, H_mul_groundState, groundState_mul_H, sub_zero]
  simp only [hComm, smul_zero, zero_add]
  -- Dissipator: L ρ L† - ½{L†L, ρ} = 0
  unfold Lindbladian.singleDissipator
  -- L * groundState = 0 since σ⁻ * groundState = 0
  have hLρ : decayOp γ * groundState = 0 := by
    unfold decayOp
    rw [Matrix.smul_mul, σminus_mul_groundState, smul_zero]
  simp only [hLρ, Matrix.zero_mul, zero_sub, neg_eq_zero]
  -- ½{L†L, ρ} = 0 since both L†L*ρ and ρ*L†L are zero
  simp only [anticommutator, decayOp_dagger_decayOp_mul_groundState γ hγ,
    groundState_mul_decayOp_dagger_decayOp γ hγ, add_zero, smul_zero]

/-- [X, σ⁻] = 0 implies X_{10} = 0 and X_{00} = X_{11} -/
theorem sigma_minus_commutator (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟦X, σminus⟧ = 0 → X 1 0 = 0 ∧ X 0 0 = X 1 1 := by
  intro hComm
  -- [X, σ⁻]_{00} = -X_{10}, so X_{10} = 0
  -- [X, σ⁻]_{01} = X_{00} - X_{11}, so X_{00} = X_{11}
  have h00 : (⟦X, σminus⟧ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by rw [hComm]; rfl
  have h01 : (⟦X, σminus⟧ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by rw [hComm]; rfl
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    σminus, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h00 h01
  ring_nf at h00 h01
  constructor
  · exact neg_eq_zero.mp h00
  · exact sub_eq_zero.mp h01

/-- [X, σ⁺] = 0 implies X_{01} = 0 and X_{00} = X_{11} -/
theorem sigma_plus_commutator (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟦X, σplus⟧ = 0 → X 0 1 = 0 ∧ X 0 0 = X 1 1 := by
  intro hComm
  -- [X, σ⁺]_{00} = X_{01}, so X_{01} = 0
  -- [X, σ⁺]_{10} = X_{11} - X_{00}, so X_{00} = X_{11}
  have h00 : (⟦X, σplus⟧ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by rw [hComm]; rfl
  have h10 : (⟦X, σplus⟧ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hComm]; rfl
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    σplus, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h00 h10
  ring_nf at h00 h10
  constructor
  · exact h00
  · -- h10: -X 0 0 + X 1 1 = 0, i.e., X 1 1 = X 0 0
    have : X 1 1 = X 0 0 := by
      have h := h10
      ring_nf at h ⊢
      rw [neg_add_eq_zero] at h
      exact h.symm
    exact this.symm

/-- For γ > 0, the two-level system is ergodic -/
theorem twoLevel_ergodic (ω γ : ℝ) (hγ : γ > 0) :
    IsErgodic (twoLevelL ω γ) := by
  -- IsErgodic means hasTrivialCommutant
  unfold IsErgodic hasTrivialCommutant commutantSet IsInCommutant twoLevelL
  simp only [Set.mem_setOf_eq, List.mem_singleton]
  intro X ⟨_, hCommL, hCommLdag⟩
  -- From [X, decayOp γ] = 0, extract [X, σ⁻] = 0
  have hCommSigma : ⟦X, σminus⟧ = 0 := by
    have hL := hCommL (decayOp γ) rfl
    unfold decayOp at hL
    rw [commutator_smul_right] at hL
    have hγ' : (Real.sqrt γ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero']
      linarith
    exact smul_eq_zero.mp hL |>.resolve_left hγ'
  -- From [X, (decayOp γ)†] = 0, extract [X, σ⁺] = 0
  have hCommSigmaPlus : ⟦X, σplus⟧ = 0 := by
    have hLdag := hCommLdag (decayOp γ) rfl
    rw [decayOp_dagger] at hLdag
    rw [commutator_smul_right] at hLdag
    have hγ' : (Real.sqrt γ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero']
      linarith
    exact smul_eq_zero.mp hLdag |>.resolve_left hγ'
  -- From [X, σ⁻] = 0: X_{10} = 0, X_{00} = X_{11}
  obtain ⟨hX10, hDiag⟩ := sigma_minus_commutator X hCommSigma
  -- From [X, σ⁺] = 0: X_{01} = 0, X_{00} = X_{11}
  obtain ⟨hX01, _⟩ := sigma_plus_commutator X hCommSigmaPlus
  -- So X = X_{00} • I
  use X 0 0
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hX01]
  · simp [Matrix.one_apply, hX10]
  · simp [Matrix.one_apply, hDiag]

/-- Quantum deficiency is zero for γ > 0 -/
theorem twoLevel_deficiency_zero (ω γ : ℝ) (hγ : γ > 0) :
    quantumDeficiency (twoLevelL ω γ) = 0 := by
  rw [deficiency_zero_iff_ergodic]
  exact twoLevel_ergodic ω γ hγ

end DefectCRN.Quantum.Examples.TwoLevel
