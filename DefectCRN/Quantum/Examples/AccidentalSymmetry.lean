/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.StructuralDeficiency

/-!
# Accidental Symmetry Example

This example demonstrates the distinction between structural deficiency (δ_Q^struct)
and quantum deficiency (δ_Q) through the phenomenon of "accidental symmetry."

## Model

Consider n = 2 with:
- Hamiltonian: H = ω σ_x where σ_x = |0⟩⟨1| + |1⟩⟨0|
- Single self-adjoint jump operator: L = √γ σ_x

The quantum network graph G has coherent edge {0,1}.

## Key Results

1. **Structural analysis**: D(G) is strongly connected, so δ_Q^struct(G) = 0
2. **Specific dynamics**: The aligned operators create a hidden conservation law
3. **Accidental symmetry**: δ_Q = 1 > 0 = δ_Q^struct(G)

## Physical Interpretation

Both |+⟩⟨+| and |-⟩⟨-| are stationary states, where |±⟩ = (|0⟩ ± |1⟩)/√2.
The Lindbladian L(ρ) = -iω[σ_x, ρ] + γ(σ_x ρ σ_x - ρ) vanishes on any
ρ diagonal in the {|+⟩, |-⟩} basis because [σ_x, ρ] = 0 and σ_x² = I.

## References

* Paper Example 3.7: "Genericity in Action: Accidental Symmetry"
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum.Examples.AccidentalSymmetry

open scoped Matrix BigOperators ComplexConjugate
open Matrix DefectCRN.Quantum

/-! ### Pauli σ_x matrix -/

/-- Pauli X matrix: σ_x = |0⟩⟨1| + |1⟩⟨0| -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]

/-- σ_x is self-adjoint (Hermitian) -/
theorem σx_hermitian : σx.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σx, Matrix.of_apply]

/-- σ_x² = I -/
theorem σx_sq : σx * σx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ_x has trace 0 -/
theorem σx_trace : σx.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, σx]
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ### The aligned Lindbladian -/

/-- Hamiltonian H = ω σ_x -/
noncomputable def alignedH (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (ω : ℂ) • σx

/-- The aligned Hamiltonian is Hermitian -/
theorem alignedH_hermitian (ω : ℝ) : (alignedH ω).IsHermitian := by
  unfold alignedH
  rw [Matrix.IsHermitian, conjTranspose_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact σx_hermitian.eq

/-- Jump operator L = √γ σ_x -/
noncomputable def alignedJump (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt γ : ℂ) • σx

/-- The aligned Lindbladian with H = ω σ_x and L = √γ σ_x -/
noncomputable def alignedL (ω γ : ℝ) : Lindbladian 2 where
  hamiltonian := alignedH ω
  hamiltonian_hermitian := alignedH_hermitian ω
  jumpOps := [alignedJump γ]

/-! ### Plus and minus eigenstates -/

/-- Plus eigenstate |+⟩⟨+| = (1/2)(I + σ_x) -/
noncomputable def plusState : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (1 + σx)

/-- Minus eigenstate |-⟩⟨-| = (1/2)(I - σ_x) -/
noncomputable def minusState : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (1 - σx)

/-- Plus state is Hermitian -/
theorem plusState_hermitian : plusState.IsHermitian := by
  unfold plusState
  rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_one, σx_hermitian.eq]
  congr 1
  simp [Complex.star_def]

/-- Minus state is Hermitian -/
theorem minusState_hermitian : minusState.IsHermitian := by
  unfold minusState
  rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_one, σx_hermitian.eq]
  congr 1
  simp [Complex.star_def]

/-- Plus state has trace 1 -/
theorem plusState_trace : plusState.trace = 1 := by
  unfold plusState
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, σx_trace]
  simp

/-- Minus state has trace 1 -/
theorem minusState_trace : minusState.trace = 1 := by
  unfold minusState
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, σx_trace]
  simp

/-! ### σ_x commutes with plus and minus states -/

/-- σ_x commutes with plus state: [σ_x, |+⟩⟨+|] = 0 -/
theorem σx_comm_plusState : ⟦σx, plusState⟧ = 0 := by
  unfold plusState commutator
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, σx_sq, sub_self]

/-- σ_x commutes with minus state: [σ_x, |-⟩⟨-|] = 0 -/
theorem σx_comm_minusState : ⟦σx, minusState⟧ = 0 := by
  unfold minusState commutator
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul, σx_sq, sub_self]

/-- σ_x |+⟩⟨+| σ_x = |+⟩⟨+| (since σ_x² = I) -/
theorem σx_plusState_σx : σx * plusState * σx = plusState := by
  unfold plusState
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul]
  have h1 : σx * σx * σx = σx := by rw [σx_sq]; simp
  simp only [σx_sq, h1, one_mul]

/-- σ_x |-⟩⟨-| σ_x = |-⟩⟨-| -/
theorem σx_minusState_σx : σx * minusState * σx = minusState := by
  unfold minusState
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul]
  have h1 : σx * σx * σx = σx := by rw [σx_sq]; simp
  simp only [σx_sq, h1, one_mul]

/-! ### Helper lemmas for aligned jump operator -/

/-- The aligned jump operator is self-adjoint -/
theorem alignedJump_self_adjoint (γ : ℝ) : (alignedJump γ)† = alignedJump γ := by
  unfold alignedJump
  rw [dagger_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact σx_hermitian.eq

/-- L†L = γI for the aligned jump operator -/
theorem alignedJump_dagger_mul (γ : ℝ) (hγ : γ ≥ 0) :
    (alignedJump γ)† * (alignedJump γ) = (γ : ℂ) • 1 := by
  rw [alignedJump_self_adjoint]
  unfold alignedJump
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, σx_sq]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  exact Real.mul_self_sqrt hγ

/-- L * plusState * L† = γ * plusState -/
theorem alignedJump_sandwich_plusState (γ : ℝ) (hγ : γ ≥ 0) :
    (alignedJump γ) * plusState * (alignedJump γ)† = (γ : ℂ) • plusState := by
  rw [alignedJump_self_adjoint]
  unfold alignedJump
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [σx_plusState_σx]
  simp only [smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  exact Real.mul_self_sqrt hγ

/-- L * minusState * L† = γ * minusState -/
theorem alignedJump_sandwich_minusState (γ : ℝ) (hγ : γ ≥ 0) :
    (alignedJump γ) * minusState * (alignedJump γ)† = (γ : ℂ) • minusState := by
  rw [alignedJump_self_adjoint]
  unfold alignedJump
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [σx_minusState_σx]
  simp only [smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  exact Real.mul_self_sqrt hγ

/-- {L†L, plusState} = 2γ * plusState -/
theorem alignedJump_anticomm_plusState (γ : ℝ) (hγ : γ ≥ 0) :
    ⟨(alignedJump γ)† * (alignedJump γ), plusState⟩₊ = (2 * γ : ℂ) • plusState := by
  rw [alignedJump_dagger_mul γ hγ]
  simp only [anticommutator, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [← smul_add, ← two_smul ℂ plusState, smul_smul]
  congr 1
  ring

/-- {L†L, minusState} = 2γ * minusState -/
theorem alignedJump_anticomm_minusState (γ : ℝ) (hγ : γ ≥ 0) :
    ⟨(alignedJump γ)† * (alignedJump γ), minusState⟩₊ = (2 * γ : ℂ) • minusState := by
  rw [alignedJump_dagger_mul γ hγ]
  simp only [anticommutator, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [← smul_add, ← two_smul ℂ minusState, smul_smul]
  congr 1
  ring

/-! ### Stationarity proofs -/

/-- The plus state is stationary under the aligned Lindbladian.

    L(|+⟩⟨+|) = -iω[σ_x, |+⟩⟨+|] + γ(σ_x|+⟩⟨+|σ_x - |+⟩⟨+|) = 0 -/
theorem plusState_stationary (ω γ : ℝ) (hγ : γ ≥ 0) :
    (alignedL ω γ).IsStationaryState plusState := by
  unfold Lindbladian.IsStationaryState Lindbladian.apply Lindbladian.unitaryPart
    Lindbladian.dissipator alignedL
  simp only [List.foldl_cons, List.foldl_nil, add_zero]
  -- Unitary part: -i[H, ρ] = -iω[σ_x, plusState] = 0
  have hUnitary : ⟦alignedH ω, plusState⟧ = 0 := by
    unfold alignedH
    rw [commutator_smul_left, σx_comm_plusState, smul_zero]
  simp only [hUnitary, smul_zero, zero_add]
  -- Dissipator: L ρ L† - ½{L†L, ρ}
  unfold Lindbladian.singleDissipator
  rw [alignedJump_sandwich_plusState γ hγ, alignedJump_anticomm_plusState γ hγ]
  -- γ • plusState - (1/2) • (2*γ) • plusState = 0
  rw [smul_smul]
  have h : (1/2 : ℂ) * (2 * ↑γ) = ↑γ := by ring
  rw [h, sub_self]

/-- The minus state is stationary under the aligned Lindbladian -/
theorem minusState_stationary (ω γ : ℝ) (hγ : γ ≥ 0) :
    (alignedL ω γ).IsStationaryState minusState := by
  unfold Lindbladian.IsStationaryState Lindbladian.apply Lindbladian.unitaryPart
    Lindbladian.dissipator alignedL
  simp only [List.foldl_cons, List.foldl_nil, add_zero]
  -- Unitary part
  have hUnitary : ⟦alignedH ω, minusState⟧ = 0 := by
    unfold alignedH
    rw [commutator_smul_left, σx_comm_minusState, smul_zero]
  simp only [hUnitary, smul_zero, zero_add]
  -- Dissipator
  unfold Lindbladian.singleDissipator
  rw [alignedJump_sandwich_minusState γ hγ, alignedJump_anticomm_minusState γ hγ]
  rw [smul_smul]
  have h : (1/2 : ℂ) * (2 * ↑γ) = ↑γ := by ring
  rw [h, sub_self]

/-! ### Non-uniqueness and deficiency -/

/-- The plus and minus states are distinct -/
theorem plusState_ne_minusState : plusState ≠ minusState := by
  -- plusState = (1/2)(I + σ_x) has (0,1) entry = 1/2
  -- minusState = (1/2)(I - σ_x) has (0,1) entry = -1/2
  intro h
  have h01 : plusState 0 1 = minusState 0 1 := congrFun (congrFun h 0) 1
  unfold plusState minusState at h01
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, σx] at h01
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h01
  -- h01: 1/2 = -1/2, contradiction
  norm_num at h01

/-- The aligned Lindbladian has at least two independent stationary states.
    This demonstrates δ_Q ≥ 1 (non-uniqueness). -/
theorem alignedL_two_stationary_states (ω γ : ℝ) (hγ : γ ≥ 0) :
    ∃ ρ₁ ρ₂ : Matrix (Fin 2) (Fin 2) ℂ,
      ρ₁ ≠ ρ₂ ∧
      (alignedL ω γ).IsStationaryState ρ₁ ∧
      (alignedL ω γ).IsStationaryState ρ₂ :=
  ⟨plusState, minusState, plusState_ne_minusState,
   plusState_stationary ω γ hγ, minusState_stationary ω γ hγ⟩

/-! ### Commutant analysis -/

/-- The commutant of σ_x is 2-dimensional: span{I, σ_x}.

    [X, σ_x] = 0 iff X = aI + bσ_x for some a, b ∈ ℂ. -/
theorem σx_commutant_two_dimensional :
    ∀ X : Matrix (Fin 2) (Fin 2) ℂ, ⟦X, σx⟧ = 0 →
    ∃ a b : ℂ, X = a • 1 + b • σx := by
  intro X hComm
  have hXσ : X * σx = σx * X := sub_eq_zero.mp hComm
  -- From [X, σ_x] = 0, we get constraints:
  -- (0,0): X_{01} - X_{10} = 0  →  X_{01} = X_{10}
  -- (0,1): X_{00} - X_{11} = 0  →  X_{00} = X_{11}
  have h00 : (⟦X, σx⟧ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by rw [hComm]; rfl
  have h01 : (⟦X, σx⟧ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by rw [hComm]; rfl
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    σx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h00 h01
  ring_nf at h00 h01
  have hX01_eq_X10 : X 0 1 = X 1 0 := sub_eq_zero.mp h00
  have hX00_eq_X11 : X 0 0 = X 1 1 := sub_eq_zero.mp h01
  -- X = [[a, b], [b, a]] = aI + bσ_x
  use X 0 0, X 0 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hX01_eq_X10, hX00_eq_X11]

/-- The aligned Lindbladian is NOT ergodic.

    Since H ∝ σ_x and L ∝ σ_x, the commutant is span{I, σ_x}, not just ℂI. -/
theorem alignedL_not_ergodic (ω γ : ℝ) (hω : ω ≠ 0) (hγ : γ > 0) :
    ¬ IsErgodic (alignedL ω γ) := by
  intro hErg
  -- σ_x is in the commutant
  have hσx_comm_H : ⟦σx, alignedH ω⟧ = 0 := by
    unfold alignedH
    rw [commutator_smul_right, commutator_self, smul_zero]
  have hσx_comm_L : ⟦σx, alignedJump γ⟧ = 0 := by
    unfold alignedJump
    rw [commutator_smul_right, commutator_self, smul_zero]
  have hLdag : (alignedJump γ)† = alignedJump γ := by
    unfold alignedJump
    rw [dagger_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    congr 1
    exact σx_hermitian.eq
  have hσx_comm_Ldag : ⟦σx, (alignedJump γ)†⟧ = 0 := by rw [hLdag]; exact hσx_comm_L
  have hσx_in_comm : σx ∈ commutantSet (alignedL ω γ) := by
    simp only [commutantSet, Set.mem_setOf_eq, IsInCommutant, alignedL]
    constructor
    · exact hσx_comm_H
    constructor
    · intro Lk hLk; simp only [List.mem_singleton] at hLk; rw [hLk]; exact hσx_comm_L
    · intro Lk hLk; simp only [List.mem_singleton] at hLk; rw [hLk]; exact hσx_comm_Ldag
  -- But σ_x is not a scalar multiple of I
  have hσx_not_scalar : ¬∃ c : ℂ, σx = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro ⟨c, hc⟩
    have h01 : σx 0 1 = (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 := by rw [hc]
    simp [σx, Matrix.one_apply] at h01
  -- Contradiction with ergodicity
  unfold IsErgodic hasTrivialCommutant at hErg
  exact hσx_not_scalar (hErg σx hσx_in_comm)

/-- The commutant of the aligned Lindbladian equals the commutant of σ_x.
    Since H = ω·σ_x and L = √γ·σ_x, [X, H] = 0 ∧ [X, L] = 0 ⟺ [X, σ_x] = 0 -/
theorem alignedL_commutant_eq_σx_commutant (ω γ : ℝ) (hω : ω ≠ 0) (hγ : γ > 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ commutantSet (alignedL ω γ) ↔ ⟦X, σx⟧ = 0 := by
  constructor
  · -- If X is in the Lindbladian commutant, then [X, σ_x] = 0
    intro ⟨hH, _, _⟩
    -- From [X, H] = 0 where H = ω·σ_x
    simp only [alignedL] at hH
    unfold alignedH at hH
    rw [commutator_smul_right] at hH
    have hω' : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
    exact smul_eq_zero.mp hH |>.resolve_left hω'
  · -- If [X, σ_x] = 0, then X is in the Lindbladian commutant
    intro hComm
    simp only [commutantSet, Set.mem_setOf_eq, IsInCommutant, alignedL]
    constructor
    · -- [X, H] = 0
      unfold alignedH
      rw [commutator_smul_right, hComm, smul_zero]
    constructor
    · -- [X, Lk] = 0 for all jump operators
      intro Lk hLk
      simp only [List.mem_singleton] at hLk
      rw [hLk]
      unfold alignedJump
      rw [commutator_smul_right, hComm, smul_zero]
    · -- [X, Lk†] = 0 for all jump operators
      intro Lk hLk
      simp only [List.mem_singleton] at hLk
      rw [hLk, alignedJump_self_adjoint]
      unfold alignedJump
      rw [commutator_smul_right, hComm, smul_zero]

/-- I and σ_x are linearly independent -/
theorem one_σx_linearIndependent :
    LinearIndependent ℂ ![1, σx] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  -- hsum : ∑ i, g i • ![1, σx] i = 0
  -- This means g 0 • 1 + g 1 • σx = 0
  have hsum' : g 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + g 1 • σx = 0 := by
    convert hsum using 1
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- Look at (0,0) entry: g 0 = 0
  have h00 : g 0 = 0 := by
    have := congrFun (congrFun hsum' 0) 0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      σx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul, mul_one, mul_zero, add_zero, Matrix.zero_apply] at this
    exact this
  -- Look at (0,1) entry: g 1 = 0
  have h01 : g 1 = 0 := by
    have := congrFun (congrFun hsum' 0) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      σx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul, mul_one, mul_zero, add_zero, Matrix.zero_apply] at this
    -- The if statement should simplify: (0 : Fin 2) ≠ (1 : Fin 2)
    simp only [Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓reduceIte, mul_zero, zero_add, mul_one] at this
    exact this
  intro i
  fin_cases i
  · exact h00
  · exact h01

/-- The σ_x-commutant is spanned by I and σ_x -/
noncomputable def σxCommutantSubmodule : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Submodule.span ℂ {1, σx}

/-- Any matrix commuting with σ_x is in span{I, σ_x} -/
theorem σx_commutant_subset_span (X : Matrix (Fin 2) (Fin 2) ℂ) (hComm : ⟦X, σx⟧ = 0) :
    X ∈ σxCommutantSubmodule := by
  obtain ⟨a, b, hab⟩ := σx_commutant_two_dimensional X hComm
  rw [hab]
  unfold σxCommutantSubmodule
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert _ _))
  · exact Submodule.smul_mem _ b (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

/-- The dimension of span{I, σ_x} is 2 -/
theorem finrank_σxCommutant : Module.finrank ℂ σxCommutantSubmodule = 2 := by
  -- The basis is {I, σ_x}
  have hLI := one_σx_linearIndependent
  have hBasis : Submodule.span ℂ (Set.range ![1, σx]) = σxCommutantSubmodule := by
    unfold σxCommutantSubmodule
    congr 1
    ext x
    simp only [Set.mem_range, Matrix.cons_val_fin_one, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨i, hi⟩
      fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · intro h
      cases h with
      | inl h => exact ⟨0, by simp [h]⟩
      | inr h => exact ⟨1, by simp [h]⟩
  rw [← hBasis]
  exact finrank_span_eq_card hLI

/-- **Main Result**: The aligned Lindbladian has quantum deficiency δ_Q = 1.

    The structural deficiency is δ_Q^struct = 0 (since D(G) is strongly connected),
    but the specific parameter choice H = ωσ_x, L = √γσ_x creates an "accidental
    symmetry" that enlarges the commutant from ℂI to span{I, σ_x}.

    This is the core demonstration of non-genericity in quantum deficiency. -/
theorem alignedL_deficiency_one (ω γ : ℝ) (hω : ω ≠ 0) (hγ : γ > 0) :
    quantumDeficiency (alignedL ω γ) = 1 := by
  -- Step 1: Show commutant(alignedL) has dimension 2
  -- The commutant equals the σ_x-commutant which has dimension 2

  -- First, show the commutant submodule equals σxCommutantSubmodule
  have hCommEq : commutantSubmodule (alignedL ω γ) = σxCommutantSubmodule := by
    ext X
    constructor
    · intro hX
      have hComm : ⟦X, σx⟧ = 0 := (alignedL_commutant_eq_σx_commutant ω γ hω hγ X).mp hX
      exact σx_commutant_subset_span X hComm
    · intro hX
      -- If X ∈ span{I, σ_x}, then X = aI + bσ_x for some a, b
      -- Both I and σ_x are in the commutant
      simp only [σxCommutantSubmodule, Submodule.mem_span_insert] at hX
      obtain ⟨a, Z, hZ, hX⟩ := hX
      simp only [Submodule.mem_span_singleton] at hZ
      obtain ⟨b, hZ'⟩ := hZ
      rw [hX, ← hZ']
      -- Show a•1 + b•σ_x is in the commutant
      have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ commutantSubmodule (alignedL ω γ) :=
        one_mem_commutant (alignedL ω γ)
      have hσx : σx ∈ commutantSubmodule (alignedL ω γ) := by
        simp only [commutantSubmodule, Submodule.mem_mk, Set.mem_setOf_eq]
        exact (alignedL_commutant_eq_σx_commutant ω γ hω hγ σx).mpr (commutator_self σx)
      exact (commutantSubmodule (alignedL ω γ)).add_mem
        ((commutantSubmodule (alignedL ω γ)).smul_mem a h1)
        ((commutantSubmodule (alignedL ω γ)).smul_mem b hσx)

  -- Step 2: Compute the deficiency
  unfold quantumDeficiency
  rw [← commutant_dim_eq_stationary_dim, hCommEq, finrank_σxCommutant]

end DefectCRN.Quantum.Examples.AccidentalSymmetry
