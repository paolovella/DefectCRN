/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Quantum CRN Theory - Basic Definitions

This file provides fundamental definitions for quantum chemical reaction network theory,
extending classical CRNT to open quantum systems governed by Lindblad dynamics.

## Main definitions

* `commutator` - The commutator [A, B] = AB - BA
* `anticommutator` - The anticommutator {A, B} = AB + BA
* `dagger` - Conjugate transpose (Hermitian adjoint)

## References

* Lindblad, G. "On the generators of quantum dynamical semigroups" (1976)
* Gorini, Kossakowski, Sudarshan "Completely positive dynamical semigroups" (1976)
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators ComplexConjugate
open Matrix

variable {n m k : ℕ}

/-! ## Basic Operations -/

/-- Commutator [A, B] = AB - BA -/
noncomputable def commutator (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- Anticommutator {A, B} = AB + BA -/
noncomputable def anticommutator (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B + B * A

/-- Conjugate transpose (dagger / Hermitian adjoint) -/
abbrev dagger (A : Matrix (Fin n) (Fin m) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  A.conjTranspose

/-- Notation for commutator -/
scoped notation "⟦" A ", " B "⟧" => commutator A B

/-- Notation for anticommutator -/
scoped notation "⟨" A ", " B "⟩₊" => anticommutator A B

/-- Notation for dagger -/
postfix:max "†" => dagger

/-! ## Commutator Properties -/

@[simp]
theorem commutator_self (A : Matrix (Fin n) (Fin n) ℂ) : ⟦A, A⟧ = 0 := by
  simp only [commutator, sub_self]

theorem commutator_antisymm (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A, B⟧ = -⟦B, A⟧ := by
  simp only [commutator, neg_sub]

theorem commutator_add_left (A B C : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A + B, C⟧ = ⟦A, C⟧ + ⟦B, C⟧ := by
  simp only [commutator, add_mul, mul_add]
  abel

theorem commutator_add_right (A B C : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A, B + C⟧ = ⟦A, B⟧ + ⟦A, C⟧ := by
  simp only [commutator, add_mul, mul_add]
  abel

theorem commutator_smul_left (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⟦c • A, B⟧ = c • ⟦A, B⟧ := by
  simp only [commutator, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem commutator_smul_right (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A, c • B⟧ = c • ⟦A, B⟧ := by
  simp only [commutator, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Jacobi identity: [A, [B, C]] + [B, [C, A]] + [C, [A, B]] = 0 -/
theorem jacobi_identity (A B C : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A, ⟦B, C⟧⟧ + ⟦B, ⟦C, A⟧⟧ + ⟦C, ⟦A, B⟧⟧ = 0 := by
  simp only [commutator]
  -- After expansion, all 12 terms cancel pairwise
  noncomm_ring

/-- [X, A] = 0 implies [X, A * B] = A * [X, B] -/
theorem commutator_mul_left (X A B : Matrix (Fin n) (Fin n) ℂ)
    (hXA : ⟦X, A⟧ = 0) : ⟦X, A * B⟧ = A * ⟦X, B⟧ := by
  have hComm : X * A = A * X := sub_eq_zero.mp hXA
  simp only [commutator]
  -- Goal: X * (A * B) - (A * B) * X = A * (X * B - B * X)
  rw [← Matrix.mul_assoc X A B, hComm, Matrix.mul_assoc A X B]
  rw [Matrix.mul_assoc A B X]
  rw [← Matrix.mul_sub]

/-- [X, A] = 0 implies [X, B * A] = [X, B] * A -/
theorem commutator_mul_right (X A B : Matrix (Fin n) (Fin n) ℂ)
    (hXA : ⟦X, A⟧ = 0) : ⟦X, B * A⟧ = ⟦X, B⟧ * A := by
  have hComm : X * A = A * X := sub_eq_zero.mp hXA
  simp only [commutator]
  -- Goal: X * (B * A) - (B * A) * X = (X * B - B * X) * A
  -- LHS = X * B * A - B * A * X
  -- RHS = X * B * A - B * X * A
  -- We need B * A * X = B * X * A, which follows from A * X = X * A
  rw [← Matrix.mul_assoc X B A]
  rw [Matrix.mul_assoc B A X]
  have hAX : A * X = X * A := hComm.symm
  rw [hAX]
  rw [← Matrix.mul_assoc B X A]
  rw [← Matrix.sub_mul]

/-- If [X, A] = 0 then [X, A^n] = 0 for all n -/
theorem commutator_pow (X A : Matrix (Fin n) (Fin n) ℂ) (hXA : ⟦X, A⟧ = 0) :
    ∀ k : ℕ, ⟦X, A ^ k⟧ = 0 := by
  intro k
  induction k with
  | zero => simp [commutator]
  | succ k ih =>
    rw [pow_succ]
    rw [commutator_mul_right X A (A ^ k) hXA, ih, Matrix.zero_mul]

/-! ## Anticommutator Properties -/

@[simp]
theorem anticommutator_self (A : Matrix (Fin n) (Fin n) ℂ) :
    ⟨A, A⟩₊ = 2 • (A * A) := by
  simp only [anticommutator, two_smul]

theorem anticommutator_symm (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⟨A, B⟩₊ = ⟨B, A⟩₊ := by
  simp only [anticommutator, add_comm]

/-! ## Dagger Properties -/

@[simp]
theorem dagger_dagger (A : Matrix (Fin n) (Fin m) ℂ) : A†† = A := by
  simp only [dagger, conjTranspose_conjTranspose]

theorem dagger_mul (A : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin m) (Fin k) ℂ) :
    (A * B)† = B† * A† := by
  simp only [dagger, conjTranspose_mul]

theorem dagger_add (A B : Matrix (Fin n) (Fin m) ℂ) :
    (A + B)† = A† + B† := by
  simp only [dagger, conjTranspose_add]

theorem dagger_smul (c : ℂ) (A : Matrix (Fin n) (Fin m) ℂ) :
    (c • A)† = star c • A† := by
  simp only [dagger, conjTranspose_smul]

/-- Commutator of daggers: [A, B]† = [B†, A†] -/
theorem commutator_dagger (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⟦A, B⟧† = ⟦B†, A†⟧ := by
  simp only [commutator, dagger, conjTranspose_sub, conjTranspose_mul]

/-- If [X, A] = 0 and A is Hermitian, then [X†, A] = 0 -/
theorem commutator_dagger_hermitian (X A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hComm : ⟦X, A⟧ = 0) : ⟦X†, A⟧ = 0 := by
  -- [X, A] = 0 means XA = AX
  have hXA : X * A = A * X := by
    simp only [commutator] at hComm
    exact sub_eq_zero.mp hComm
  -- Taking adjoint: A†X† = X†A†, and since A = A†: AX† = X†A
  have hAdj : A * Xᴴ = Xᴴ * A := by
    have h := congr_arg conjTranspose hXA
    simp only [conjTranspose_mul] at h
    -- h : Aᴴ * Xᴴ = Xᴴ * Aᴴ
    rw [hA.eq] at h
    -- h : A * Xᴴ = Xᴴ * A... wait, hA.eq says A = Aᴴ, so rw gives: Aᴴ * Xᴴ = Xᴴ * Aᴴ → A * Xᴴ = Xᴴ * A
    -- But actually the rewrite replaces Aᴴ with A, so we get: A * Xᴴ = Xᴴ * A
    -- which is already in the right form!
    exact h
  -- So [X†, A] = X†A - AX† = AX† - AX† = 0
  simp only [commutator, dagger]
  rw [hAdj]
  simp only [sub_self]

/-- If [X, L] = 0 and [X, L†] = 0, then [X†, L] = 0 -/
theorem commutator_dagger_from_both (X L : Matrix (Fin n) (Fin n) ℂ)
    (hCommL : ⟦X, L⟧ = 0) (hCommLdag : ⟦X, L†⟧ = 0) : ⟦X†, L⟧ = 0 := by
  -- [X, L†] = 0 means XL† = L†X
  have hXLdag : X * Lᴴ = Lᴴ * X := by
    simp only [commutator, dagger] at hCommLdag
    exact sub_eq_zero.mp hCommLdag
  -- Taking adjoint: (XL†)† = (L†X)†, i.e., L X† = X† L
  have h : L * Xᴴ = Xᴴ * L := by
    have hadj := congr_arg conjTranspose hXLdag
    simp only [conjTranspose_mul, conjTranspose_conjTranspose] at hadj
    -- hadj : Xᴴ * L = L * Xᴴ, need L * Xᴴ = Xᴴ * L
    exact hadj
  simp only [commutator, dagger]
  rw [h]
  simp only [sub_self]

/-! ## Trace Properties -/

theorem trace_commutator (A B : Matrix (Fin n) (Fin n) ℂ) [DecidableEq (Fin n)] :
    (⟦A, B⟧).trace = 0 := by
  unfold commutator
  rw [trace_sub, trace_mul_comm, sub_self]

theorem trace_anticommutator (A B : Matrix (Fin n) (Fin n) ℂ) [DecidableEq (Fin n)] :
    (⟨A, B⟩₊).trace = 2 * (A * B).trace := by
  unfold anticommutator
  rw [trace_add, trace_mul_comm]
  ring

/-! ## Superoperator Basics -/

/-- A superoperator is a linear map on matrices -/
abbrev Superoperator (n : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ

/-- Identity superoperator -/
def idSuperop (n : ℕ) : Superoperator n := LinearMap.id

/-- Composition of superoperators -/
def compSuperop (S T : Superoperator n) : Superoperator n := S.comp T

/-! ## Positive Semidefinite and Faithful Density Matrices -/

/-- A Hermitian matrix is positive semidefinite if Re(v† ρ v) ≥ 0 for all v -/
def IsPosSemidef (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.IsHermitian ∧ ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ ρ.mulVec v).re

/-- A Hermitian matrix is positive definite if all eigenvalues are strictly positive.
    For our purposes, we define it as: for all nonzero v, Re(v† ρ v) > 0 -/
def IsPositiveDefinite (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.IsHermitian ∧ ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ ρ.mulVec v).re

/-- A density matrix is faithful if it is strictly positive definite -/
def IsFaithful (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsPositiveDefinite ρ

/-- Positive definite implies positive semidefinite -/
theorem IsPositiveDefinite.toPosSemidef {ρ : Matrix (Fin n) (Fin n) ℂ}
    (h : IsPositiveDefinite ρ) : IsPosSemidef ρ := by
  constructor
  · exact h.1
  · intro v
    by_cases hv : v = 0
    · simp [hv, mulVec, dotProduct]
    · exact le_of_lt (h.2 v hv)

/-! ## Hermitian Decomposition -/

/-- The Hermitian part of a matrix: (X + X†)/2 -/
noncomputable def hermitianPart (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1/2 : ℂ) • (X + X†)

/-- The anti-Hermitian part of a matrix: (X - X†)/2 -/
noncomputable def antiHermitianPart (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1/2 : ℂ) • (X - X†)

/-- The Hermitian part is Hermitian -/
theorem hermitianPart_isHermitian (X : Matrix (Fin n) (Fin n) ℂ) :
    (hermitianPart X).IsHermitian := by
  unfold hermitianPart
  rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add,
      conjTranspose_conjTranspose]
  simp only [dagger]
  -- star (1/2) = 1/2 since it's real
  have h : star (1/2 : ℂ) = 1/2 := by simp [Complex.star_def]
  rw [h, add_comm]

/-- The "imaginary" Hermitian part: -i times anti-Hermitian part is Hermitian -/
noncomputable def skewHermitianPart (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-Complex.I / 2) • (X - X†)

/-- The skew-Hermitian part is Hermitian -/
theorem skewHermitianPart_isHermitian (X : Matrix (Fin n) (Fin n) ℂ) :
    (skewHermitianPart X).IsHermitian := by
  unfold skewHermitianPart
  rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_sub,
      conjTranspose_conjTranspose]
  simp only [dagger, Complex.star_def, map_div₀, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  -- Goal: (I / 2) • (Xᴴ - X) = (-I / 2) • (X - Xᴴ)
  have hSub : X.conjTranspose - X = -(X - X.conjTranspose) := (neg_sub X X.conjTranspose).symm
  rw [hSub, smul_neg]
  -- Now: -((I / star 2) • (X - Xᴴ)) = (-I / 2) • (X - Xᴴ)
  rw [← neg_smul]
  -- Now: (-(I / star 2)) • (X - Xᴴ) = (-I / 2) • (X - Xᴴ)
  congr 1
  -- Need: -(I / star 2) = -I / 2
  rw [neg_div]
  congr 1
  simp [starRingEnd_apply]

/-- Any matrix X = hermitianPart X + i * skewHermitianPart X -/
theorem hermitian_decomposition (X : Matrix (Fin n) (Fin n) ℂ) :
    X = hermitianPart X + Complex.I • skewHermitianPart X := by
  unfold hermitianPart skewHermitianPart
  simp only [smul_smul]
  ring_nf
  simp only [Complex.I_sq, neg_neg, one_div, mul_comm Complex.I, Complex.div_I]
  ext i j
  simp only [dagger, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- If [X, A] = 0, then [X, c•A] = 0 -/
theorem commutator_smul_eq_zero (X A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (h : ⟦X, A⟧ = 0) : ⟦X, c • A⟧ = 0 := by
  rw [commutator_smul_right, h, smul_zero]

end DefectCRN.Quantum
