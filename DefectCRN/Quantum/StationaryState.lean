/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Lindbladian
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Stationary States of Lindblad Dynamics
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- The set of all stationary density matrices -/
def stationaryStateSet (L : Lindbladian n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {ρ | ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ}

/-- Real scalar multiplication preserves Hermiticity -/
theorem hermitian_smul_real {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (r : ℝ) :
    ((r : ℂ) • M).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, hM.eq]

/-- Positive semidefinite matrices are closed under nonneg real scalar mult -/
theorem posSemidef_smul_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsPosSemidef M)
    (r : ℝ) (hr : 0 ≤ r) : IsPosSemidef ((r : ℂ) • M) := by
  constructor
  · exact hermitian_smul_real hM.1 r
  · intro v
    -- ((r : ℂ) • M).mulVec v = (r : ℂ) • M.mulVec v
    have h1 : ((r : ℂ) • M).mulVec v = (r : ℂ) • M.mulVec v := by
      ext i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
      rw [Finset.mul_sum]
      congr 1
      ext x
      ring
    -- star v ⬝ᵥ (r • w) = r * (star v ⬝ᵥ w)
    have h2 : star v ⬝ᵥ ((r : ℂ) • M.mulVec v) = (r : ℂ) * (star v ⬝ᵥ M.mulVec v) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      congr 1
      ext x
      ring
    rw [h1, h2]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hr (hM.2 v)

/-- Positive semidefinite matrices form a convex cone -/
theorem posSemidef_add {M N : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsPosSemidef M) (hN : IsPosSemidef N) : IsPosSemidef (M + N) := by
  constructor
  · exact Matrix.IsHermitian.add hM.1 hN.1
  · intro v
    simp only [add_mulVec, dotProduct_add, Complex.add_re]
    exact add_nonneg (hM.2 v) (hN.2 v)

/-- The set of stationary states is convex -/
theorem stationary_state_convex (L : Lindbladian n) :
    Convex ℝ (stationaryStateSet L) := by
  -- Convex 𝕜 s := ∀ x ∈ s, ∀ y ∈ s, ∀ a b, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s
  intro x hx y hy a b ha hb hab
  simp only [stationaryStateSet, Set.mem_setOf_eq] at hx hy ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Hermiticity: a•x + b•y is Hermitian
    exact Matrix.IsHermitian.add (hermitian_smul_real hx.1 a) (hermitian_smul_real hy.1 b)
  · -- Positive semidefinite: convex combination of PSD is PSD
    exact posSemidef_add (posSemidef_smul_nonneg hx.2.1 a ha) (posSemidef_smul_nonneg hy.2.1 b hb)
  · -- Trace = 1: Tr(a•x + b•y) = a•Tr(x) + b•Tr(y) = a + b = 1
    rw [trace_add, trace_smul, trace_smul, hx.2.2.1, hy.2.2.1]
    -- a • (1 : ℂ) + b • (1 : ℂ) = a + b = 1
    -- ℝ-scalar mult on ℂ: a • c = (a : ℂ) * c
    have ha1 : (a : ℝ) • (1 : ℂ) = (a : ℂ) := by simp [Algebra.smul_def]
    have hb1 : (b : ℝ) • (1 : ℂ) = (b : ℂ) := by simp [Algebra.smul_def]
    rw [ha1, hb1, ← Complex.ofReal_add, Complex.ofReal_eq_one]
    exact hab
  · -- Stationarity: L(a•x + b•y) = a•L(x) + b•L(y) = 0
    have hSx := hx.2.2.2
    have hSy := hy.2.2.2
    unfold Lindbladian.IsStationaryState at hSx hSy ⊢
    -- For ℝ-scalars on ℂ-matrices, a • M = (a : ℂ) • M
    have ha' : a • x = (a : ℂ) • x := by rfl
    have hb' : b • y = (b : ℂ) • y := by rfl
    rw [L.apply_add, ha', hb', L.apply_smul, L.apply_smul, hSx, hSy]
    simp only [smul_zero, add_zero]

/-- The subspace of traceless matrices -/
noncomputable def tracelessSubspace (n : ℕ) [NeZero n] : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin n) ℂ ℂ)

/-- The range of a Lindbladian is contained in traceless matrices -/
theorem lindbladian_range_traceless (L : Lindbladian n) :
    LinearMap.range L.toLinearMap ≤ tracelessSubspace n := by
  intro M hM
  obtain ⟨ρ, hρ⟩ := hM
  simp only [tracelessSubspace, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
  rw [← hρ]
  exact L.trace_preserving ρ

/-- The kernel of L has dimension at least 1 -/
theorem stationary_subspace_nontrivial (L : Lindbladian n) :
    Module.finrank ℂ L.stationarySubspace ≥ 1 := by
  -- L maps n² dimensional space to traceless matrices (n² - 1 dimensional)
  -- By rank-nullity, ker(L) has dimension ≥ 1
  have hRN := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
  -- L.stationarySubspace is exactly the kernel
  have hKer : L.stationarySubspace = LinearMap.ker L.toLinearMap := rfl
  rw [← hKer] at hRN
  -- dim(Matrix) = n * n
  have hDimMatrix : Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) = n * n := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one]
    simp only [Fintype.card_fin]
  -- The range of L is contained in traceless matrices
  have hRange := lindbladian_range_traceless L
  have hRangeLe : Module.finrank ℂ (LinearMap.range L.toLinearMap) ≤
      Module.finrank ℂ (tracelessSubspace n) := Submodule.finrank_mono hRange
  -- The traceless subspace has dimension < n² (since trace is non-zero and surjective)
  have hDimTraceless : Module.finrank ℂ (tracelessSubspace n) < n * n := by
    -- trace is surjective: trace(diag(c,0,...,0)) = c
    have hSurj : Function.Surjective (Matrix.traceLinearMap (Fin n) ℂ ℂ) := by
      intro c
      use Matrix.diagonal (fun i => if i = 0 then c else 0)
      simp only [Matrix.traceLinearMap_apply, Matrix.trace_diagonal, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    have hInjRange := LinearMap.range_eq_top.mpr hSurj
    have hRankNullityTrace := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin n) ℂ ℂ)
    -- range = top, so finrank(range) = finrank(ℂ) = 1
    have hRangeFinrank : Module.finrank ℂ (LinearMap.range (Matrix.traceLinearMap (Fin n) ℂ ℂ)) = 1 := by
      rw [hInjRange, finrank_top]
      exact Module.finrank_self ℂ
    rw [hRangeFinrank, hDimMatrix] at hRankNullityTrace
    simp only [tracelessSubspace]
    have hn : n * n ≥ 1 := by
      have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      omega
    omega
  -- Combine: finrank(ker L) = n² - finrank(range L) ≥ n² - (n² - 1) = 1
  rw [hDimMatrix] at hRN
  omega

/-- Every Lindbladian has at least one stationary state.

    Proof approaches:
    1. **Semigroup approach**: The quantum dynamical semigroup e^{tL} maps the
       compact convex set of density matrices to itself. By Brouwer fixed point
       theorem, there exists a fixed point ρ* with e^{tL}(ρ*) = ρ* for all t,
       hence L(ρ*) = 0.

    2. **Direct construction**: Starting from any nonzero element in ker(L),
       symmetrize to get Hermitian, take absolute value to get PSD, normalize
       to get trace 1. This requires spectral theory.

    This is marked as an axiom since it requires fixed point theory or
    spectral decomposition machinery. -/
theorem exists_stationary_state (L : Lindbladian n) :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ := by
  sorry

/-- Dimension of the stationary state space -/
noncomputable def stationaryDim (L : Lindbladian n) : ℕ :=
  Module.finrank ℂ L.stationarySubspace

end DefectCRN.Quantum
