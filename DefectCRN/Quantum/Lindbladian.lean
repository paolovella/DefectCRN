/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Basic

/-!
# Lindblad Generator

This file defines the Lindblad superoperator, the generator of quantum
Markov semigroups for open quantum systems.

## Main definitions

* `Lindbladian` - Structure containing Hamiltonian H and jump operators Lₖ
* `Lindbladian.apply` - The Lindblad superoperator L(ρ)

## Main results

* `Lindbladian.trace_preserving` - Tr(L(ρ)) = 0
* `Lindbladian.hermiticity_preserving` - L(ρ)† = L(ρ) when ρ is Hermitian

## References

* Lindblad, G. "On the generators of quantum dynamical semigroups" (1976)
* Gorini, Kossakowski, Sudarshan "Completely positive dynamical semigroups" (1976)
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators ComplexConjugate
open Matrix

variable {n : ℕ} [NeZero n]

/-! ## Lindbladian Structure -/

/-- A Lindblad generator consists of a Hamiltonian and a list of jump operators -/
structure Lindbladian (n : ℕ) where
  /-- System Hamiltonian (must be Hermitian) -/
  hamiltonian : Matrix (Fin n) (Fin n) ℂ
  /-- Proof that Hamiltonian is Hermitian -/
  hamiltonian_hermitian : hamiltonian.IsHermitian
  /-- List of jump (Lindblad) operators -/
  jumpOps : List (Matrix (Fin n) (Fin n) ℂ)

namespace Lindbladian

variable (L : Lindbladian n)

/-! ## Component Parts -/

/-- The Hamiltonian (unitary) part: -i[H, ρ] -/
noncomputable def unitaryPart (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -Complex.I • ⟦L.hamiltonian, ρ⟧

/-- Single dissipator term for one jump operator: LρL† - ½{L†L, ρ} -/
noncomputable def singleDissipator (Lk : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Lk * ρ * Lk† - (1/2 : ℂ) • ⟨Lk† * Lk, ρ⟩₊

/-- The dissipative part: Σₖ (LₖρLₖ† - ½{Lₖ†Lₖ, ρ}) -/
noncomputable def dissipator (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  L.jumpOps.foldl (fun acc Lk => acc + singleDissipator Lk ρ) 0

/-- The full Lindblad superoperator L(ρ) = -i[H,ρ] + Σₖ(LₖρLₖ† - ½{Lₖ†Lₖ,ρ}) -/
noncomputable def apply (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  L.unitaryPart ρ + L.dissipator ρ

/-! ## Single Dissipator Properties -/

/-- Single dissipator is additive in ρ -/
theorem singleDissipator_add (Lk ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    singleDissipator Lk (ρ + σ) = singleDissipator Lk ρ + singleDissipator Lk σ := by
  simp only [singleDissipator, anticommutator]
  simp only [mul_add, add_mul, smul_add]
  abel

/-- Single dissipator respects scalar multiplication -/
theorem singleDissipator_smul (c : ℂ) (Lk ρ : Matrix (Fin n) (Fin n) ℂ) :
    singleDissipator Lk (c • ρ) = c • singleDissipator Lk ρ := by
  simp only [singleDissipator, anticommutator]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]
  simp only [smul_comm c (1/2 : ℂ)]

/-- Single dissipator has zero trace -/
theorem singleDissipator_trace (Lk ρ : Matrix (Fin n) (Fin n) ℂ) [DecidableEq (Fin n)] :
    (singleDissipator Lk ρ).trace = 0 := by
  simp only [singleDissipator]
  rw [trace_sub, trace_smul]
  -- Tr(LρL†) = Tr(L†Lρ) by cyclic property of trace
  have h1 : (Lk * ρ * Lk†).trace = (Lk† * Lk * ρ).trace := by
    rw [Matrix.trace_mul_cycle, mul_assoc]
  -- Tr({L†L, ρ}) = 2·Tr(L†Lρ) by trace of anticommutator
  have h2 : (⟨Lk† * Lk, ρ⟩₊).trace = 2 * (Lk† * Lk * ρ).trace := by
    rw [trace_anticommutator, Matrix.trace_mul_cycle]
  rw [h1, h2]
  simp only [one_div, smul_eq_mul]
  ring

/-- Single dissipator preserves Hermiticity -/
theorem singleDissipator_hermitian (Lk ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : (singleDissipator Lk ρ).IsHermitian := by
  simp only [singleDissipator, anticommutator]
  apply Matrix.IsHermitian.sub
  · -- (Lk * ρ * Lk†)† = Lk * ρ† * Lk† = Lk * ρ * Lk†
    rw [Matrix.IsHermitian]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [hρ.eq, mul_assoc]
  · -- (½ • (Lk†Lk ρ + ρ Lk†Lk))† = ½ • ...
    rw [Matrix.IsHermitian]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
               conjTranspose_conjTranspose, dagger]
    -- star (1/2) = 1/2 since 1/2 is real
    have h12 : star (1/2 : ℂ) = 1/2 := by simp [Complex.star_def]
    rw [h12, hρ.eq]
    -- ρ * (Lk† * Lk) + Lk† * Lk * ρ = Lk† * Lk * ρ + ρ * (Lk† * Lk)
    rw [add_comm]

/-! ## Fold Lemmas for Dissipator -/

-- General lemma: fold starting from init equals init + fold starting from 0
private theorem fold_add_init {α β : Type*} [AddCommMonoid β]
    (f : α → β) (init : β) (Ls : List α) :
    Ls.foldl (fun acc x => acc + f x) init = init + Ls.foldl (fun acc x => acc + f x) 0 := by
  induction Ls generalizing init with
  | nil => simp
  | cons x Ls ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih, ih (f x)]
    abel

-- General lemma: fold from (a + b) with additive f equals fold from a + fold from b
private theorem fold_split_init {α β : Type*} [AddCommMonoid β]
    (f g h : α → β) (hfgh : ∀ x, f x = g x + h x) (a b : β) (Ls : List α) :
    Ls.foldl (fun acc x => acc + f x) (a + b) =
    Ls.foldl (fun acc x => acc + g x) a + Ls.foldl (fun acc x => acc + h x) b := by
  induction Ls generalizing a b with
  | nil => simp
  | cons x Ls ih =>
    simp only [List.foldl_cons]
    have heq : a + b + f x = (a + g x) + (b + h x) := by rw [hfgh]; ac_rfl
    rw [heq]
    exact ih (a + g x) (b + h x)

-- General lemma: if f = g + h pointwise, fold of f = fold of g + fold of h
private theorem fold_add_fun {α β : Type*} [AddCommMonoid β]
    (f g h : α → β) (hfgh : ∀ x, f x = g x + h x) (Ls : List α) :
    Ls.foldl (fun acc x => acc + f x) 0 =
    Ls.foldl (fun acc x => acc + g x) 0 + Ls.foldl (fun acc x => acc + h x) 0 := by
  have h := fold_split_init f g h hfgh 0 0 Ls
  simp only [add_zero] at h
  exact h

-- General lemma: fold with scalar mult pulls out scalar
private theorem fold_smul_fun {α : Type*} {β : Type*} [AddCommMonoid β] [Module ℂ β]
    (c : ℂ) (f : α → β) (Ls : List α) :
    Ls.foldl (fun acc x => acc + c • f x) 0 = c • Ls.foldl (fun acc x => acc + f x) 0 := by
  induction Ls with
  | nil => simp
  | cons x Ls ih =>
    simp only [List.foldl_cons, zero_add]
    rw [fold_add_init (c • f ·), fold_add_init (f ·), ih, smul_add]

-- General lemma: if trace of f x = 0 for all x, trace of fold = 0
private theorem fold_trace_zero {α : Type*}
    (f : α → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ x, (f x).trace = 0)
    (Ls : List α) [DecidableEq (Fin n)] :
    (Ls.foldl (fun acc x => acc + f x) 0).trace = 0 := by
  induction Ls with
  | nil => simp
  | cons x Ls ih =>
    simp only [List.foldl_cons, zero_add]
    rw [fold_add_init, trace_add, hf, zero_add, ih]

-- General lemma: if f x is Hermitian for all x, fold is Hermitian
private theorem fold_hermitian {α : Type*}
    (f : α → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ x, (f x).IsHermitian)
    (Ls : List α) :
    (Ls.foldl (fun acc x => acc + f x) 0).IsHermitian := by
  induction Ls with
  | nil => simp [Matrix.IsHermitian]
  | cons x Ls ih =>
    simp only [List.foldl_cons, zero_add]
    rw [fold_add_init]
    exact Matrix.IsHermitian.add (hf x) ih

/-- Helper: fold of dissipators is additive -/
theorem dissipator_fold_add (Ls : List (Matrix (Fin n) (Fin n) ℂ))
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    Ls.foldl (fun acc Lk => acc + singleDissipator Lk (ρ + σ)) 0 =
    Ls.foldl (fun acc Lk => acc + singleDissipator Lk ρ) 0 +
    Ls.foldl (fun acc Lk => acc + singleDissipator Lk σ) 0 := by
  exact fold_add_fun
    (fun Lk => singleDissipator Lk (ρ + σ))
    (fun Lk => singleDissipator Lk ρ)
    (fun Lk => singleDissipator Lk σ)
    (fun Lk => singleDissipator_add Lk ρ σ)
    Ls

/-- Helper: fold of dissipators respects scalar mult -/
theorem dissipator_fold_smul (c : ℂ) (Ls : List (Matrix (Fin n) (Fin n) ℂ))
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Ls.foldl (fun acc Lk => acc + singleDissipator Lk (c • ρ)) 0 =
    c • Ls.foldl (fun acc Lk => acc + singleDissipator Lk ρ) 0 := by
  -- Rewrite using singleDissipator_smul and apply fold_smul_fun
  have heq : (fun acc Lk => acc + singleDissipator Lk (c • ρ)) =
             (fun acc Lk => acc + c • singleDissipator Lk ρ) := by
    ext acc Lk
    rw [singleDissipator_smul]
  rw [heq]
  exact fold_smul_fun c (fun Lk => singleDissipator Lk ρ) Ls

/-- Helper: fold of dissipator traces is zero -/
theorem dissipator_fold_trace (Ls : List (Matrix (Fin n) (Fin n) ℂ))
    (ρ : Matrix (Fin n) (Fin n) ℂ) [DecidableEq (Fin n)] :
    (Ls.foldl (fun acc Lk => acc + singleDissipator Lk ρ) 0).trace = 0 := by
  exact fold_trace_zero
    (fun Lk => singleDissipator Lk ρ)
    (fun Lk => singleDissipator_trace Lk ρ)
    Ls

/-- Helper: fold of dissipators preserves Hermiticity -/
theorem dissipator_fold_hermitian (Ls : List (Matrix (Fin n) (Fin n) ℂ))
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.IsHermitian) :
    (Ls.foldl (fun acc Lk => acc + singleDissipator Lk ρ) 0).IsHermitian := by
  exact fold_hermitian
    (fun Lk => singleDissipator Lk ρ)
    (fun Lk => singleDissipator_hermitian Lk ρ hρ)
    Ls

/-! ## Linearity -/

theorem apply_add (ρ σ : Matrix (Fin n) (Fin n) ℂ) :
    L.apply (ρ + σ) = L.apply ρ + L.apply σ := by
  simp only [apply, unitaryPart, dissipator]
  rw [commutator_add_right, dissipator_fold_add, smul_add]
  abel

theorem apply_smul (c : ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    L.apply (c • ρ) = c • L.apply ρ := by
  simp only [apply, unitaryPart, dissipator]
  rw [commutator_smul_right, dissipator_fold_smul, smul_comm, smul_add]

/-- Lindbladian as a linear map on matrices -/
noncomputable def toLinearMap : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := L.apply
  map_add' := L.apply_add
  map_smul' := L.apply_smul

/-! ## Fundamental Properties -/

/-- The Lindblad superoperator preserves trace: Tr(L(ρ)) = 0 -/
theorem trace_preserving (ρ : Matrix (Fin n) (Fin n) ℂ) [DecidableEq (Fin n)] :
    (L.apply ρ).trace = 0 := by
  simp only [apply, unitaryPart, dissipator]
  rw [trace_add, trace_smul, trace_commutator, smul_zero, zero_add]
  exact dissipator_fold_trace L.jumpOps ρ

/-- The Lindblad superoperator preserves Hermiticity -/
theorem hermiticity_preserving (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : (L.apply ρ).IsHermitian := by
  simp only [apply, unitaryPart, dissipator]
  apply Matrix.IsHermitian.add
  · -- Unitary part: (-i[H, ρ])† = -i[H, ρ] when H, ρ Hermitian
    rw [Matrix.IsHermitian]
    simp only [conjTranspose_smul, commutator, conjTranspose_sub, conjTranspose_mul]
    rw [L.hamiltonian_hermitian.eq, hρ.eq]
    simp only [Complex.star_def, map_neg, Complex.conj_I]
    -- Goal: --i • (ρH - Hρ) = -i • (Hρ - ρH)
    simp only [neg_neg]
    -- Goal: i • (ρH - Hρ) = -i • (Hρ - ρH)
    -- Use: ρH - Hρ = -(Hρ - ρH) and (-c) • x = -(c • x)
    rw [show ρ * L.hamiltonian - L.hamiltonian * ρ = -(L.hamiltonian * ρ - ρ * L.hamiltonian)
        by simp only [neg_sub]]
    simp only [smul_neg, neg_smul]
  · -- Dissipator part: each term preserves Hermiticity
    exact dissipator_fold_hermitian L.jumpOps ρ hρ

/-! ## Stationary States -/

/-- A density matrix ρ is a stationary state if L(ρ) = 0 -/
def IsStationaryState (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  L.apply ρ = 0

/-- The kernel of L (space of stationary states) -/
noncomputable def stationarySubspace : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.ker L.toLinearMap

theorem mem_stationarySubspace_iff (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ρ ∈ L.stationarySubspace ↔ L.IsStationaryState ρ := by
  simp [stationarySubspace, IsStationaryState, LinearMap.mem_ker, toLinearMap]

/-- Zero is always a stationary "state" (not normalized) -/
theorem zero_stationary : L.IsStationaryState 0 := by
  simp only [IsStationaryState, apply, unitaryPart, dissipator, commutator]
  simp only [mul_zero, zero_mul, sub_self, smul_zero, zero_add]
  -- Each term in the fold is zero since singleDissipator _ 0 = 0
  have hSingle : ∀ Lk, singleDissipator Lk (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    intro Lk
    simp only [singleDissipator, anticommutator, mul_zero, zero_mul, add_zero, smul_zero, sub_zero]
  -- Prove the fold equals 0 by converting to sum
  have hFold : ∀ (Ls : List (Matrix (Fin n) (Fin n) ℂ)),
      Ls.foldl (fun acc Lk => acc + singleDissipator Lk 0) 0 = 0 := by
    intro Ls
    induction Ls with
    | nil => rfl
    | cons Lk Ls' ih =>
      simp only [List.foldl_cons, zero_add, hSingle]
      convert ih using 2
      simp [hSingle]
  exact hFold L.jumpOps

/-! ## Special Cases -/

/-- Pure Hamiltonian evolution (no dissipation) -/
def pureHamiltonian (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    Lindbladian n where
  hamiltonian := H
  hamiltonian_hermitian := hH
  jumpOps := []

/-- Pure dissipation (no Hamiltonian) -/
def pureDissipation (Ls : List (Matrix (Fin n) (Fin n) ℂ)) : Lindbladian n where
  hamiltonian := 0
  hamiltonian_hermitian := by simp [Matrix.IsHermitian]
  jumpOps := Ls

end Lindbladian

end DefectCRN.Quantum
