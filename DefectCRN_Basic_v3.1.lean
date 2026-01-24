/-
Defect Cohomology for Chemical Reaction Networks
Formal verification in Lean 4 / Mathlib

Main results:
- π : Ω¹ → ker(BW) is a well-defined projector
- π is W-self-adjoint: ⟨π ω, η⟩_W = ⟨ω, π η⟩_W
- H¹_W ≅ ker(BW) / im(Bᵀ) represented by π(Ω¹)

Author: Paolo Vella
Date: January 2026
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false

open scoped BigOperators Matrix
open Matrix Finset

namespace DefectCRN

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ## Basic definitions -/

def vertexSum (x : V → ℝ) : ℝ := ∑ v, x v

/-- The subspace 1^⊥ of functions summing to zero. -/
def onePerp : Submodule ℝ (V → ℝ) where
  carrier := {x | vertexSum x = 0}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, vertexSum] at *
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  zero_mem' := by simp [vertexSum]
  smul_mem' := fun c {x} hx => by
    simp only [Set.mem_setOf_eq, vertexSum] at *
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- Project to 1^⊥ by subtracting mean. -/
noncomputable def projOnePerp [NeZero (Fintype.card V)] (x : V → ℝ) : V → ℝ :=
  fun v => x v - (∑ u, x u) / (Fintype.card V : ℝ)

theorem projOnePerp_zero [NeZero (Fintype.card V)] : projOnePerp (0 : V → ℝ) = 0 := by
  funext v; simp [projOnePerp]

theorem projOnePerp_mem [NeZero (Fintype.card V)] (x : V → ℝ) :
    projOnePerp x ∈ onePerp (V := V) := by
  simp only [onePerp, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq, vertexSum]
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (Fintype.card V))
  show ∑ v : V, projOnePerp x v = 0
  simp only [projOnePerp, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem projOnePerp_idem [NeZero (Fintype.card V)] (x : V → ℝ)
    (hx : x ∈ onePerp (V := V)) : projOnePerp x = x := by
  simp only [onePerp, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq, vertexSum] at hx
  funext v; rw [projOnePerp, hx, zero_div, sub_zero]

/-! ## Matrix operations -/

def matMulVec' {α β : Type*} [Fintype β] (M : Matrix α β ℝ) (x : β → ℝ) : α → ℝ :=
  fun a => ∑ b, M a b * x b

/-- BW applied to edge function: (BW ω)_v = ∑_e B_{ve} w_e ω_e -/
def BW_apply (B : Matrix V E ℝ) (w : E → ℝ) (x : E → ℝ) : V → ℝ :=
  matMulVec' B (fun e => w e * x e)

/-- Bᵀ applied to vertex function: (Bᵀ φ)_e = ∑_v B_{ve} φ_v -/
def Bt_apply (B : Matrix V E ℝ) (φ : V → ℝ) : E → ℝ :=
  fun e => ∑ v, B v e * φ v

/-- L = BWBᵀ applied to vertex function -/
def L_apply (B : Matrix V E ℝ) (w : E → ℝ) (x : V → ℝ) : V → ℝ :=
  BW_apply B w (Bt_apply B x)

/-! ## Inner products -/

/-- W-weighted inner product on edges: ⟨ω, η⟩_W = ∑_e w_e ω_e η_e -/
def innerW (w : E → ℝ) (x y : E → ℝ) : ℝ := ∑ e, w e * x e * y e

/-- Standard inner product on vertices -/
def innerV (x y : V → ℝ) : ℝ := ∑ v, x v * y v

/-! ## Fundamental lemmas -/

theorem BW_apply_mem_onePerp (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0) (x : E → ℝ) :
    BW_apply B w x ∈ onePerp (V := V) := by
  simp only [onePerp, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq, vertexSum,
    BW_apply, matMulVec']
  calc ∑ v : V, ∑ e : E, B v e * (w e * x e)
      = ∑ e : E, ∑ v : V, B v e * (w e * x e) := Finset.sum_comm
    _ = ∑ e : E, (∑ v : V, B v e) * (w e * x e) := by congr 1; ext e; rw [Finset.sum_mul]
    _ = 0 := by simp [hBcol]

theorem L_apply_mem_onePerp (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0) (x : V → ℝ) :
    L_apply B w x ∈ onePerp (V := V) :=
  BW_apply_mem_onePerp B w hBcol (Bt_apply B x)

theorem Bt_apply_const (B : Matrix V E ℝ) (hBcol : ∀ e, (∑ v, B v e) = 0) (c : ℝ) :
    Bt_apply B (fun _ => c) = 0 := by
  funext e
  simp only [Bt_apply, Pi.zero_apply, ← Finset.sum_mul, hBcol, zero_mul]

theorem L_apply_eq_L_apply_proj [NeZero (Fintype.card V)] (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0) (φ : V → ℝ) :
    L_apply B w φ = L_apply B w (projOnePerp φ) := by
  funext v
  simp only [L_apply, BW_apply, matMulVec', Bt_apply, projOnePerp]
  congr 1; ext e
  have h1 : ∑ u : V, B u e * (φ u - (∑ x, φ x) / ↑(Fintype.card V)) =
            ∑ u : V, (B u e * φ u - B u e * ((∑ x, φ x) / ↑(Fintype.card V))) := by
    congr 1; ext u; ring
  rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hBcol, zero_mul, sub_zero]

/-! ## Laplacian inverse structure -/

/-- Inverse of L restricted to 1^⊥ -/
structure LaplacianInverse (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0) where
  inv : onePerp (V := V) →ₗ[ℝ] onePerp (V := V)
  left_inv : ∀ x : onePerp (V := V),
    (⟨L_apply B w (inv x).1, L_apply_mem_onePerp B w hBcol (inv x).1⟩ : onePerp (V := V)) = x
  right_inv : ∀ x : onePerp (V := V),
    inv ⟨L_apply B w x.1, L_apply_mem_onePerp B w hBcol x.1⟩ = x

/-! ## The projection π -/

/-- λ*(ω) = L⁻¹(proj(BW ω)) -/
noncomputable def lambdaStar (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) : V → ℝ :=
  (Linv.inv ⟨projOnePerp (BW_apply B w ω), projOnePerp_mem _⟩).1

/-- π(ω) = ω - Bᵀ λ*(ω) -/
noncomputable def piProj (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) : E → ℝ :=
  fun e => ω e - Bt_apply B (lambdaStar B w hBcol Linv ω) e

/-! ## Main theorems: π is a projector onto ker(BW) -/

/-- BW ∘ π = 0: π projects into ker(BW) -/
theorem piProj_in_kerBW (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) : BW_apply B w (piProj B w hBcol Linv ω) = 0 := by
  have hBW_mem : BW_apply B w ω ∈ onePerp (V := V) := BW_apply_mem_onePerp B w hBcol ω
  have hproj : projOnePerp (BW_apply B w ω) = BW_apply B w ω := projOnePerp_idem _ hBW_mem
  have hL : L_apply B w (lambdaStar B w hBcol Linv ω) = projOnePerp (BW_apply B w ω) := by
    have := Linv.left_inv ⟨projOnePerp (BW_apply B w ω), projOnePerp_mem _⟩
    exact congrArg Subtype.val this
  rw [hproj] at hL
  funext v
  simp only [piProj, BW_apply, matMulVec', Bt_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
  simp only [L_apply, BW_apply, matMulVec'] at hL
  have hLv := congrFun hL v
  simp only [matMulVec', Bt_apply] at hLv
  rw [hLv]; ring

/-- π ∘ Bᵀ = 0: π kills exact forms -/
theorem piProj_kills_exact (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (φ : V → ℝ) : piProj B w hBcol Linv (Bt_apply B φ) = 0 := by
  let φ' : onePerp (V := V) := ⟨projOnePerp φ, projOnePerp_mem φ⟩
  have hL_eq : L_apply B w φ = L_apply B w φ'.1 := L_apply_eq_L_apply_proj B w hBcol φ
  have hL_mem : L_apply B w φ ∈ onePerp (V := V) := L_apply_mem_onePerp B w hBcol φ
  have hproj_L : projOnePerp (L_apply B w φ) = L_apply B w φ := projOnePerp_idem _ hL_mem
  have hL'_mem : L_apply B w φ'.1 ∈ onePerp (V := V) := L_apply_mem_onePerp B w hBcol φ'.1
  have hproj_L' : projOnePerp (L_apply B w φ'.1) = L_apply B w φ'.1 := projOnePerp_idem _ hL'_mem
  have hBWBt : BW_apply B w (Bt_apply B φ) = L_apply B w φ := rfl
  have hls : lambdaStar B w hBcol Linv (Bt_apply B φ) = φ'.1 := by
    simp only [lambdaStar, hBWBt, hproj_L, hL_eq, hproj_L']
    have := Linv.right_inv φ'
    exact congrArg Subtype.val this
  funext e
  simp only [piProj, hls, Pi.zero_apply, Bt_apply, projOnePerp]
  have h1 : ∑ v : V, B v e * φ v - ∑ x : V, B x e * (φ x - (∑ u : V, φ u) / ↑(Fintype.card V)) =
            ∑ v : V, B v e * ((∑ u : V, φ u) / ↑(Fintype.card V)) := by
    have h2 : ∑ x : V, B x e * (φ x - (∑ u : V, φ u) / ↑(Fintype.card V)) =
              ∑ x : V, (B x e * φ x - B x e * ((∑ u : V, φ u) / ↑(Fintype.card V))) := by
      congr 1; ext x; ring
    rw [h2, Finset.sum_sub_distrib]; ring
  rw [h1, ← Finset.sum_mul, hBcol, zero_mul]

/-- π is identity on ker(BW) -/
theorem piProj_idem_on_ker (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (h : E → ℝ) (hh : BW_apply B w h = 0) :
    piProj B w hBcol Linv h = h := by
  have hproj : projOnePerp (BW_apply B w h) = 0 := by rw [hh]; exact projOnePerp_zero
  have hzero_mem : (0 : V → ℝ) ∈ onePerp (V := V) := onePerp.zero_mem
  have harg_eq : (⟨projOnePerp (BW_apply B w h), projOnePerp_mem _⟩ : onePerp (V := V)) =
                 ⟨0, hzero_mem⟩ := Subtype.ext hproj
  have hinv_zero : (Linv.inv ⟨0, hzero_mem⟩).1 = 0 := by
    have := Linv.inv.map_zero
    exact congrArg Subtype.val this
  have hls : lambdaStar B w hBcol Linv h = 0 := by
    simp only [lambdaStar, harg_eq, hinv_zero]
  funext e
  simp only [piProj, hls, Bt_apply]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

/-- π² = π: π is idempotent -/
theorem piProj_idempotent (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) :
    piProj B w hBcol Linv (piProj B w hBcol Linv ω) = piProj B w hBcol Linv ω := by
  apply piProj_idem_on_ker
  exact piProj_in_kerBW B w hBcol Linv ω

/-! ## W-self-adjointness of π -/

/-- ⟨Bᵀφ, ω⟩_W = ⟨φ, BW ω⟩ : adjointness of B and Bᵀ -/
theorem innerW_Bt_eq_innerV_BW (B : Matrix V E ℝ) (w : E → ℝ)
    (φ : V → ℝ) (ω : E → ℝ) :
    innerW w (Bt_apply B φ) ω = innerV φ (BW_apply B w ω) := by
  simp only [innerW, innerV, Bt_apply, BW_apply, matMulVec']
  calc ∑ e : E, w e * (∑ v : V, B v e * φ v) * ω e
      = ∑ e : E, (∑ v : V, w e * (B v e * φ v)) * ω e := by
        congr 1; ext e; rw [Finset.mul_sum]
    _ = ∑ e : E, ∑ v : V, w e * (B v e * φ v) * ω e := by
        congr 1; ext e; rw [Finset.sum_mul]
    _ = ∑ v : V, ∑ e : E, w e * (B v e * φ v) * ω e := Finset.sum_comm
    _ = ∑ v : V, φ v * ∑ e : E, B v e * (w e * ω e) := by
        congr 1; ext v; rw [Finset.mul_sum]; congr 1; ext e; ring

/-- innerW is symmetric -/
theorem innerW_symm (w : E → ℝ) (x y : E → ℝ) :
    innerW w x y = innerW w y x := by
  simp only [innerW]; congr 1; ext e; ring

/-- ⟨π ω, η⟩_W = ⟨ω, η⟩_W - ⟨λ*, BW η⟩ -/
theorem innerW_piProj_left (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω η : E → ℝ) :
    innerW w (piProj B w hBcol Linv ω) η =
    innerW w ω η - innerV (lambdaStar B w hBcol Linv ω) (BW_apply B w η) := by
  simp only [innerW, piProj, Bt_apply]
  have h1 : ∑ e : E, w e * (ω e - ∑ v : V, B v e * lambdaStar B w hBcol Linv ω v) * η e =
            ∑ e : E, (w e * ω e * η e - w e * (∑ v : V, B v e * lambdaStar B w hBcol Linv ω v) * η e) := by
    congr 1; ext e; ring
  rw [h1, Finset.sum_sub_distrib]
  congr 1
  calc ∑ e : E, w e * (∑ v : V, B v e * lambdaStar B w hBcol Linv ω v) * η e
      = ∑ e : E, (∑ v : V, w e * (B v e * lambdaStar B w hBcol Linv ω v)) * η e := by
        congr 1; ext e; rw [Finset.mul_sum]
    _ = ∑ e : E, ∑ v : V, w e * (B v e * lambdaStar B w hBcol Linv ω v) * η e := by
        congr 1; ext e; rw [Finset.sum_mul]
    _ = ∑ v : V, ∑ e : E, w e * (B v e * lambdaStar B w hBcol Linv ω v) * η e := Finset.sum_comm
    _ = ∑ v : V, lambdaStar B w hBcol Linv ω v * ∑ e : E, B v e * (w e * η e) := by
        congr 1; ext v; rw [Finset.mul_sum]; congr 1; ext e; ring
    _ = innerV (lambdaStar B w hBcol Linv ω) (BW_apply B w η) := by
        simp only [innerV, BW_apply, matMulVec']

/-- ⟨π ω, η⟩_W = ⟨ω, η⟩_W when BW η = 0 -/
theorem piProj_selfadj_on_ker (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω η : E → ℝ) (hη : BW_apply B w η = 0) :
    innerW w (piProj B w hBcol Linv ω) η = innerW w ω η := by
  rw [innerW_piProj_left, hη]
  simp only [innerV, BW_apply, matMulVec', Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

/-- Main theorem: ⟨π ω, π η⟩_W = ⟨ω, π η⟩_W (W-self-adjointness) -/
theorem piProj_W_selfadjoint (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω η : E → ℝ) :
    innerW w (piProj B w hBcol Linv ω) (piProj B w hBcol Linv η) =
    innerW w ω (piProj B w hBcol Linv η) := by
  apply piProj_selfadj_on_ker
  exact piProj_in_kerBW B w hBcol Linv η

/-- Corollary: ⟨π ω, η⟩_W = ⟨π ω, π η⟩_W -/
theorem piProj_W_selfadjoint' (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω η : E → ℝ) :
    innerW w (piProj B w hBcol Linv ω) η =
    innerW w (piProj B w hBcol Linv ω) (piProj B w hBcol Linv η) := by
  have h1 : innerW w (piProj B w hBcol Linv ω) η =
            innerW w η (piProj B w hBcol Linv ω) := innerW_symm w _ _
  have h2 : innerW w η (piProj B w hBcol Linv ω) =
            innerW w (piProj B w hBcol Linv η) (piProj B w hBcol Linv ω) := by
    rw [← piProj_W_selfadjoint]
  have h3 : innerW w (piProj B w hBcol Linv η) (piProj B w hBcol Linv ω) =
            innerW w (piProj B w hBcol Linv ω) (piProj B w hBcol Linv η) := innerW_symm w _ _
  rw [h1, h2, h3]

/-- Full self-adjointness: ⟨π ω, η⟩_W = ⟨ω, π η⟩_W -/
theorem piProj_W_selfadjoint_full (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω η : E → ℝ) :
    innerW w (piProj B w hBcol Linv ω) η = innerW w ω (piProj B w hBcol Linv η) := by
  rw [piProj_W_selfadjoint', piProj_W_selfadjoint]

/-! ## Onsager-Rayleigh Variational Principle -/

/-- W⁻¹-weighted inner product (dissipation metric) -/
def innerWinv (w : E → ℝ) (J K : E → ℝ) : ℝ := ∑ e, J e * K e / w e

/-- The Onsager-Rayleigh functional: F_ω(J) = ½⟨J,J⟩_{W⁻¹} - ⟨ω,J⟩ -/
noncomputable def onsagerRayleigh (w : E → ℝ) (ω J : E → ℝ) : ℝ :=
  (1/2) * innerWinv w J J - ∑ e, ω e * J e

/-- The optimal flux J* = W π(ω) -/
noncomputable def optimalFlux (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) : E → ℝ :=
  fun e => w e * piProj B w hBcol Linv ω e

/-- J* satisfies the conservation constraint BJ* = 0 -/
theorem optimalFlux_in_kerB (B : Matrix V E ℝ) (w : E → ℝ)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) : matMulVec' B (optimalFlux B w hBcol Linv ω) = 0 := by
  have hπ := piProj_in_kerBW B w hBcol Linv ω
  funext v
  simp only [optimalFlux, matMulVec', Pi.zero_apply]
  simp only [BW_apply, matMulVec'] at hπ
  have hv := congrFun hπ v
  simp only [Pi.zero_apply] at hv
  convert hv using 1
  congr 1; ext e; ring

/-- J* satisfies KKT stationarity: J*/w = ω - Bᵀλ* = π(ω) -/
theorem optimalFlux_stationarity (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, w e > 0)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) (e : E) :
    optimalFlux B w hBcol Linv ω e / w e = piProj B w hBcol Linv ω e := by
  simp only [optimalFlux]
  have hw_pos : w e ≠ 0 := ne_of_gt (hw e)
  field_simp

/-- Main theorem: J* = W π(ω) satisfies KKT conditions -/
theorem onsager_rayleigh_kkt (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, w e > 0)
    (hBcol : ∀ e, (∑ v, B v e) = 0)
    (Linv : LaplacianInverse B w hBcol) [NeZero (Fintype.card V)]
    (ω : E → ℝ) :
    let J := optimalFlux B w hBcol Linv ω
    let μ := lambdaStar B w hBcol Linv ω
    -- Primal feasibility: BJ = 0
    (matMulVec' B J = 0) ∧
    -- Stationarity: W⁻¹J - ω + Bᵀμ = 0, i.e., J = W(ω - Bᵀμ) = W π(ω)
    (∀ e, J e / w e - ω e + Bt_apply B μ e = 0) := by
  constructor
  · exact optimalFlux_in_kerB B w hBcol Linv ω
  · intro e
    simp only [optimalFlux, piProj, Bt_apply]
    have hw_pos : w e ≠ 0 := ne_of_gt (hw e)
    field_simp
    ring

end DefectCRN
