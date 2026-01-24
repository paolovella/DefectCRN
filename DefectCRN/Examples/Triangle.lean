/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Triangle Example: The 3-Cycle

This file demonstrates the Onsager-Rayleigh variational framework
on the simplest non-trivial example: a triangle (3-cycle).

## Setup

```
    v₀
   /  \
  e₀   e₂
 ↓      ↑
v₁ --→ v₂
    e₁
```

Vertices: V = {v₀, v₁, v₂} = Fin 3
Edges: E = {e₀: v₀→v₁, e₁: v₁→v₂, e₂: v₂→v₀} = Fin 3

The incidence matrix B is:
```
       e₀  e₁  e₂
  v₀ [ -1   0   1 ]   (leaves via e₀, enters via e₂)
  v₁ [  1  -1   0 ]   (enters via e₀, leaves via e₁)
  v₂ [  0   1  -1 ]   (enters via e₁, leaves via e₂)
```

## Key Results

1. ker(B) = span{(1,1,1)} — the uniform circulation
2. For uniform weights w = (1,1,1), the optimal flux J* is proportional to (1,1,1)
3. The projection π(ω) extracts the "cyclic mode" from any ω

This is the prototypical example of Kirchhoff's theorem on electrical networks.
-/

namespace Triangle

open Finset BigOperators Matrix

/-- The vertex set: 3 vertices -/
abbrev V := Fin 3

/-- The edge set: 3 edges forming a cycle -/
abbrev E := Fin 3

/-- The incidence matrix for the triangle.
    B v e = +1 if e enters v, -1 if e leaves v, 0 otherwise.
    
    e₀: v₀ → v₁ (leaves v₀, enters v₁)
    e₁: v₁ → v₂ (leaves v₁, enters v₂)  
    e₂: v₂ → v₀ (leaves v₂, enters v₀) -/
def B : Matrix V E ℝ := ![
  ![-1,  0,  1],   -- v₀: source of e₀, target of e₂
  ![ 1, -1,  0],   -- v₁: target of e₀, source of e₁
  ![ 0,  1, -1]    -- v₂: target of e₁, source of e₂
]

/-- Column sums of B are zero (conservation at each edge) -/
theorem B_col_sum_zero : ∀ e : E, (∑ v : V, B v e) = 0 := by
  intro e
  fin_cases e <;> native_decide

/-- The uniform flux (1, 1, 1) -/
def uniformFlux : E → ℝ := fun _ => 1

/-- B · uniformFlux = 0: the uniform flux is a circulation -/
theorem uniform_in_ker : ∀ v : V, (∑ e : E, B v e * uniformFlux e) = 0 := by
  intro v
  simp only [uniformFlux, mul_one]
  fin_cases v <;> native_decide

/-- Any flux J in ker(B) is a scalar multiple of uniformFlux.
    This is because dim(ker(B)) = 1 for a connected graph with |E| = |V|. -/
theorem ker_is_span_uniform (J : E → ℝ) 
    (hJ : ∀ v : V, (∑ e : E, B v e * J e) = 0) :
    ∃ c : ℝ, ∀ e : E, J e = c * uniformFlux e := by
  -- From the three equations:
  -- v₀: -J₀ + J₂ = 0  ⟹  J₀ = J₂
  -- v₁:  J₀ - J₁ = 0  ⟹  J₀ = J₁
  -- v₂:  J₁ - J₂ = 0  ⟹  J₁ = J₂
  have h0 := hJ 0
  have h1 := hJ 1
  have h2 := hJ 2
  simp only [Fin.sum_univ_three, Fin.isValue] at h0 h1 h2
  simp only [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, 
             Matrix.head_cons] at h0 h1 h2
  -- h0: -1 * J 0 + 0 * J 1 + 1 * J 2 = 0, i.e., J 2 = J 0
  -- h1:  1 * J 0 + (-1) * J 1 + 0 * J 2 = 0, i.e., J 0 = J 1
  -- h2:  0 * J 0 + 1 * J 1 + (-1) * J 2 = 0, i.e., J 1 = J 2
  use J 0
  intro e
  simp only [uniformFlux, mul_one]
  fin_cases e
  · rfl
  · linarith
  · linarith

/-- Uniform weights -/
def w : E → ℝ := fun _ => 1

/-- Weights are positive -/
theorem w_pos : ∀ e : E, w e > 0 := by
  intro e; simp only [w]; norm_num

/-- The weighted Laplacian for the triangle with uniform weights.
    L = B W B^T where W = diag(w).
    
    For uniform w = 1:
    L = B B^T = 
    [  2  -1  -1 ]
    [ -1   2  -1 ]
    [ -1  -1   2 ]
    
    This is the standard graph Laplacian of the triangle. -/
def L : Matrix V V ℝ := ![
  ![ 2, -1, -1],
  ![-1,  2, -1],
  ![-1, -1,  2]
]

/-- L = B W B^T (verification) -/
theorem L_eq_BWBt : L = B * (Matrix.diagonal w) * Bᵀ := by
  ext i j
  simp only [L, B, w, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> native_decide

/-- The constant vector is in ker(L) -/
theorem const_in_ker_L : ∀ v : V, (∑ v' : V, L v v') = 0 := by
  intro v
  fin_cases v <;> native_decide

/-- The Onsager-Rayleigh functional for the triangle:
    F(J) = (1/2) ∑ J_e²/w_e - ∑ ω_e J_e 
    
    For uniform w = 1:
    F(J) = (1/2)(J₀² + J₁² + J₂²) - (ω₀ J₀ + ω₁ J₁ + ω₂ J₂) -/
def onsagerRayleigh (ω J : E → ℝ) : ℝ :=
  (1/2) * (∑ e : E, J e * J e / w e) - (∑ e : E, ω e * J e)

/-- For the triangle, the optimal flux is J* = c · (1,1,1) where
    c = (ω₀ + ω₁ + ω₂) / 3
    
    This is the projection of ω onto the cyclic mode. -/
def optimalFluxCoeff (ω : E → ℝ) : ℝ :=
  (ω 0 + ω 1 + ω 2) / 3

/-- The optimal flux -/
def optimalFlux (ω : E → ℝ) : E → ℝ :=
  fun e => optimalFluxCoeff ω * uniformFlux e

/-- The optimal flux simplifies to the constant (ω₀ + ω₁ + ω₂)/3 -/
theorem optimalFlux_eq (ω : E → ℝ) (e : E) : 
    optimalFlux ω e = (ω 0 + ω 1 + ω 2) / 3 := by
  simp only [optimalFlux, optimalFluxCoeff, uniformFlux, mul_one]

/-- The optimal flux is in ker(B) -/
theorem optimalFlux_in_ker (ω : E → ℝ) : 
    ∀ v : V, (∑ e : E, B v e * optimalFlux ω e) = 0 := by
  intro v
  have h : ∃ c, ∀ e, optimalFlux ω e = c * uniformFlux e := by
    use optimalFluxCoeff ω
    intro e; rfl
  obtain ⟨c, hc⟩ := h
  simp_rw [hc]
  have := uniform_in_ker
  simp only [uniformFlux, mul_one] at this
  calc ∑ e : E, B v e * (c * 1) 
      = c * ∑ e : E, B v e := by rw [← Finset.mul_sum]; ring_nf
    _ = c * 0 := by rw [this v]
    _ = 0 := by ring

/-- KKT condition: at optimum, J*/w = π(ω) where π projects onto ker(BW).
    For uniform w, this means J* = ω projected onto span{(1,1,1)}.
    
    The stationarity condition is: J*/w - ω ∈ im(B^T)
    i.e., there exists λ such that J_e/w_e = ω_e + (B^T λ)_e -/
theorem optimalFlux_stationarity (ω : E → ℝ) :
    ∃ λ : V → ℝ, ∀ e : E, 
      optimalFlux ω e / w e = ω e + (∑ v : V, B v e * λ v) := by
  -- The Lagrange multiplier λ adjusts ω to its cyclic projection
  -- For the triangle: λ_v = (mean - ω_v') where adjustment needed
  let c := optimalFluxCoeff ω
  -- λ such that B^T λ = c - ω (on each edge)
  -- Actually we need: c = ω_e + (B^T λ)_e
  -- i.e., (B^T λ)_e = c - ω_e
  -- 
  -- For edge e₀ (v₀→v₁): (B^T λ)₀ = -λ₀ + λ₁ = c - ω₀
  -- For edge e₁ (v₁→v₂): (B^T λ)₁ = -λ₁ + λ₂ = c - ω₁
  -- For edge e₂ (v₂→v₀): (B^T λ)₂ = -λ₂ + λ₀ = c - ω₂
  -- 
  -- Adding: 0 = 3c - (ω₀ + ω₁ + ω₂) ✓ (consistent!)
  -- 
  -- Solution: λ₀ = 0, λ₁ = c - ω₀, λ₂ = 2c - ω₀ - ω₁
  use fun v => match v with
    | 0 => 0
    | 1 => c - ω 0
    | 2 => 2*c - ω 0 - ω 1
  intro e
  simp only [optimalFlux, optimalFluxCoeff, uniformFlux, w, mul_one, div_one]
  simp only [Fin.sum_univ_three, Fin.isValue]
  simp only [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  fin_cases e <;> ring

/-- The optimal flux minimizes the Onsager-Rayleigh functional over ker(B).
    
    For any J ∈ ker(B), we have F(J*) ≤ F(J), with equality iff J = J*. -/
theorem optimalFlux_minimizes (ω J : E → ℝ) 
    (hJ : ∀ v : V, (∑ e : E, B v e * J e) = 0) :
    onsagerRayleigh ω (optimalFlux ω) ≤ onsagerRayleigh ω J := by
  -- J ∈ ker(B) implies J = c · (1,1,1) for some c
  obtain ⟨c, hc⟩ := ker_is_span_uniform J hJ
  -- J* = c* · (1,1,1) where c* = (ω₀ + ω₁ + ω₂)/3
  let cstar := optimalFluxCoeff ω
  -- F(J) = (1/2) · 3c² - (ω₀ + ω₁ + ω₂)c = (3/2)c² - 3·c*·c
  -- F(J*) = (3/2)c*² - 3·c*·c* = -(3/2)c*²
  -- F(J) - F(J*) = (3/2)c² - 3·c*·c + (3/2)c*² = (3/2)(c - c*)²  ≥ 0
  simp only [onsagerRayleigh, optimalFlux, optimalFluxCoeff, uniformFlux, w, mul_one, div_one]
  simp only [Fin.sum_univ_three, Fin.isValue]
  simp_rw [hc]
  simp only [uniformFlux, mul_one]
  -- Now just algebra: (3/2)c*² - 3c*·c* ≤ (3/2)c² - 3c*·c
  have h : (1/2) * (cstar * cstar + cstar * cstar + cstar * cstar) - 
           (ω 0 * cstar + ω 1 * cstar + ω 2 * cstar) ≤
           (1/2) * (c * c + c * c + c * c) - 
           (ω 0 * c + ω 1 * c + ω 2 * c) := by
    -- cstar = (ω 0 + ω 1 + ω 2) / 3
    have hcstar : cstar = (ω 0 + ω 1 + ω 2) / 3 := rfl
    -- LHS = (3/2)c*² - (ω₀+ω₁+ω₂)c* = (3/2)c*² - 3c*·c* = -(3/2)c*²
    -- RHS = (3/2)c² - (ω₀+ω₁+ω₂)c = (3/2)c² - 3c*·c
    -- RHS - LHS = (3/2)c² - 3c*c + (3/2)c*² = (3/2)(c² - 2c*c + c*²) = (3/2)(c-c*)² ≥ 0
    have key : (1/2) * (c * c + c * c + c * c) - (ω 0 * c + ω 1 * c + ω 2 * c) -
               ((1/2) * (cstar * cstar + cstar * cstar + cstar * cstar) - 
                (ω 0 * cstar + ω 1 * cstar + ω 2 * cstar)) =
               (3/2) * (c - cstar) * (c - cstar) := by
      rw [hcstar]; ring
    have sq_nonneg : 0 ≤ (3/2) * (c - cstar) * (c - cstar) := by
      apply mul_nonneg
      · norm_num
      · apply mul_self_nonneg
    linarith
  exact h

/-- Uniqueness: if J ∈ ker(B) achieves the minimum, then J = J* -/
theorem optimalFlux_unique (ω J : E → ℝ)
    (hJ : ∀ v : V, (∑ e : E, B v e * J e) = 0)
    (hmin : onsagerRayleigh ω J = onsagerRayleigh ω (optimalFlux ω)) :
    J = optimalFlux ω := by
  -- J = c · (1,1,1), J* = c* · (1,1,1)
  -- F(J) = F(J*) implies (3/2)(c - c*)² = 0, hence c = c*
  obtain ⟨c, hc⟩ := ker_is_span_uniform J hJ
  let cstar := optimalFluxCoeff ω
  -- From the equality F(J) = F(J*), we get c = c*
  have hceq : c = cstar := by
    simp only [onsagerRayleigh, optimalFlux, optimalFluxCoeff, uniformFlux, w, 
               mul_one, div_one, Fin.sum_univ_three, Fin.isValue] at hmin
    simp_rw [hc, uniformFlux, mul_one] at hmin
    have hcstar : cstar = (ω 0 + ω 1 + ω 2) / 3 := rfl
    -- From hmin, derive c = cstar
    have key : (1/2) * (c * c + c * c + c * c) - (ω 0 * c + ω 1 * c + ω 2 * c) =
               (1/2) * (cstar * cstar + cstar * cstar + cstar * cstar) - 
               (ω 0 * cstar + ω 1 * cstar + ω 2 * cstar) := hmin
    have expand : (3/2) * (c - cstar) * (c - cstar) = 0 := by
      have h1 : (1/2) * (c * c + c * c + c * c) - (ω 0 * c + ω 1 * c + ω 2 * c) -
                ((1/2) * (cstar * cstar + cstar * cstar + cstar * cstar) - 
                 (ω 0 * cstar + ω 1 * cstar + ω 2 * cstar)) =
                (3/2) * (c - cstar) * (c - cstar) := by rw [hcstar]; ring
      linarith
    have sq_zero : (c - cstar) * (c - cstar) = 0 := by linarith
    have diff_zero : c - cstar = 0 := by
      rcases eq_or_ne (c - cstar) 0 with h | h
      · exact h
      · have := mul_self_pos.mpr h
        linarith
    linarith
  -- Now J e = c = cstar = optimalFlux ω e
  funext e
  rw [hc e, hceq]
  simp only [optimalFlux, uniformFlux, mul_one]

/-!
## Summary

For the triangle (3-cycle) with uniform weights w = (1,1,1):

1. **Kernel structure**: ker(B) = ℝ · (1,1,1) — one-dimensional, spanned by uniform circulation

2. **Optimal flux**: J* = ((ω₀ + ω₁ + ω₂)/3, (ω₀ + ω₁ + ω₂)/3, (ω₀ + ω₁ + ω₂)/3)
   This is the projection of the driving force ω onto the cyclic mode.

3. **KKT conditions**: J*/w - ω ∈ im(B^T), with explicit Lagrange multipliers.

4. **Optimality**: J* minimizes F(J) = (1/2)⟨J,J⟩_{W⁻¹} - ⟨ω,J⟩ over ker(B).

5. **Uniqueness**: J* is the unique minimizer.

This is the simplest instance of Kirchhoff's network theorem:
- The "voltage" ω drives a current J through the cycle
- The current distributes to minimize dissipation
- For a single cycle, this means uniform flow

The triangle serves as a "unit test" for the Onsager-Rayleigh framework:
every theorem from Basic.lean can be verified explicitly with matrices.
-/

end Triangle
