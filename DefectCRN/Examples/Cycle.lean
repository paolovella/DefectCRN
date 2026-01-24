/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic

/-!
# The n-Cycle: Generalization of the Triangle

This file demonstrates the Onsager-Rayleigh variational framework
on the n-cycle, generalizing the Triangle example.

## Setup

For n ≥ 2, the n-cycle has:
- Vertices: V = Fin n = {0, 1, ..., n-1}
- Edges: E = Fin n = {e₀, e₁, ..., e_{n-1}}
- Edge eᵢ goes from vertex i to vertex (i+1) mod n

```
For n = 4:
    v₀ ----e₀---→ v₁
     ↑             |
    e₃            e₁
     |             ↓
    v₃ ←---e₂---- v₂
```

The incidence matrix B is:
- B i i = -1  (edge i leaves vertex i)
- B ((i+1) mod n) i = +1  (edge i enters vertex (i+1) mod n)
- B j i = 0 otherwise

## Key Results

1. ker(B) = span{(1,1,...,1)} — dimension 1
2. The optimal flux J* = (mean of ω) · (1,1,...,1)
3. This is Kirchhoff's theorem for a single cycle

The n-cycle is the fundamental building block:
- Any graph's fluxes decompose into cycle contributions
- The Onsager-Rayleigh functional optimizes over cycle space
-/

namespace Cycle

open Finset BigOperators Matrix

variable (n : ℕ) [NeZero n]

/-- The vertex and edge sets for the n-cycle -/
abbrev V := Fin n
abbrev E := Fin n

/-- The incidence matrix for the n-cycle.
    Edge i goes from vertex i to vertex (i+1) mod n.
    
    B v e = -1 if v = e (edge leaves v)
    B v e = +1 if v = e + 1 mod n (edge enters v)
    B v e = 0 otherwise -/
def B : Matrix (V n) (E n) ℝ := fun v e =>
  if v = e then -1
  else if v = e + 1 then 1
  else 0

/-- Column sums of B are zero: each edge leaves one vertex and enters another -/
theorem B_col_sum_zero : ∀ e : E n, (∑ v : V n, B n v e) = 0 := by
  intro e
  simp only [B]
  -- Sum over all vertices: exactly one is e (contributes -1), one is e+1 (contributes +1)
  have h : ∑ v : Fin n, (if v = e then (-1 : ℝ) else if v = e + 1 then 1 else 0) = 
           (if e = e then -1 else if e = e + 1 then 1 else 0) +
           (if (e + 1) = e then -1 else if (e + 1) = e + 1 then 1 else 0) +
           ∑ v ∈ Finset.univ.filter (fun v => v ≠ e ∧ v ≠ e + 1), 
             (if v = e then (-1 : ℝ) else if v = e + 1 then 1 else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun v => v = e ∨ v = e + 1)]
    congr 1
    · -- Sum over {e, e+1}
      by_cases heq : e = e + 1
      · -- n = 1 case: e = e + 1
        simp only [Finset.filter_or, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, heq]
        simp only [Finset.union_idempotent, Finset.sum_singleton]
        simp only [↓reduceIte, add_zero]
      · -- n ≥ 2: e ≠ e + 1
        simp only [Finset.filter_or, Finset.filter_eq', Finset.mem_univ, ↓reduceIte]
        rw [Finset.sum_union]
        · simp only [Finset.sum_singleton, ↓reduceIte, heq]
        · simp only [Finset.disjoint_singleton_right, Finset.mem_singleton]
          exact heq
    · -- Sum over complement: all terms are 0
      apply Finset.sum_eq_zero
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hv
      simp only [hv.1, ↓reduceIte, hv.2]
  rw [h]
  simp only [↓reduceIte]
  by_cases heq : e = e + 1
  · simp only [heq, ↓reduceIte, add_zero]
    -- e = e + 1 means n = 1
    have : ∀ v, v ≠ e ∧ v ≠ e + 1 → False := by
      intro v ⟨h1, h2⟩
      rw [heq] at h1
      exact h1 h2
    simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    intro v
    by_contra hv
    push_neg at hv
    exact this v hv
  · simp only [heq, ↓reduceIte]
    have hsum : ∑ v ∈ Finset.univ.filter (fun v => v ≠ e ∧ v ≠ e + 1), 
                  (if v = e then (-1 : ℝ) else if v = e + 1 then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [hv.1, ↓reduceIte, hv.2]
    rw [hsum]
    ring

/-- The uniform flux: all edges carry flow 1 -/
def uniformFlux : E n → ℝ := fun _ => 1

/-- The uniform flux is in ker(B): it's a valid circulation -/
theorem uniform_in_ker : ∀ v : V n, (∑ e : E n, B n v e * uniformFlux n e) = 0 := by
  intro v
  simp only [uniformFlux, mul_one, B]
  -- At vertex v: edge v leaves (-1), edge (v-1) enters (+1)
  -- More precisely: edge (v-1) mod n enters v (since that edge goes to v)
  -- edge v leaves v
  have h : ∑ e : Fin n, (if v = e then (-1 : ℝ) else if v = e + 1 then 1 else 0) = 
           -1 + 1 := by
    -- The term for e = v contributes -1
    -- The term for e = v - 1 (i.e., e + 1 = v) contributes +1
    -- All other terms are 0
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun e => v = e ∨ v = e + 1)]
    have hrest : ∑ e ∈ Finset.univ.filter (fun e => ¬(v = e ∨ v = e + 1)), 
                   (if v = e then (-1 : ℝ) else if v = e + 1 then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, not_or, true_and] at he
      simp only [he.1, ↓reduceIte, he.2]
    rw [hrest, add_zero]
    -- Now sum over {e : v = e ∨ v = e + 1}
    by_cases h1 : ∃ e, v = e ∧ v = e + 1
    · -- v = e and v = e + 1, so e = e + 1, meaning n = 1
      obtain ⟨e, he1, he2⟩ := h1
      have : e = e + 1 := by rw [← he1, ← he2]
      -- n = 1, so there's only one element
      have huniq : Finset.univ.filter (fun e' => v = e' ∨ v = e' + 1) = {e} := by
        ext e'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hor
          rcases hor with heq | heq'
          · rw [heq, he1]
          · have : e' + 1 = e + 1 := by rw [← heq', ← he2]
            exact Fin.add_right_cancel this
        · intro heq
          left; rw [heq, he1]
      rw [huniq, Finset.sum_singleton]
      simp only [he1, ↓reduceIte, he2]
    · -- Normal case: v = e and v = e + 1 are different conditions
      push_neg at h1
      -- e such that v = e
      have hexists1 : ∃! e, v = e := ⟨v, rfl, fun e he => he.symm⟩
      -- e such that v = e + 1, i.e., e = v - 1
      have hexists2 : ∃! e, v = e + 1 := by
        use v - 1
        constructor
        · simp only [sub_add_cancel]
        · intro e he
          have : e + 1 = v := he.symm
          calc e = e + 1 - 1 := by ring
            _ = v - 1 := by rw [this]
      -- The two elements are different
      have hne : v ≠ v - 1 + 1 → v ≠ (v - 1 : Fin n) + 1 → False := by
        intro h _
        simp only [sub_add_cancel] at h
      -- Actually v - 1 + 1 = v always in Fin n
      have hsimp : (v - 1 : Fin n) + 1 = v := by simp only [sub_add_cancel]
      -- So the condition v = e + 1 is satisfied by e = v - 1
      -- And v = e is satisfied by e = v
      -- These give different e unless v = v - 1, i.e., 1 = 0 in Fin n, i.e., n = 1
      by_cases hn1 : v = v - 1
      · -- n divides 1, so n = 1
        exfalso
        have : (1 : Fin n) = 0 := by
          calc (1 : Fin n) = v - (v - 1) := by ring
            _ = v - v := by rw [hn1]
            _ = 0 := by ring
        have : n = 1 := by
          have h1 : (1 : Fin n).val = 0 := by simp only [this, Fin.val_zero]
          have h2 : (1 : Fin n).val = 1 % n := Fin.val_one
          rw [h2] at h1
          omega
        -- But then h1 should have found a witness
        apply h1 v
        constructor
        · rfl
        · rw [hsimp]
      · -- v ≠ v - 1, so we have two distinct elements
        have hdistinct : v ≠ v - 1 := hn1
        rw [Finset.filter_or]
        have hfilt1 : Finset.univ.filter (fun e => v = e) = {v} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
        have hfilt2 : Finset.univ.filter (fun e => v = e + 1) = {v - 1} := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
          constructor
          · intro he
            have : e + 1 = v := he.symm
            calc e = e + 1 - 1 := by ring
              _ = v - 1 := by rw [this]
          · intro he
            rw [he, sub_add_cancel]
        rw [hfilt1, hfilt2]
        have hdisjoint : Disjoint ({v} : Finset (Fin n)) {v - 1} := by
          simp only [Finset.disjoint_singleton]
          exact hdistinct
        rw [Finset.sum_union hdisjoint]
        simp only [Finset.sum_singleton, ↓reduceIte, hsimp]
        ring
  rw [h]; ring

/-- Mean of a function over Fin n -/
def mean (f : E n → ℝ) : ℝ := (∑ e : E n, f e) / n

/-- Any flux in ker(B) is a scalar multiple of the uniform flux.
    For n ≥ 2, dim(ker(B)) = 1. -/
theorem ker_is_span_uniform (hn : 1 < n) (J : E n → ℝ) 
    (hJ : ∀ v : V n, (∑ e : E n, B n v e * J e) = 0) :
    ∃ c : ℝ, ∀ e : E n, J e = c * uniformFlux n e := by
  -- The equations are: -J_v + J_{v-1} = 0 for all v
  -- i.e., J_v = J_{v-1} for all v
  -- This means J is constant
  use J 0
  intro e
  simp only [uniformFlux, mul_one]
  -- Show J e = J 0 by induction on e
  induction e using Fin.inductionOn with
  | zero => rfl
  | succ i ih =>
    -- From hJ at vertex (i+1): -J_{i+1} + J_i = 0, so J_{i+1} = J_i
    have hv := hJ (i + 1)
    simp only [B] at hv
    -- The only non-zero terms are for e = i+1 (gives -J_{i+1}) and e = i (gives +J_i if (i+1) = i + 1)
    have hsimplify : ∑ e : Fin n, (if (i + 1 : Fin n) = e then -1 else if (i + 1 : Fin n) = e + 1 then 1 else 0) * J e =
                     -J (i + 1) + J i := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) 
            (p := fun e => (i + 1 : Fin n) = e ∨ (i + 1 : Fin n) = e + 1)]
      have hrest : ∑ e ∈ Finset.univ.filter (fun e => ¬((i + 1 : Fin n) = e ∨ (i + 1 : Fin n) = e + 1)), 
                     (if (i + 1 : Fin n) = e then -1 else if (i + 1 : Fin n) = e + 1 then 1 else 0) * J e = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, not_or, true_and] at he
        simp only [he.1, ↓reduceIte, he.2, zero_mul]
      rw [hrest, add_zero]
      -- Sum over {i+1, i}
      have hne : (i + 1 : Fin n) ≠ i := by
        intro heq
        have : (1 : Fin n) = 0 := by
          calc (1 : Fin n) = (i + 1) - i := by ring
            _ = i - i := by rw [heq]
            _ = 0 := by ring
        have hval : (1 : Fin n).val = 0 := by simp only [this, Fin.val_zero]
        have hval' : (1 : Fin n).val = 1 % n := Fin.val_one
        rw [hval'] at hval
        omega
      rw [Finset.filter_or]
      have hfilt1 : Finset.univ.filter (fun e => (i + 1 : Fin n) = e) = {i + 1} := by
        ext e; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
      have hfilt2 : Finset.univ.filter (fun e => (i + 1 : Fin n) = e + 1) = {i} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
        constructor
        · intro he
          have : e + 1 = i + 1 := he.symm
          exact Fin.add_right_cancel this
        · intro he
          rw [he]
      rw [hfilt1, hfilt2]
      have hdisjoint : Disjoint ({i + 1} : Finset (Fin n)) {i} := by
        simp only [Finset.disjoint_singleton]
        exact hne
      rw [Finset.sum_union hdisjoint]
      simp only [Finset.sum_singleton, ↓reduceIte]
      ring
    rw [hsimplify] at hv
    -- So -J_{i+1} + J_i = 0, i.e., J_{i+1} = J_i
    have : J (i + 1) = J i := by linarith
    rw [this, ih]

/-- Uniform weights -/
def w : E n → ℝ := fun _ => 1

/-- Weights are positive -/
theorem w_pos : ∀ e : E n, w n e > 0 := by
  intro e; simp only [w]; norm_num

/-- The Onsager-Rayleigh functional for the n-cycle:
    F(J) = (1/2) ∑ J_e²/w_e - ∑ ω_e J_e -/
def onsagerRayleigh (ω J : E n → ℝ) : ℝ :=
  (1/2) * (∑ e : E n, J e * J e / w n e) - (∑ e : E n, ω e * J e)

/-- The optimal flux coefficient: mean of ω -/
def optimalFluxCoeff (ω : E n → ℝ) : ℝ := mean n ω

/-- The optimal flux: uniform flow at the mean rate -/
def optimalFlux (ω : E n → ℝ) : E n → ℝ :=
  fun e => optimalFluxCoeff n ω * uniformFlux n e

/-- The optimal flux simplifies to the mean of ω -/
theorem optimalFlux_eq (ω : E n → ℝ) (e : E n) : 
    optimalFlux n ω e = mean n ω := by
  simp only [optimalFlux, optimalFluxCoeff, uniformFlux, mul_one]

/-- The optimal flux is in ker(B) -/
theorem optimalFlux_in_ker (ω : E n → ℝ) : 
    ∀ v : V n, (∑ e : E n, B n v e * optimalFlux n ω e) = 0 := by
  intro v
  have h : ∀ e, optimalFlux n ω e = optimalFluxCoeff n ω * uniformFlux n e := fun e => rfl
  simp_rw [h]
  have hunif := uniform_in_ker n
  calc ∑ e : E n, B n v e * (optimalFluxCoeff n ω * uniformFlux n e)
      = optimalFluxCoeff n ω * ∑ e : E n, B n v e * uniformFlux n e := by
        rw [← Finset.mul_sum]; ring_nf
        apply Finset.sum_congr rfl; intro e _; ring
    _ = optimalFluxCoeff n ω * 0 := by rw [hunif v]
    _ = 0 := by ring

/-- The optimal flux minimizes F over ker(B) -/
theorem optimalFlux_minimizes (hn : 1 < n) (ω J : E n → ℝ) 
    (hJ : ∀ v : V n, (∑ e : E n, B n v e * J e) = 0) :
    onsagerRayleigh n ω (optimalFlux n ω) ≤ onsagerRayleigh n ω J := by
  -- J ∈ ker(B) implies J = c · (1,...,1) for some c
  obtain ⟨c, hc⟩ := ker_is_span_uniform n hn J hJ
  let cstar := optimalFluxCoeff n ω
  -- F(J) = (n/2)c² - (∑ω)c
  -- F(J*) = (n/2)c*² - (∑ω)c* where c* = (∑ω)/n
  -- F(J) - F(J*) = (n/2)(c - c*)² ≥ 0
  simp only [onsagerRayleigh, optimalFlux, optimalFluxCoeff, uniformFlux, w, mean, mul_one, div_one]
  simp_rw [hc, uniformFlux, mul_one]
  -- Algebra: show LHS ≤ RHS
  have key : (1/2) * ∑ e : E n, cstar * cstar - ∑ e : E n, ω e * cstar ≤ 
             (1/2) * ∑ e : E n, c * c - ∑ e : E n, ω e * c := by
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have hcstar : cstar = (∑ e : E n, ω e) / n := rfl
    -- LHS = (n/2)c*² - (∑ω)c*
    -- RHS = (n/2)c² - (∑ω)c  
    -- RHS - LHS = (n/2)(c² - c*²) - (∑ω)(c - c*)
    --           = (n/2)(c - c*)(c + c*) - n·c*(c - c*)
    --           = (c - c*) · [(n/2)(c + c*) - n·c*]
    --           = (c - c*) · [(n/2)c + (n/2)c* - n·c*]
    --           = (c - c*) · [(n/2)c - (n/2)c*]
    --           = (n/2)(c - c*)² ≥ 0
    have expand : (1/2) * (↑n * (c * c)) - (∑ e : E n, ω e) * c -
                  ((1/2) * (↑n * (cstar * cstar)) - (∑ e : E n, ω e) * cstar) =
                  (↑n / 2) * (c - cstar) * (c - cstar) := by
      rw [hcstar]
      field_simp
      ring
    have sq_nonneg : 0 ≤ (↑n / 2) * (c - cstar) * (c - cstar) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply div_nonneg; simp; linarith
      · apply mul_self_nonneg
    linarith
  convert key using 2 <;> ring

/-- Uniqueness: if J achieves the minimum, then J = J* -/
theorem optimalFlux_unique (hn : 1 < n) (ω J : E n → ℝ)
    (hJ : ∀ v : V n, (∑ e : E n, B n v e * J e) = 0)
    (hmin : onsagerRayleigh n ω J = onsagerRayleigh n ω (optimalFlux n ω)) :
    J = optimalFlux n ω := by
  obtain ⟨c, hc⟩ := ker_is_span_uniform n hn J hJ
  let cstar := optimalFluxCoeff n ω
  -- From F(J) = F(J*), we get (n/2)(c - c*)² = 0, so c = c*
  have hceq : c = cstar := by
    simp only [onsagerRayleigh, optimalFlux, optimalFluxCoeff, uniformFlux, w, mean, 
               mul_one, div_one, Finset.sum_const, Finset.card_fin, smul_eq_mul] at hmin
    simp_rw [hc, uniformFlux, mul_one] at hmin
    have hcstar : cstar = (∑ e : E n, ω e) / n := rfl
    have expand : (↑n / 2) * (c - cstar) * (c - cstar) = 0 := by
      have h1 : (1/2) * (↑n * (c * c)) - (∑ e : E n, ω e) * c -
                ((1/2) * (↑n * (cstar * cstar)) - (∑ e : E n, ω e) * cstar) =
                (↑n / 2) * (c - cstar) * (c - cstar) := by
        rw [hcstar]; field_simp; ring
      linarith
    have hn_pos : (0 : ℝ) < n := by simp; linarith
    have hn2_pos : (0 : ℝ) < n / 2 := by linarith
    have sq_zero : (c - cstar) * (c - cstar) = 0 := by
      have := expand
      have h1 : (↑n / 2) * ((c - cstar) * (c - cstar)) = 0 := by linarith
      exact (mul_eq_zero.mp h1).resolve_left (ne_of_gt hn2_pos)
    have diff_zero : c - cstar = 0 := by
      rcases eq_or_ne (c - cstar) 0 with h | h
      · exact h
      · have := mul_self_pos.mpr h
        linarith
    linarith
  funext e
  rw [hc e, hceq]
  simp only [optimalFlux, uniformFlux, mul_one]

/-!
## Summary

For the n-cycle (n ≥ 2) with uniform weights w = (1,...,1):

1. **Kernel structure**: ker(B) = ℝ · (1,...,1) — one-dimensional

2. **Optimal flux**: J* = (mean ω) · (1,...,1) = ((∑ωᵢ)/n, ..., (∑ωᵢ)/n)

3. **Optimality**: F(J*) ≤ F(J) for all J ∈ ker(B), with equality iff J = J*

4. **Physical interpretation**:
   - The driving force ω is "projected" onto the single cyclic mode
   - The mean ⟨ω⟩ = (∑ωᵢ)/n is the net thermodynamic drive around the cycle
   - If ⟨ω⟩ > 0: clockwise circulation
   - If ⟨ω⟩ < 0: counterclockwise circulation
   - If ⟨ω⟩ = 0: no net flow (detailed balance)

5. **Kirchhoff's theorem**: For a single cycle, the current is uniform
   and determined by the total EMF divided by total resistance.

The n-cycle demonstrates the core mechanism:
- Cycles are the "degrees of freedom" for steady-state fluxes
- The Onsager-Rayleigh functional selects the optimal distribution
- For graphs with multiple cycles, J* decomposes into cycle contributions
-/

end Cycle
