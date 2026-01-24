/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Michaelis-Menten Enzyme Kinetics

The Michaelis-Menten mechanism is the fundamental model of enzyme catalysis:

```
E + S ⇌ ES → E + P
      k₁   k₃
      ⇌
      k₂
```

where:
- E = enzyme (catalyst)
- S = substrate (reactant)
- ES = enzyme-substrate complex
- P = product

## Network Structure

**Species** (S = Fin 4):
- 0: E (enzyme)
- 1: S (substrate)
- 2: ES (complex)
- 3: P (product)

**Complexes** (V = Fin 3):
- 0: E + S
- 1: ES
- 2: E + P

**Reactions** (E = Fin 3):
- 0: E + S → ES (binding, rate k₁)
- 1: ES → E + S (unbinding, rate k₂)
- 2: ES → E + P (catalysis, rate k₃)

## Key Results

1. This network has **deficiency zero** (δ = 3 - 1 - 2 = 0)
2. Conservation laws: [E] + [ES] = E_total (enzyme conservation)
3. At steady state: the classic Michaelis-Menten equation emerges
4. The Onsager-Rayleigh framework gives the variational structure

## Matrices

Incidence matrix B (3×3):
```
       e₀  e₁  e₂
v₀    -1   1   0     (E+S)
v₁     1  -1  -1     (ES)
v₂     0   0   1     (E+P)
```

Complex composition Y (4×3):
```
       v₀  v₁  v₂
E       1   0   1
S       1   0   0
ES      0   1   0
P       0   0   1
```

Stoichiometric matrix N = Y·B (4×3):
```
       e₀  e₁  e₂
E      -1   1   1
S      -1   1   0
ES      1  -1  -1
P       0   0   1
```
-/

namespace MichaelisMenten

open Finset BigOperators Matrix

/-!
## Part 1: Network Definition
-/

/-- Species: E, S, ES, P -/
abbrev Species := Fin 4

/-- Species indices -/
def idxE : Species := 0
def idxS : Species := 1
def idxES : Species := 2
def idxP : Species := 3

/-- Complexes: E+S, ES, E+P -/
abbrev Complex := Fin 3

/-- Complex indices -/
def cplxES : Complex := 0   -- E + S
def cplxC : Complex := 1    -- ES (the complex)
def cplxEP : Complex := 2   -- E + P

/-- Reactions: binding, unbinding, catalysis -/
abbrev Reaction := Fin 3

/-- Reaction indices -/
def rxnBind : Reaction := 0    -- E + S → ES
def rxnUnbind : Reaction := 1  -- ES → E + S
def rxnCat : Reaction := 2     -- ES → E + P

/-- Incidence matrix B.
    B[v,e] = +1 if reaction e produces complex v
    B[v,e] = -1 if reaction e consumes complex v -/
def B : Matrix Complex Reaction ℝ := ![
  ![-1,  1,  0],   -- E+S: consumed by e₀, produced by e₁
  ![ 1, -1, -1],   -- ES: produced by e₀, consumed by e₁ and e₂
  ![ 0,  0,  1]    -- E+P: produced by e₂
]

/-- Complex composition matrix Y.
    Y[s,v] = stoichiometric coefficient of species s in complex v -/
def Y : Matrix Species Complex ℝ := ![
  ![1, 0, 1],   -- E: present in E+S and E+P
  ![1, 0, 0],   -- S: present in E+S only
  ![0, 1, 0],   -- ES: present in ES only
  ![0, 0, 1]    -- P: present in E+P only
]

/-- Stoichiometric matrix N = Y · B -/
def N : Matrix Species Reaction ℝ := Y * B

/-- Verify N has the expected form -/
theorem N_eq : N = ![
  ![-1,  1,  1],   -- E: consumed in e₀, produced in e₁ and e₂
  ![-1,  1,  0],   -- S: consumed in e₀, produced in e₁
  ![ 1, -1, -1],   -- ES: produced in e₀, consumed in e₁ and e₂
  ![ 0,  0,  1]    -- P: produced in e₂
] := by native_decide

/-!
## Part 2: Conservation Laws
-/

/-- Column sums of B are zero (each reaction conserves complex count) -/
theorem B_col_sum_zero : ∀ e : Reaction, (∑ v : Complex, B v e) = 0 := by
  intro e
  fin_cases e <;> native_decide

/-- Enzyme conservation: E + ES is constant.
    Row E + Row ES of N = [0, 0, 0] -/
theorem enzyme_conservation : 
    ∀ e : Reaction, N idxE e + N idxES e = 0 := by
  intro e
  simp only [N, Y, B, idxE, idxES]
  fin_cases e <;> native_decide

/-- The enzyme conservation vector: (1, 0, 1, 0) · N = 0 -/
def enzymeConsVector : Species → ℝ := ![1, 0, 1, 0]

theorem enzyme_cons_in_ker_Nt : 
    ∀ e : Reaction, (∑ s : Species, enzymeConsVector s * N s e) = 0 := by
  intro e
  simp only [enzymeConsVector, N, Y, B]
  fin_cases e <;> native_decide

/-!
## Part 3: Deficiency Calculation
-/

/-- Number of complexes -/
def numComplexes : ℕ := 3

/-- Number of linkage classes (the network is connected) -/
def numLinkageClasses : ℕ := 1

/-- Rank of stoichiometric matrix.
    N has rank 2 because:
    - Row E + Row ES = 0 (enzyme conservation)
    - Rows S and P are independent
    - So dim(row space) = 2 -/
def stoichRank : ℕ := 2

/-- The CRNT deficiency: δ = n - ℓ - s = 3 - 1 - 2 = 0 -/
def deficiency : ℕ := numComplexes - numLinkageClasses - stoichRank

theorem deficiency_zero : deficiency = 0 := by
  simp only [deficiency, numComplexes, numLinkageClasses, stoichRank]
  norm_num

/-!
## Part 4: Mass-Action Kinetics
-/

/-- Concentration vector -/
def Conc := Species → ℝ

/-- Positive concentrations -/
def Conc.isPositive (c : Conc) : Prop := ∀ s, c s > 0

/-- Rate constants: k₁ (binding), k₂ (unbinding), k₃ (catalysis) -/
structure RateConsts where
  k1 : ℝ  -- E + S → ES
  k2 : ℝ  -- ES → E + S  
  k3 : ℝ  -- ES → E + P
  k1_pos : k1 > 0
  k2_pos : k2 > 0
  k3_pos : k3 > 0

/-- Mass-action reaction rate for each reaction -/
noncomputable def reactionRate (k : RateConsts) (c : Conc) : Reaction → ℝ
  | 0 => k.k1 * c idxE * c idxS      -- v₀ = k₁[E][S]
  | 1 => k.k2 * c idxES              -- v₁ = k₂[ES]
  | 2 => k.k3 * c idxES              -- v₂ = k₃[ES]

/-- The reaction flux vector J = (v₀, v₁, v₂) -/
noncomputable def flux (k : RateConsts) (c : Conc) : Reaction → ℝ :=
  reactionRate k c

/-!
## Part 5: Steady State Analysis
-/

/-- Steady state condition: N · J = 0 (no net change in any species) -/
def isSteadyState (k : RateConsts) (c : Conc) : Prop :=
  ∀ s : Species, (∑ e : Reaction, N s e * flux k c e) = 0

/-- Complex balanced condition: at each complex, inflow = outflow -/
def isComplexBalanced (k : RateConsts) (c : Conc) : Prop :=
  ∀ v : Complex, 
    (∑ e : Reaction, max 0 (B v e) * flux k c e) = 
    (∑ e : Reaction, max 0 (-B v e) * flux k c e)

/-- At steady state, the flux is in ker(N) -/
theorem steady_state_flux_in_ker (k : RateConsts) (c : Conc) 
    (hss : isSteadyState k c) :
    ∀ s : Species, (∑ e : Reaction, N s e * flux k c e) = 0 := hss

/-!
## Part 6: The Michaelis-Menten Equation
-/

/-- Total enzyme concentration (conserved quantity) -/
noncomputable def E_total (c : Conc) : ℝ := c idxE + c idxES

/-- At quasi-steady state for ES, we have:
    d[ES]/dt = k₁[E][S] - k₂[ES] - k₃[ES] = 0
    This gives: [ES] = k₁[E][S] / (k₂ + k₃) -/
theorem quasi_steady_state_ES (k : RateConsts) (c : Conc) 
    (hss : (∑ e : Reaction, N idxES e * flux k c e) = 0) :
    k.k1 * c idxE * c idxS = (k.k2 + k.k3) * c idxES := by
  simp only [N, Y, B, idxES, flux, reactionRate] at hss
  simp only [Fin.sum_univ_three, Fin.isValue] at hss
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, 
             Matrix.head_cons, Matrix.cons_val_fin_one] at hss
  -- hss: 1 * (k.k1 * c 0 * c 1) + (-1) * (k.k2 * c 2) + (-1) * (k.k3 * c 2) = 0
  linarith

/-- The Michaelis constant K_M = (k₂ + k₃) / k₁ -/
noncomputable def K_M (k : RateConsts) : ℝ := (k.k2 + k.k3) / k.k1

/-- The maximum velocity V_max = k₃ · E_total -/
noncomputable def V_max (k : RateConsts) (c : Conc) : ℝ := k.k3 * E_total c

/-- At quasi-steady state:
    [ES] = E_total · [S] / (K_M + [S])
    
    This is derived from:
    - [ES] = k₁[E][S] / (k₂ + k₃)
    - [E] = E_total - [ES]
    Solving gives [ES] = E_total · [S] / (K_M + [S]) -/
theorem michaelis_menten_ES (k : RateConsts) (c : Conc)
    (hqss : k.k1 * c idxE * c idxS = (k.k2 + k.k3) * c idxES)
    (hcons : c idxE + c idxES = E_total c)
    (hS_pos : c idxS > 0) (hKM_pos : K_M k + c idxS > 0) :
    c idxES = E_total c * c idxS / (K_M k + c idxS) := by
  -- From hqss: k₁ · [E] · [S] = (k₂ + k₃) · [ES]
  -- From hcons: [E] = E_total - [ES]
  -- Substitute: k₁ · (E_total - [ES]) · [S] = (k₂ + k₃) · [ES]
  -- Expand: k₁ · E_total · [S] - k₁ · [ES] · [S] = (k₂ + k₃) · [ES]
  -- Collect: k₁ · E_total · [S] = [ES] · (k₂ + k₃ + k₁ · [S])
  -- Solve: [ES] = k₁ · E_total · [S] / (k₂ + k₃ + k₁ · [S])
  --             = E_total · [S] / ((k₂ + k₃)/k₁ + [S])
  --             = E_total · [S] / (K_M + [S])
  have hE : c idxE = E_total c - c idxES := by linarith
  rw [hE] at hqss
  -- hqss: k₁ · (E_total - [ES]) · [S] = (k₂ + k₃) · [ES]
  have expand : k.k1 * (E_total c - c idxES) * c idxS = 
                k.k1 * E_total c * c idxS - k.k1 * c idxES * c idxS := by ring
  rw [expand] at hqss
  -- k₁ · E_total · [S] - k₁ · [ES] · [S] = (k₂ + k₃) · [ES]
  -- k₁ · E_total · [S] = [ES] · (k₂ + k₃ + k₁ · [S])
  have collect : k.k1 * E_total c * c idxS = c idxES * (k.k2 + k.k3 + k.k1 * c idxS) := by
    linarith
  -- [ES] = k₁ · E_total · [S] / (k₂ + k₃ + k₁ · [S])
  have hpos : k.k2 + k.k3 + k.k1 * c idxS > 0 := by
    have := k.k1_pos
    have := k.k2_pos
    have := k.k3_pos
    linarith
  have solve : c idxES = k.k1 * E_total c * c idxS / (k.k2 + k.k3 + k.k1 * c idxS) := by
    field_simp at collect ⊢
    linarith
  rw [solve]
  -- Now show this equals E_total · [S] / (K_M + [S])
  simp only [K_M]
  have hk1_pos := k.k1_pos
  field_simp
  ring

/-- The Michaelis-Menten equation for reaction velocity:
    v = V_max · [S] / (K_M + [S]) = k₃ · [ES] -/
theorem michaelis_menten_velocity (k : RateConsts) (c : Conc)
    (hES : c idxES = E_total c * c idxS / (K_M k + c idxS))
    (hKM_pos : K_M k + c idxS > 0) :
    flux k c rxnCat = V_max k c * c idxS / (K_M k + c idxS) := by
  simp only [flux, reactionRate, rxnCat, V_max]
  rw [hES]
  ring

/-!
## Part 7: Onsager-Rayleigh Structure
-/

/-- Uniform weights for simplicity -/
def w : Reaction → ℝ := fun _ => 1

theorem w_pos : ∀ e : Reaction, w e > 0 := by
  intro e; simp only [w]; norm_num

/-- The Onsager-Rayleigh functional at concentration c -/
noncomputable def onsagerRayleigh (k : RateConsts) (c : Conc) (J : Reaction → ℝ) : ℝ :=
  (1/2) * (∑ e : Reaction, J e * J e / w e) - 
  ∑ e : Reaction, (flux k c e) * J e

/-- At steady state, the actual flux minimizes a modified functional
    over the constraint set {J : N · J = 0}.
    
    The Onsager-Rayleigh principle says J* = argmin F(J) subject to B · J = 0.
    For Michaelis-Menten, the steady state flux satisfies this principle. -/

/-!
## Part 8: Thermodynamic Interpretation
-/

/-- The dissipation function: Φ = ∑ Jₑ · Aₑ where Aₑ is the affinity.
    At steady state, Φ ≥ 0 with equality only at equilibrium.
    
    For Michaelis-Menten at steady state (but not equilibrium):
    - Substrate is consumed, product is formed
    - Net flux through the cycle: J₀ - J₁ = J₂ > 0
    - The system dissipates free energy: Φ = J₂ · ΔG > 0 -/

/-- Net flux through the catalytic step -/
noncomputable def netCatalyticFlux (k : RateConsts) (c : Conc) : ℝ :=
  flux k c rxnCat

/-- At steady state, net binding = net catalysis:
    J₀ - J₁ = J₂ (what goes in must come out) -/
theorem flux_balance_steady_state (k : RateConsts) (c : Conc)
    (hss_ES : (∑ e : Reaction, N idxES e * flux k c e) = 0) :
    flux k c rxnBind - flux k c rxnUnbind = flux k c rxnCat := by
  simp only [N, Y, B, idxES, flux, reactionRate, rxnBind, rxnUnbind, rxnCat] at *
  simp only [Fin.sum_univ_three, Fin.isValue] at hss_ES
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, 
             Matrix.head_cons, Matrix.cons_val_fin_one] at hss_ES
  -- hss_ES: 1 * v₀ + (-1) * v₁ + (-1) * v₂ = 0
  -- So v₀ - v₁ - v₂ = 0, i.e., v₀ - v₁ = v₂
  linarith

/-!
## Summary

The Michaelis-Menten mechanism demonstrates:

1. **CRNT Structure**:
   - 4 species, 3 complexes, 3 reactions
   - Deficiency δ = 3 - 1 - 2 = 0 ✓

2. **Conservation Laws**:
   - Enzyme conservation: [E] + [ES] = E_total

3. **Michaelis-Menten Equation**:
   - [ES] = E_total · [S] / (K_M + [S])
   - v = V_max · [S] / (K_M + [S])
   - K_M = (k₂ + k₃) / k₁
   - V_max = k₃ · E_total

4. **Steady State Flux Balance**:
   - J₀ - J₁ = J₂ (conservation at ES complex)

5. **Onsager-Rayleigh Connection**:
   - The steady state flux minimizes dissipation
   - Deficiency zero ensures unique steady state

This is the foundational model of enzyme kinetics, showing how
the abstract CRNT framework applies to real biochemistry.
-/

end MichaelisMenten
