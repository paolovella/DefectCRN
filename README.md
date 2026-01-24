# Defect Cohomology for Chemical Reaction Networks (v2)

Lean 4 formalization of the linear-response current theory for CRNs.

## Key Improvement over v1

**`symm_inv` is now DERIVED, not axiomatized.**

The symmetry of L⁻¹ on 1^⊥ follows from the symmetry of L = BWBᵀ:

```lean
theorem LaplacianInverse.symm_inv (x y : onePerp) :
    innerV (Linv.inv x).1 y.1 = innerV x.1 (Linv.inv y).1 := by
  -- Uses L_apply_symm: ⟨Lx, y⟩ = ⟨x, Ly⟩
  -- If x = L(x'), y = L(y'), then ⟨L⁻¹x, y⟩ = ⟨x', Ly'⟩ = ⟨Lx', y'⟩ = ⟨x, L⁻¹y⟩
  ...
```

## Axioms

Only TWO axioms remain:

1. **`hBcol`**: Column sums of B are zero
   ```lean
   hBcol : ∀ e : E, (∑ v : V, B v e) = 0
   ```
   This is a defining property of incidence matrices.

2. **`LaplacianInverse`**: L is invertible on 1^⊥
   ```lean
   structure LaplacianInverse where
     inv : onePerp →ₗ[ℝ] onePerp
     left_inv : ∀ x, ⟨L(inv x), _⟩ = x
     right_inv : ∀ x, inv⟨Lx, _⟩ = x
   ```
   This encodes graph connectivity (L is positive definite on 1^⊥).

## Theorems Proven (no sorry)

### Core Projection Properties (Lemma 3.1)
- `piProj_in_kerBW`: BW(π(ω)) = 0
- `piProj_kills_exact`: π(Bᵀφ) = 0
- `piProj_idem_on_ker`: π(h) = h if BW(h) = 0
- `piProj_idempotent`: π ∘ π = π
- `piProj_W_selfAdjoint`: ⟨πx, y⟩_W = ⟨x, πy⟩_W

### Supporting Lemmas
- `L_apply_symm`: ⟨Lx, y⟩ = ⟨x, Ly⟩ (L is self-adjoint)
- `LaplacianInverse.symm_inv`: ⟨L⁻¹x, y⟩ = ⟨x, L⁻¹y⟩ (DERIVED)
- `innerW_exact_harmonic_orthog`: ⟨Bᵀφ, h⟩_W = 0 if BW(h) = 0
- `sharp_energy_bound`: ‖J*‖²_{W⁻¹} = ‖π(ω)‖²_W

## Setup

```bash
# Ensure elan is installed
curl -sSf https://get.mathlib.org | sh

# Build
cd DefectCRN_v2
lake update
lake build
```

## Next Steps (Tier 1 Complete)

1. **Derive hBcol** from a proper Graph structure (optional - it's already minimal)
2. **Prove LaplacianInverse exists** for connected graphs (requires spectral theory)
3. **Add the three-cycle example** as a concrete instantiation

## Connection to Paper

This formalizes §2-§3 of "Cohomological Bounds on Steady-State Currents in Driven Reaction Networks":
- Weighted Hodge decomposition (Lemma 2.1)
- Minimum dissipation principle (Theorem 3.1)
- Projection properties (Lemma 3.1)
- Sharp energy bound (Corollary 3.5)
