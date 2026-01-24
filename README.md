# DefectCRN: Formal Verification of Chemical Reaction Network Theory

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.14.0-blue)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-latest-green)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache%202.0-orange)](LICENSE)
[![Paper](https://img.shields.io/badge/Paper-PDF-red)](paper.pdf)

A formally verified Lean 4 library for Chemical Reaction Network Theory (CRNT), implementing the Onsager–Rayleigh variational framework and the Feinberg–Horn–Jackson deficiency zero theorem.

**Author**: Paolo Vella ([paolovella1993@gmail.com](mailto:paolovella1993@gmail.com))

## Highlights

- **2529 lines** of Lean 4 code
- **66 theorems** fully proven
- **0 sorry** (zero unproven assertions)
- Complete **paper** with formal correspondence table

## Quick Start

```bash
# Clone
git clone https://github.com/paolovella/DefectCRN.git
cd DefectCRN

# Build (requires Lean 4.14.0 via elan)
lake exe cache get   # Download Mathlib cache
lake build           # Should complete with 0 errors

# Verify no sorry
grep -r "sorry" DefectCRN/*.lean DefectCRN/**/*.lean
# Expected: empty output
```

## Project Structure

```
DefectCRN/
├── Basic.lean                 # Core Onsager–Rayleigh theory (852 lines)
├── CRNT.lean                  # Species, deficiency, mass-action (513 lines)
└── Examples/
    ├── Triangle.lean          # 3-cycle verification (319 lines)
    ├── Cycle.lean             # n-cycle parametric (438 lines)
    └── MichaelisMenten.lean   # Enzyme kinetics (407 lines)
```

| File | Lines | Theorems | Description |
|------|-------|----------|-------------|
| `Basic.lean` | 852 | 25 | Graph Laplacian, Hodge decomposition, Onsager–Rayleigh functional |
| `CRNT.lean` | 513 | 15 | Stoichiometric matrix, deficiency, cycle affinities, mass-action |
| `Triangle.lean` | 319 | 8 | Explicit 3×3 matrices, kernel computation |
| `Cycle.lean` | 438 | 8 | Parametric n-cycle, Kirchhoff's theorem |
| `MichaelisMenten.lean` | 407 | 10 | E+S ⇌ ES → E+P, QSSA derivation |
| **Total** | **2529** | **66** | |

## Theory Overview

### Part 1: Onsager–Rayleigh Variational Framework

The central functional:

$$F(J) = \frac{1}{2}\langle J, J \rangle_{W^{-1}} - \langle \omega, J \rangle$$

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Optimality | `onsager_rayleigh_optimal` | J* = argmin_{J ∈ ker(B)} F(J) |
| Uniqueness | `onsager_rayleigh_unique` | F(J) = F(J*) ⟹ J = J* |
| Quadratic Expansion | `onsager_quadratic_expansion` | F(J*+h) - F(J*) = ½⟨h,h⟩_{W⁻¹} |
| Lyapunov | `lyapunov_zero_iff` | V(J) = 0 ⟺ J = J* |

### Part 2: CRNT Deficiency Theory

**Definitions:**
- Stoichiometric matrix: N = Y · B
- Deficiency: δ = n - ℓ - rank(N)

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Cycle Affinity | `cycle_affinity_constant` | A_cycle independent of concentration |
| Deficiency Zero | `deficiency_zero_equilibrium_exists` | δ=0 + WR ⟹ ∃ positive equilibrium |
| Detailed Balance | `detailed_balance_equilibrium_const` | DB ⟹ ln(K_e) = N·ln(c) |

### Part 3: Examples

| Example | Key Result |
|---------|------------|
| **Triangle** | ker(B) = ℝ·(1,1,1), J* = mean(ω)·𝟙 |
| **n-Cycle** | Kirchhoff: current = total EMF / total resistance |
| **Michaelis–Menten** | v = V_max·[S]/(K_m + [S]) with δ = 0 |

## Paper

The accompanying paper (`paper.pdf`) provides:
- Complete mathematical exposition
- All proofs in traditional notation
- Correspondence table (Appendix A) mapping each theorem to Lean

### Paper ↔ Lean Correspondence

| Paper | Lean Theorem | File |
|-------|--------------|------|
| Theorem 2.3 (Hodge) | `hodge_decomp` | Basic.lean |
| Theorem 4.2 (Optimality) | `onsager_rayleigh_optimal` | Basic.lean |
| Corollary 4.3 (Uniqueness) | `onsager_rayleigh_unique` | Basic.lean |
| Theorem 5.10 (Cycle Affinity) | `cycle_affinity_constant` | CRNT.lean |
| Theorem 5.11 (Def Zero) | `deficiency_zero_equilibrium_exists` | CRNT.lean |
| Theorem 6.8 (Michaelis–Menten) | `michaelis_menten_velocity` | MichaelisMenten.lean |

See `paper.pdf` Appendix A for the complete 27-row correspondence table.

## Important Notes

### Scope and Assumptions

1. **Deficiency Zero Theorem**: Follows Feinberg–Horn–Jackson definitions
   - Weak reversibility = each linkage class is strongly connected
   - Uniqueness is per stoichiometric compatibility class

2. **Michaelis–Menten**: Derived under standard QSSA
   - Quasi-steady state for ES complex
   - Enzyme conservation: [E] + [ES] = E_total

3. **Variational vs Kinetic**: 
   - Sections 2–4: Linear response near detailed balance
   - Section 5: Exact structural results for nonlinear mass-action

### Graph Deficiency vs CRNT Deficiency

| Concept | Formula | Location |
|---------|---------|----------|
| Graph deficiency | δ_graph = \|V\| - ℓ - rank(B) | `Basic.lean` |
| CRNT deficiency | δ = \|V\| - ℓ - rank(YB) | `CRNT.lean` |

Graph deficiency = 0 for any connected graph. CRNT deficiency can be > 0.

## Requirements

- **Lean**: 4.14.0 (install via [elan](https://github.com/leanprover/elan))
- **Mathlib4**: See `lake-manifest.json` for exact commit
- **Build time**: ~3-5 minutes (with Mathlib cache)

## Citation

```bibtex
@software{vella2025defectcrn,
  author = {Vella, Paolo},
  title = {DefectCRN: Formal Verification of Chemical Reaction Network Theory},
  year = {2025},
  url = {https://github.com/paolovella/DefectCRN},
  version = {1.0}
}
```

## References

- Feinberg, M. (1972). Complex balancing in general kinetic systems. *Arch. Rational Mech. Anal.* 49:187–194.
- Horn, F. & Jackson, R. (1972). General mass action kinetics. *Arch. Rational Mech. Anal.* 47:81–116.
- Feinberg, M. (1987). Chemical reaction network structure and the stability of complex isothermal reactors. *Chem. Eng. Sci.* 42(10):2229–2268.

## License

Apache 2.0

## Acknowledgments

Built with [Lean 4](https://leanprover.github.io/) and [Mathlib4](https://github.com/leanprover-community/mathlib4).
