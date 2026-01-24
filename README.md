# DefectCRN: Formal Verification of Chemical Reaction Network Theory

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.14.0-blue)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-latest-green)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache%202.0-orange)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18363743.svg)](https://doi.org/10.5281/zenodo.18363743)
[![Paper](https://img.shields.io/badge/Paper-PDF-red)](paper.pdf)

A formally verified Lean 4 library for Chemical Reaction Network Theory (CRNT), implementing the Onsager-Rayleigh variational framework, deficiency theorems, persistence theory, cohomological deficiency, and stochastic extensions.

**Author**: Paolo Vella ([paolovella1993@gmail.com](mailto:paolovella1993@gmail.com))

## Highlights

- **7861 lines** of Lean 4 code
- **273 theorems** fully proven
- **0 sorry** (zero unproven assertions)
- **0 axioms** (no additional axioms beyond Lean's core)
- **0 warnings** (clean build)
- Complete **paper** with formal correspondence table
- **Cohomological deficiency theory**: DeficiencySubspace isomorphic to H^1

## Quick Start

```bash
# Clone
git clone https://github.com/paolovella/DefectCRN.git
cd DefectCRN

# Build (requires Lean 4.14.0 via elan)
lake exe cache get   # Download Mathlib cache
lake build           # Should complete with 0 errors

# Verify no sorry or axioms
grep -r "sorry" DefectCRN/*.lean DefectCRN/**/*.lean
# Expected: empty output
```

## Project Structure

```
DefectCRN/
├── Basic.lean                 # Core Onsager-Rayleigh theory (852 lines)
├── CRNT.lean                  # Species, deficiency, mass-action (512 lines)
├── DeficiencyOne.lean         # Deficiency one theorem (367 lines)
├── Persistence.lean           # Persistence and permanence (312 lines)
├── Stochastic.lean            # Chemical Master Equation (241 lines)
├── HigherDeficiency.lean      # Networks with δ ≥ 2 (191 lines)
├── Multistability.lean        # Multiple steady states (238 lines)
├── Oscillations.lean          # Hopf bifurcations, limit cycles (273 lines)
├── ReactionDiffusion.lean     # Spatial patterns, Turing (270 lines)
├── Control.lean               # Feedback control (284 lines)
├── Cohomology/                # Cohomological deficiency theory
│   ├── ChainComplex.lean      # CRN chain complex (254 lines)
│   ├── Cycles.lean            # Cycle/coboundary spaces (307 lines)
│   ├── Deficiency.lean        # Main theorem: δ ≅ dim(H¹) (286 lines)
│   ├── Obstruction.lean       # Degrees of freedom interpretation (241 lines)
│   ├── VariationalDuality.lean # Onsager-Rayleigh connection (258 lines)
│   ├── Foundations/           # NEW in v5.0: Rigorous foundations
│   │   ├── InnerProducts.lean # W and W⁻¹ weighted inner products (225 lines)
│   │   ├── CochainComplex.lean # Graph cochain complex (111 lines)
│   │   └── DeficiencySubspace.lean # ker(Y) ∩ im(B^T) (199 lines)
│   └── Examples/
│       ├── Triangle.lean      # δ = 0 example (218 lines)
│       ├── MichaelisMenten.lean # δ = 0 example (249 lines)
│       └── DeficiencyOne.lean # δ = 1 example (136 lines)
└── Examples/
    ├── Triangle.lean          # 3-cycle verification (319 lines)
    ├── Cycle.lean             # n-cycle parametric (438 lines)
    ├── MichaelisMenten.lean   # Enzyme kinetics (407 lines)
    ├── Glycolysis.lean        # Glycolysis pathway (238 lines)
    └── TCA.lean               # TCA cycle (273 lines)
```

| File | Lines | Theorems | Description |
|------|-------|----------|-------------|
| `Basic.lean` | 852 | 38 | Graph Laplacian, Hodge decomposition, Onsager-Rayleigh functional |
| `CRNT.lean` | 512 | 10 | Stoichiometric matrix, deficiency, cycle affinities, mass-action |
| `DeficiencyOne.lean` | 367 | 4 | Deficiency one existence/uniqueness, linkage classes |
| `Persistence.lean` | 312 | 8 | Trajectories, persistence, permanence, omega-limit sets, siphons |
| `Stochastic.lean` | 241 | 6 | Discrete states, propensities, product-form distributions, CME |
| `HigherDeficiency.lean` | 191 | 4 | D2A conditions, concordance, SR-graph |
| `Multistability.lean` | 238 | 7 | Bifurcations, sign conditions, injectivity |
| `Oscillations.lean` | 273 | 5 | Hopf bifurcation, limit cycles, Routh-Hurwitz |
| `ReactionDiffusion.lean` | 270 | 3 | Turing patterns, traveling waves |
| `Control.lean` | 284 | 7 | Antithetic control, robustness, adaptation |
| `Cohomology/*` | 1931 | 95 | Chain complex, DeficiencySubspace, δ ≅ dim(H¹), Foundations |
| `Examples/*` | 1675 | 34 | Triangle, Cycle, Michaelis-Menten, Glycolysis, TCA |
| **Total** | **7861** | **273** | |

## Theory Overview

### Part 1: Onsager-Rayleigh Variational Framework

The central functional:

$$F(J) = \frac{1}{2}\langle J, J \rangle_{W^{-1}} - \langle \omega, J \rangle$$

**Weighted Inner Products (v5.0):**
- W-weighted: $\langle x, y \rangle_W = \sum_i W_i x_i y_i$
- W⁻¹-weighted: $\langle x, y \rangle_{W^{-1}} = \sum_i x_i y_i / W_i$

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Optimality | `onsager_rayleigh_optimal` | J* = argmin_{J in ker(B)} F(J) |
| Uniqueness | `onsager_rayleigh_unique` | F(J) = F(J*) => J = J* |
| Quadratic Expansion | `onsager_quadratic_expansion` | F(J*+h) - F(J*) = 1/2 <h,h>_{W^-1} |
| Lyapunov | `lyapunov_zero_iff` | V(J) = 0 <=> J = J* |

### Part 2: CRNT Deficiency Theory

**Definitions:**
- Stoichiometric matrix: N = Y · B
- Deficiency: δ = n - l - rank(N)

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Cycle Affinity | `cycle_affinity_constant` | A_cycle independent of concentration |
| Deficiency Zero | `deficiency_zero_equilibrium_exists` | δ=0 + WR => exists positive equilibrium |
| Detailed Balance | `detailed_balance_equilibrium_const` | DB => ln(K_e) = N · ln(c) |

### Part 3: Cohomological Deficiency Theory

**Chain Complex:**
$$0 \to \mathbb{R}^E \xrightarrow{B^T} \mathbb{R}^V \xrightarrow{Y} \mathbb{R}^S \to 0$$

**Key Definition (v5.0):**
- **DeficiencySubspace** = ker(Y) ∩ im(B^T) ≅ H¹

This is the space of complex vectors arising from fluxes but invisible to species dynamics.

**Physical Interpretation:**
- Elements of DeficiencySubspace represent **degrees of freedom** in steady-state behavior
- δ > 0 allows richer dynamics including multistability

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Cohomological Deficiency | `deficiency_eq_dim_defect_space` | δ = dim(DeficiencySubspace) ≅ dim(H¹) |
| Exactness | `deficiency_zero_iff_exact` | δ = 0 iff chain complex exact at V |
| Variational Duality | `variational_cohomology_duality` | Connection to Onsager-Rayleigh multipliers |

### Part 4: Persistence and Permanence

| Concept | Lean Name | Description |
|---------|-----------|-------------|
| Persistence | `isPersistentCRN` | No species concentration approaches zero |
| Permanence | `isPermanentCRN` | Compact attractor bounded away from boundary |
| Global Attractor | `GlobalAttractorProperty` | Anderson (2011) single linkage class result |

### Part 5: Stochastic Chemical Reaction Networks

| Concept | Lean Name | Description |
|---------|-----------|-------------|
| Product Form | `productFormDist` | π(n) ∝ ∏_s c_s^{n_s} / n_s! |
| CME Stationary | `product_form_is_stationary` | Product form is CME stationary distribution |
| Deterministic Limit | `stochastic_to_deterministic_limit` | Kurtz: n(t)/V → c(t) as V → ∞ |

### Part 6: Examples

| Example | Species | Reactions | Key Result |
|---------|---------|-----------|------------|
| **Triangle** | 3 | 3 | ker(B) = ℝ · (1,1,1), J* = mean(ω) · 1 |
| **n-Cycle** | n | n | Kirchhoff: current = total EMF / total resistance |
| **Michaelis-Menten** | 4 | 3 | v = V_max · [S] / (K_m + [S]) with δ = 0 |
| **Glycolysis** | 8 | 8 | Simplified metabolic pathway |
| **TCA** | 16 | 10 | Complete Krebs cycle with conservation laws |

## Paper

The accompanying paper (`paper.pdf`) provides:
- Complete mathematical exposition
- All proofs in traditional notation
- Correspondence table (Appendix A) mapping each theorem to Lean

### Paper <-> Lean Correspondence (Selected)

| Paper | Lean Theorem | File |
|-------|--------------|------|
| Theorem 2.3 (Hodge) | `hodge_decomp` | Basic.lean |
| Theorem 4.2 (Optimality) | `onsager_rayleigh_optimal` | Basic.lean |
| Theorem 5.11 (Def Zero) | `deficiency_zero_equilibrium_exists` | CRNT.lean |
| Theorem 7.1 (Cohom. Def.) | `deficiency_eq_dim_defect_space` | Cohomology/Deficiency.lean |
| Theorem 7.4 (Degrees of Freedom) | `defect_is_degree_of_freedom` | Cohomology/Obstruction.lean |

See `paper.pdf` Appendix A for the complete correspondence table.

## Requirements

- **Lean**: 4.14.0 (install via [elan](https://github.com/leanprover/elan))
- **Mathlib4**: See `lake-manifest.json` for exact commit
- **Build time**: ~3-5 minutes (with Mathlib cache)

## Citation

```bibtex
@software{vella2026defectcrn,
  author = {Vella, Paolo},
  title = {DefectCRN: Formal Verification of Chemical Reaction Network Theory},
  year = {2026},
  url = {https://github.com/paolovella/DefectCRN},
  version = {5.0.0}
}
```

## References

### Core CRNT

- Feinberg, M. (1972). Complex balancing in general kinetic systems. *Arch. Rational Mech. Anal.* 49:187-194.
- Horn, F. & Jackson, R. (1972). General mass action kinetics. *Arch. Rational Mech. Anal.* 47:81-116.
- Feinberg, M. (1987). Chemical reaction network structure and the stability of complex isothermal reactors. *Chem. Eng. Sci.* 42(10):2229-2268.
- Feinberg, M. (1995). The existence and uniqueness of steady states for a class of chemical reaction networks. *Arch. Rational Mech. Anal.* 132:311-370.

### Persistence and Stability

- Angeli, D., De Leenheer, P., & Sontag, E. D. (2007). A Petri net approach to the study of persistence in chemical reaction networks. *Mathematical Biosciences*.
- Anderson, D. F. (2011). A proof of the global attractor conjecture in the single linkage class case. *SIAM Journal on Applied Mathematics*.

### Stochastic Theory

- Anderson, D. F., Craciun, G., & Kurtz, T. G. (2010). Product-form stationary distributions for deficiency zero chemical reaction networks. *Bulletin of Mathematical Biology*.
- Kurtz, T. G. (1972). The relationship between stochastic and deterministic models for chemical reactions. *Journal of Chemical Physics*.

## License

Apache 2.0

## Acknowledgments

Built with [Lean 4](https://leanprover.github.io/) and [Mathlib4](https://github.com/leanprover-community/mathlib4).
