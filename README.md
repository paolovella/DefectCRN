# DefectCRN: Formal Verification of Chemical Reaction Network Theory

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.14.0-blue)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-latest-green)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache%202.0-orange)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18363235.svg)](https://doi.org/10.5281/zenodo.18363235)
[![Paper](https://img.shields.io/badge/Paper-PDF-red)](paper_v3.pdf)

A formally verified Lean 4 library for Chemical Reaction Network Theory (CRNT), implementing the Onsager-Rayleigh variational framework, deficiency theorems, persistence theory, and stochastic extensions.

**Author**: Paolo Vella ([paolovella1993@gmail.com](mailto:paolovella1993@gmail.com))

## Highlights

- **5214 lines** of Lean 4 code
- **126 theorems** fully proven
- **0 sorry** (zero unproven assertions)
- **0 axioms** (no additional axioms beyond Lean's core)
- Complete **paper** with formal correspondence table

## Quick Start

```bash
# Clone
git clone https://github.com/paolovella/DefectCRN.git
cd DefectCRN

# Build (requires Lean 4.14.0 via elan)
lake exe cache get   # Download Mathlib cache
lake build           # Should complete with 0 errors

# Verify no sorry or axioms
grep -r "sorry\|axiom" DefectCRN/*.lean DefectCRN/**/*.lean
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
├── HigherDeficiency.lean      # Networks with δ ≥ 2 (175 lines)
├── Multistability.lean        # Multiple steady states (220 lines)
├── Oscillations.lean          # Hopf bifurcations, limit cycles (280 lines)
├── ReactionDiffusion.lean     # Spatial patterns, Turing (260 lines)
├── Control.lean               # Feedback control (285 lines)
└── Examples/
    ├── Triangle.lean          # 3-cycle verification (319 lines)
    ├── Cycle.lean             # n-cycle parametric (438 lines)
    ├── MichaelisMenten.lean   # Enzyme kinetics (407 lines)
    ├── Glycolysis.lean        # Glycolysis pathway (237 lines)
    └── TCA.lean               # TCA cycle (265 lines)
```

| File | Lines | Theorems | Description |
|------|-------|----------|-------------|
| `Basic.lean` | 852 | 38 | Graph Laplacian, Hodge decomposition, Onsager-Rayleigh functional |
| `CRNT.lean` | 512 | 10 | Stoichiometric matrix, deficiency, cycle affinities, mass-action |
| `DeficiencyOne.lean` | 367 | 4 | Deficiency one existence/uniqueness, linkage classes |
| `Persistence.lean` | 312 | 8 | Trajectories, persistence, permanence, omega-limit sets, siphons |
| `Stochastic.lean` | 241 | 6 | Discrete states, propensities, product-form distributions, CME |
| `HigherDeficiency.lean` | 175 | 4 | D2A conditions, concordance, SR-graph |
| `Multistability.lean` | 220 | 6 | Bifurcations, sign conditions, injectivity |
| `Oscillations.lean` | 280 | 6 | Hopf bifurcation, limit cycles, Routh-Hurwitz |
| `ReactionDiffusion.lean` | 260 | 4 | Turing patterns, traveling waves |
| `Control.lean` | 285 | 6 | Antithetic control, robustness, adaptation |
| `Triangle.lean` | 319 | 11 | Explicit 3x3 matrices, kernel computation |
| `Cycle.lean` | 438 | 8 | Parametric n-cycle, Kirchhoff's theorem |
| `MichaelisMenten.lean` | 407 | 11 | E+S <-> ES -> E+P, QSSA derivation |
| `Glycolysis.lean` | 237 | 2 | 8-species metabolic pathway |
| `TCA.lean` | 265 | 2 | TCA cycle, 16 species, conservation laws |
| **Total** | **5214** | **126** | |

## Theory Overview

### Part 1: Onsager-Rayleigh Variational Framework

The central functional:

$$F(J) = \frac{1}{2}\langle J, J \rangle_{W^{-1}} - \langle \omega, J \rangle$$

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Optimality | `onsager_rayleigh_optimal` | J* = argmin_{J in ker(B)} F(J) |
| Uniqueness | `onsager_rayleigh_unique` | F(J) = F(J*) => J = J* |
| Quadratic Expansion | `onsager_quadratic_expansion` | F(J*+h) - F(J*) = 1/2 <h,h>_{W^-1} |
| Lyapunov | `lyapunov_zero_iff` | V(J) = 0 <=> J = J* |

### Part 2: CRNT Deficiency Theory

**Definitions:**
- Stoichiometric matrix: N = Y . B
- Deficiency: delta = n - l - rank(N)

**Main Results:**

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Cycle Affinity | `cycle_affinity_constant` | A_cycle independent of concentration |
| Deficiency Zero | `deficiency_zero_equilibrium_exists` | delta=0 + WR => exists positive equilibrium |
| Detailed Balance | `detailed_balance_equilibrium_const` | DB => ln(K_e) = N . ln(c) |

### Part 3: Deficiency One Theorem

For networks with deficiency delta = 1:

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| Existence | `deficiencyOne_existence` | delta=1 + WR + conditions => exists equilibrium |
| Uniqueness | `deficiencyOne_uniqueness` | Under D1A conditions, equilibrium is unique up to scaling |
| Onsager Optimal | `deficiencyOne_onsager_optimal` | KKT conditions imply variational optimality |

### Part 4: Persistence and Permanence

Global stability analysis for CRNs:

| Concept | Lean Name | Description |
|---------|-----------|-------------|
| Persistence | `isPersistentCRN` | No species concentration approaches zero |
| Permanence | `isPermanentCRN` | Compact attractor bounded away from boundary |
| Omega-limit | `omegaLimitSet` | Asymptotic behavior characterization |
| Siphons | `isSiphon` | Structural conditions for persistence |
| Global Attractor | `GlobalAttractorProperty` | Anderson (2011) single linkage class result |

### Part 5: Stochastic Chemical Reaction Networks

Extension to the Chemical Master Equation:

| Concept | Lean Name | Description |
|---------|-----------|-------------|
| Discrete State | `State` | Molecule counts n in N^S |
| Product Form | `productFormDist` | pi(n) proportional to prod_s c_s^{n_s} / n_s! |
| CME Stationary | `product_form_is_stationary` | Product form is CME stationary distribution |
| Deterministic Limit | `stochastic_to_deterministic_limit` | Kurtz theorem: n(t)/V -> c(t) as V -> infinity |
| Fluctuation-Dissipation | `fluctuation_dissipation` | Connection to Onsager coefficients |

### Part 6: Examples

| Example | Species | Reactions | Key Result |
|---------|---------|-----------|------------|
| **Triangle** | 3 | 3 | ker(B) = R . (1,1,1), J* = mean(omega) . 1 |
| **n-Cycle** | n | n | Kirchhoff: current = total EMF / total resistance |
| **Michaelis-Menten** | 4 | 3 | v = V_max . [S] / (K_m + [S]) with delta = 0 |
| **Glycolysis** | 8 | 8 | Simplified metabolic pathway, 12 complexes |

## Paper

The accompanying paper (`paper.pdf`) provides:
- Complete mathematical exposition
- All proofs in traditional notation
- Correspondence table (Appendix A) mapping each theorem to Lean

### Paper <-> Lean Correspondence

| Paper | Lean Theorem | File |
|-------|--------------|------|
| Theorem 2.3 (Hodge) | `hodge_decomp` | Basic.lean |
| Theorem 4.2 (Optimality) | `onsager_rayleigh_optimal` | Basic.lean |
| Corollary 4.3 (Uniqueness) | `onsager_rayleigh_unique` | Basic.lean |
| Theorem 5.10 (Cycle Affinity) | `cycle_affinity_constant` | CRNT.lean |
| Theorem 5.11 (Def Zero) | `deficiency_zero_equilibrium_exists` | CRNT.lean |
| Theorem 5.12 (Def One) | `deficiencyOne_existence` | DeficiencyOne.lean |
| Theorem 6.1 (Persistence) | `deficiency_zero_persistence` | Persistence.lean |
| Theorem 6.5 (Product Form) | `product_form_is_stationary` | Stochastic.lean |
| Theorem 7.8 (Michaelis-Menten) | `michaelis_menten_velocity` | MichaelisMenten.lean |

See `paper.pdf` Appendix A for the complete correspondence table.

## Important Notes

### Scope and Assumptions

1. **Deficiency Zero Theorem**: Follows Feinberg-Horn-Jackson definitions
   - Weak reversibility = each linkage class is strongly connected
   - Uniqueness is per stoichiometric compatibility class

2. **Deficiency One Theorem**: Feinberg (1995) extension
   - Requires all linkage class deficiencies delta_i = 0
   - Global deficiency delta = 1

3. **Persistence Theory**: Based on Angeli-De Leenheer-Sontag (2007)
   - Siphon-based structural conditions
   - Connection to Lyapunov stability

4. **Stochastic Extensions**: Anderson-Craciun-Kurtz (2010)
   - Product-form stationary distributions
   - Thermodynamic limit connections

5. **Michaelis-Menten**: Derived under standard QSSA
   - Quasi-steady state for ES complex
   - Enzyme conservation: [E] + [ES] = E_total

### Graph Deficiency vs CRNT Deficiency

| Concept | Formula | Location |
|---------|---------|----------|
| Graph deficiency | delta_graph = \|V\| - l - rank(B) | `Basic.lean` |
| CRNT deficiency | delta = \|V\| - l - rank(YB) | `CRNT.lean` |

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
  version = {2.0}
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
