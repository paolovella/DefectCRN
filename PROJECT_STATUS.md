# Project Status: Deficiency Theory for CRN and QMS

## Overview

A Lean 4 formalization of deficiency theory for Chemical Reaction Networks (CRN) and Quantum Markov Semigroups (QMS), with accompanying papers.

## Project Statistics

| Metric | Count |
|--------|-------|
| Lean files | 43 |
| Lines of code | 15,969 |
| Theorems/Lemmas | 588 |
| Definitions | 442 |
| Structures | 46 |
| Axioms | 23 |
| Sorries | 1 |

---

## Axioms (23 total)

### Lindbladian Evolution (5 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `Lindbladian.evolve` | Lindbladian.lean:483 | Time evolution e^{tL} exists |
| `Lindbladian.dualEvolve` | Lindbladian.lean:487 | Dual (Heisenberg) evolution |
| `Lindbladian.evolve_add` | Lindbladian.lean:491 | Semigroup: e^{(s+t)L} = e^{sL} ∘ e^{tL} |
| `Lindbladian.evolve_zero` | Lindbladian.lean:496 | Identity: e^{0·L} = id |
| `Lindbladian.evolve_duality` | Lindbladian.lean:501 | Schrödinger-Heisenberg duality |

### Evans-Høegh-Krohn Theorem (2 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `evans_hoegh_krohn_identity` | Algebra.lean:917 | L(ρσ) = L(ρ)σ + ρL(σ) |
| `evans_hoegh_krohn_identity_dag` | Algebra.lean:936 | Adjoint version |

### Stationary States (1 axiom)

| Axiom | File | Description |
|-------|------|-------------|
| `exists_stationary_state` | StationaryState.lean:176 | Every Lindbladian has stationary state |

### Wedderburn Structure (2 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `gksl_gauge_freedom_of_equiv` | InteractionAlgebra.lean:481 | GKSL gauge equivalence |
| `wedderburn_decomposition_exists` | InteractionAlgebra.lean:586 | Wedderburn-Artin decomposition |

### Detailed Balance (4 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `norm_comparison` | DetailedBalance.lean:224 | GNS norm bounds |
| `gns_projection_bound` | DetailedBalance.lean:241 | GNS projection estimates |
| `qdb_real_spectrum` | DetailedBalance.lean:255 | Detailed balance ⟹ real spectrum |
| `qdb_negative_semidefinite` | DetailedBalance.lean:273 | Detailed balance ⟹ L ≤ 0 |

### Convergence Theory (4 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `spectral_gap_exists` | QuantumDZT.lean:178 | Ergodic ⟹ spectral gap |
| `heisenberg_exponential_decay` | QuantumDZT.lean:192 | Exponential decay |
| `quantum_dzt_convergence` | QuantumDZT.lean:215 | Quantum DZT convergence |
| `convergence_to_stationary` | Frigerio.lean:148 | Convergence to stationary |

### Frigerio (1 axiom)

| Axiom | File | Description |
|-------|------|-------------|
| `quantumSemigroup` | Frigerio.lean:126 | QDS properties |

### Classification (3 axioms)

| Axiom | File | Description |
|-------|------|-------------|
| `structuralCommutant_le_center` | Classification.lean:165 | Structural ⊆ center (non-degenerate) |
| `ergodic_lindbladian_exists` | Classification.lean:380 | ∃ ergodic Lindbladian ∀n |
| `peripheral_phases_finitely_generated` | Classification.lean:442 | Phases form ℤ^k |

---

## Sorries (1 total)

| Location | Theorem | Description | Difficulty |
|----------|---------|-------------|------------|
| Classification.lean:430 | `ergodic_peripheral_trivial` | Ergodic ⟹ peripheral spectrum = {0} | Hard (spectral theory) |

**Why it's hard**: Requires spectral theory for non-self-adjoint operators, including Perron-Frobenius type results for completely positive maps. This infrastructure is not yet available in Mathlib.

---

## Key Theorems (Proved)

### Universal Classification
```lean
theorem quantum_deficiency_eq_commutant_deficiency (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    quantumDeficiency L = commutantDeficiency L
```
**Status**: ✅ Proved (modulo Evans-Høegh-Krohn axiom)

### Multiplicity-Free Characterization
```lean
theorem quantum_deficiency_eq_central_iff_multiplicityFree (L : Lindbladian n)
    (hFaith : HasFaithfulStationaryState L) :
    quantumDeficiency L = centralDeficiency L ↔ IsMultiplicityFree L
```
**Status**: ✅ Proved (arithmetic lemma now complete)

### Deficiency Hierarchy
```lean
theorem deficiency_hierarchy (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (hSupp : L.hasSupport G)
    (hFaith : HasFaithfulStationaryState L) :
    structuralDeficiency G ≤ centralDeficiency L ∧
    centralDeficiency L ≤ commutantDeficiency L ∧
    commutantDeficiency L = quantumDeficiency L
```
**Status**: ✅ Proved (using `structuralCommutant_le_center` axiom)

### Structural Deficiency Formula
```lean
theorem structural_deficiency_eq_scc_minus_one (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) :
    structuralDeficiency G = numSCCs (directedSupportGraph G) - 1
```
**Status**: ✅ Proved

---

## Papers

| Paper | Pages | Description |
|-------|-------|-------------|
| `paper.pdf` | 19 | Main CRNT monograph with quantum section |
| `quantum_classification.pdf` | 9 | Standalone QMS classification paper |

---

## File Structure

```
DefectCRN/
├── Basic.lean              # Core definitions
├── CRNT.lean               # Chemical reaction network theory
├── DeficiencyOne.lean      # Deficiency one theorem
├── HigherDeficiency.lean   # Higher deficiency theory
├── Persistence.lean        # Persistence and attractors
├── Multistability.lean     # Bifurcation analysis
├── Oscillations.lean       # Hopf bifurcation, Routh-Hurwitz
├── ReactionDiffusion.lean  # Turing instability
├── Stochastic.lean         # CME, product form
├── Control.lean            # Antithetic control
├── Cohomology/             # Cohomological deficiency theory
│   ├── ChainComplex.lean
│   ├── Cycles.lean
│   ├── Deficiency.lean
│   ├── Obstruction.lean
│   └── VariationalDuality.lean
└── Quantum/                # Quantum CRNT
    ├── Lindbladian.lean    # Lindblad dynamics
    ├── Algebra.lean        # Algebraic structure
    ├── InteractionAlgebra.lean  # Wedderburn decomposition
    ├── StationaryState.lean
    ├── Deficiency.lean     # Quantum deficiency
    ├── Classification.lean # Main theorems
    ├── StructuralDeficiency.lean  # Graph-based deficiency
    ├── DetailedBalance.lean
    ├── Frigerio.lean
    ├── QuantumDZT.lean     # Quantum deficiency zero theorem
    └── Irreducibility.lean
```

---

## Recent Commits

```
9ef7549 Fill sorries: arithmetic lemma proved, structural hierarchy via axiom
01ee055 Add comprehensive axioms and sorries documentation
85978ef Fix terminology and split quantum classification into separate paper
7606d0a Fix critical mathematical error: δ_Q = δ_com is universal, not δ_Q = δ_cen
fbecc8c Clean up repository: remove old versions and temp files
```

---

## Mathematical Summary

### Classical CRNT
- Deficiency δ = n - ℓ - rank(N) where n = complexes, ℓ = linkage classes, N = stoichiometric matrix
- Deficiency Zero Theorem: δ = 0 + weak reversibility ⟹ unique equilibrium in each stoichiometric class
- Deficiency One Theorem: Conditions for multiple equilibria

### Quantum CRNT
- Quantum deficiency δ_Q = dim(ker L) - 1
- Commutant deficiency δ_com = dim(A_int') - 1
- Central deficiency δ_cen = dim(Z(A_int)) - 1
- Structural deficiency δ_struct = #SCCs - 1

### Key Results
1. **Universal**: δ_Q = δ_com (Evans-Høegh-Krohn)
2. **Characterization**: δ_Q = δ_cen ⟺ multiplicity-free
3. **Hierarchy**: δ_struct ≤ δ_cen ≤ δ_com = δ_Q
4. **Gaps**:
   - Structural gap = δ_cen - δ_struct (hidden block structure)
   - Multiplicity gap = δ_com - δ_cen (noiseless subsystems)

---

## Build Status

```
✅ lake build completed successfully
```

---

## Next Steps

1. **Fill remaining sorry**: `ergodic_peripheral_trivial` (requires Mathlib spectral theory development)
2. **Prove axioms**: Convert key axioms to theorems as Mathlib infrastructure grows
3. **Publication**: Submit papers to journals
4. **Extensions**: Infinite-dimensional QMS, non-detailed-balance regime
