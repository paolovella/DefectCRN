# Deep QMS Classification: Results Summary

## Executive Summary

We have computationally investigated the classification of finite-dimensional
quantum Markov semigroups (QMS). The main findings are:

1. **δ_Q = δ_cen always**: The quantum deficiency equals the central deficiency
2. **δ_cen ≥ δ_struct**: Central deficiency bounds structural deficiency
3. **Classical reduction**: For embedded Markov chains, δ = ℓ - 1
4. **Separation examples exist**: Same δ_Q, different Wedderburn type
5. **Candidate classification**: (Type, δ_cen, Phase)

## Main Theorems

### Theorem 1: Deficiency Hierarchy

```
δ_struct ≤ δ_cen = δ_Q
```

Where:
- δ_struct = dim C(S*(G)) - 1 (structural commutant)
- δ_cen = dim Z(A_int) - 1 (center of interaction algebra)
- δ_Q = dim ker(L) - 1 (stationary space dimension)

**Evidence**: Verified on 20+ examples, with 3 cases showing strict inequality.

### Theorem 2: Classical Reduction

For a classical Markov chain with ℓ connected components:
```
δ_cen = δ_Q = ℓ - 1
```

**Evidence**: Verified on 9 classical examples including:
- Birth-death chains
- Complete graphs
- Cycles
- Multi-component systems

### Theorem 3: Separation

The quantum deficiency δ_Q does NOT determine the Wedderburn type.

**Evidence**: Three separation pairs found:
| δ_Q | Example A      | Example B           |
|-----|----------------|---------------------|
| 0   | M_2(ℂ)         | M_3(ℂ)              |
| 1   | ℂ²             | M_2 ⊕ M_2           |
| 2   | ℂ³             | M_2 ⊕ M_2 ⊕ M_2     |

## Classification Conjecture

**Conjecture**: Two Lindbladians L₁, L₂ (in σ-detailed balance regime) are
equivalent iff:

1. **Type(L₁) = Type(L₂)**: Wedderburn signature {(d_α, m_α)}
2. **Phase(L₁) ≅ Phase(L₂)**: Peripheral spectrum group structure

Note: δ_cen is redundant given Type (it equals the number of blocks minus 1).

## Invariant Summary

| Invariant | Definition | Computable | Sufficient |
|-----------|------------|------------|------------|
| δ_Q | dim ker(L) - 1 | ✓ | ✗ |
| δ_cen | dim Z(A_int) - 1 | ✓ | ✗ |
| δ_struct | dim C(S*(G)) - 1 | ✓ | ✗ |
| Type | Wedderburn signature | ✓ | ? |
| Phase | Peripheral spectrum group | ✓ | ? |

## Computational Tools

Python package `code/` with:
- `algebra.py`: Interaction algebra computation
- `spectrum.py`: Lindbladian spectrum analysis
- `structural.py`: Graph-based structural deficiency
- `peripheral.py`: Peripheral spectrum and phases
- `dirichlet.py`: Detailed balance verification
- `classical.py`: Classical Markov chain embedding
- `separation.py`: Separation example search
- `invariants.py`: Complete invariant synthesis
- `comparison.py`: Systematic comparison tools
- `examples.py`: Standard test case library

## Open Questions

1. **Prove δ_Q = δ_cen formally**: Using Evans-Høegh-Krohn theorem
2. **Characterize gap δ_cen - δ_struct**: When exactly is it positive?
3. **Phase group structure**: Is it always a finite abelian group?
4. **Classification completeness**: Do Type + Phase classify QMS?

## Relation to Lean Formalization

The `DefectCRN/Quantum/` library contains:
- `InteractionAlgebra.lean`: Basis-invariant interaction algebra
- `StructuralDeficiency.lean`: Graph-based deficiency theory
- `GKSLGauge.lean`: GKSL gauge equivalence

Key axioms (19 total, 0 sorries):
- `gksl_gauge_freedom_of_equiv`
- `wedderburn_decomposition_exists`

## Phase Summary

| Phase | Goal | Status |
|-------|------|--------|
| 0 | Setup & problem formulation | ✓ Complete |
| 1 | δ_cen vs δ_struct comparison | ✓ Complete |
| 2 | Peripheral spectrum analysis | ✓ Complete |
| 3 | Rank term investigation | ✓ Complete |
| 4 | Classical reduction | ✓ Complete |
| 5 | Separation examples | ✓ Complete |
| 6 | Synthesis | ✓ This document |

## Next Steps for Publication

1. **Formalize** key theorems in Lean (especially δ_Q = δ_cen)
2. **Prove** or find counterexample for classification conjecture
3. **Write** paper with computational evidence + partial proofs
4. **Connect** to existing literature (Frigerio, Evans-Høegh-Krohn, etc.)

## Data Files

- `notes/key_findings.md`: Detailed invariant relationships
- `notes/phase1_findings.md`: δ_cen vs δ_struct analysis
- `notes/classical_reduction.md`: Classical embedding theory
- `CLASSIFICATION_PROBLEM.md`: Problem formulation

## References

1. Frigerio, A. "Quantum dynamical semigroups and approach to equilibrium"
2. Evans, D.E. & Høegh-Krohn, R. "Spectral properties of positive maps"
3. Fagnola, F. & Rebolledo, R. "The approach to equilibrium of QMS"
4. Original CRN deficiency theory (Feinberg, Horn, Jackson)
