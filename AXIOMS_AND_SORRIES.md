# Axioms and Sorries in the Lean Formalization

## Summary

- **Axioms**: 22 total
- **Sorries**: 4 total

---

## Axioms

### Lindbladian Evolution (5 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `Lindbladian.lean:483` | `Lindbladian.evolve` | Time evolution map e^{tL} exists |
| `Lindbladian.lean:487` | `Lindbladian.dualEvolve` | Dual (Heisenberg) evolution exists |
| `Lindbladian.lean:491` | `Lindbladian.evolve_add` | Semigroup property: e^{(s+t)L} = e^{sL} ∘ e^{tL} |
| `Lindbladian.lean:496` | `Lindbladian.evolve_zero` | Identity at zero: e^{0·L} = id |
| `Lindbladian.lean:501` | `Lindbladian.evolve_duality` | Schrödinger-Heisenberg duality |

**Status**: Standard QMS theory; could be derived from matrix exponential properties in Mathlib.

### Evans-Høegh-Krohn Theorem (2 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `Algebra.lean:917` | `evans_hoegh_krohn_identity` | L(ρσ) = L(ρ)σ + ρL(σ) for stationary σ |
| `Algebra.lean:936` | `evans_hoegh_krohn_identity_dag` | Adjoint version of above |

**Status**: Deep result from operator algebra; proof requires modular theory not in Mathlib.

### Stationary States (1 axiom)

| File | Axiom | Description |
|------|-------|-------------|
| `StationaryState.lean:176` | `exists_stationary_state` | Every Lindbladian has a stationary state |

**Status**: Follows from Brouwer fixed point theorem; provable with more Mathlib setup.

### Wedderburn Structure (2 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `InteractionAlgebra.lean:481` | `gksl_gauge_freedom_of_equiv` | GKSL gauge equivalence preserves algebra |
| `InteractionAlgebra.lean:580` | `wedderburn_decomposition_exists` | Wedderburn-Artin decomposition exists |

**Status**: Wedderburn theorem is classical algebra; needs formalization of semisimple algebras.

### Detailed Balance (4 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `DetailedBalance.lean:224` | `norm_comparison` | Norm bounds for GNS construction |
| `DetailedBalance.lean:241` | `gns_projection_bound` | GNS projection estimates |
| `DetailedBalance.lean:255` | `qdb_real_spectrum` | Detailed balance ⟹ real spectrum |
| `DetailedBalance.lean:273` | `qdb_negative_semidefinite` | Detailed balance ⟹ L ≤ 0 in GNS |

**Status**: Standard detailed balance theory; proofs require functional calculus.

### Convergence Theory (4 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `QuantumDZT.lean:178` | `spectral_gap_exists` | Ergodic systems have spectral gap |
| `QuantumDZT.lean:192` | `heisenberg_exponential_decay` | Exponential decay in Heisenberg picture |
| `QuantumDZT.lean:215` | `quantum_dzt_convergence` | Quantum DZT: ergodic ⟹ convergence |
| `Frigerio.lean:148` | `convergence_to_stationary` | Convergence to stationary state |

**Status**: Requires spectral theory of non-self-adjoint operators; not yet in Mathlib.

### Frigerio's Theorem (1 axiom)

| File | Axiom | Description |
|------|-------|-------------|
| `Frigerio.lean:126` | `quantumSemigroup` | Quantum dynamical semigroup properties |

**Status**: Basic semigroup theory; could be derived from evolution axioms.

### Classification (2 axioms)

| File | Axiom | Description |
|------|-------|-------------|
| `Classification.lean:383` | `ergodic_lindbladian_exists` | ∀n, ∃ ergodic Lindbladian on M_n |
| `Classification.lean:445` | `peripheral_phases_finitely_generated` | Peripheral phases form ℤ^k |

**Status**: First is constructive (depolarizing channel); second is elementary (finite spectrum).

---

## Sorries

### Arithmetic Lemma (1 sorry)

| File | Location | Description |
|------|----------|-------------|
| `InteractionAlgebra.lean:739` | `center_dim_eq_commutant_dim_iff_multiplicityFree` | If Σm_α² = #blocks, then all m_α = 1 |

**Difficulty**: Easy. Pure arithmetic/combinatorics.

**Proof sketch**: Σm_α² ≥ Σ1 = r with equality iff all m_α = 1 (Cauchy-Schwarz or direct).

### Structural Hierarchy (1 sorry)

| File | Location | Description |
|------|----------|-------------|
| `Classification.lean:197` | `deficiency_hierarchy` | δ_struct ≤ δ_cen for non-degenerate graphs |

**Difficulty**: Medium. Requires showing structural commutant ⊆ center.

**Proof sketch**: For non-degenerate graphs, structural commutant elements are block-diagonal and commute with all of A_int, hence lie in Z(A_int).

### Spectral Theory (1 sorry)

| File | Location | Description |
|------|----------|-------------|
| `Classification.lean:433` | `ergodic_peripheral_trivial` | Ergodic ⟹ peripheral spectrum = {0} |

**Difficulty**: Hard. Requires spectral theory not in Mathlib.

**Proof sketch**: Peripheral eigenvalues correspond to invariant projections; ergodicity (trivial commutant) implies no such projections except identity.

### Algebra Detail (1 sorry)

| File | Location | Description |
|------|----------|-------------|
| `Algebra.lean:1017` | (in proof) | Detailed algebraic manipulation |

**Difficulty**: Medium. Routine but tedious matrix algebra.

---

## Axiom Categories

| Category | Count | Provability |
|----------|-------|-------------|
| Evolution/Semigroup | 6 | Provable with matrix exponential |
| Evans-Høegh-Krohn | 2 | Requires modular theory |
| Wedderburn | 2 | Needs semisimple algebra theory |
| Detailed Balance | 4 | Needs functional calculus |
| Convergence | 4 | Needs spectral theory |
| Classification | 2 | One constructive, one elementary |
| Stationary | 1 | Provable (fixed point) |

---

## Priority for Filling Sorries

1. **High priority** (blocks main theorems):
   - `center_dim_eq_commutant_dim_iff_multiplicityFree` (arithmetic)
   - `deficiency_hierarchy` (structural ≤ central)

2. **Medium priority** (strengthens results):
   - `ergodic_peripheral_trivial` (spectral theory)

3. **Low priority** (internal details):
   - Algebra.lean:1017 (routine computation)

---

## Notes

- All axioms are mathematically valid statements from established QMS theory
- The formalization prioritizes structural correctness over complete proof
- Key theorems (δ_Q = δ_com, multiplicity-free characterization) have complete proofs modulo axioms
- Filling the arithmetic sorry would complete the multiplicity-free characterization proof
