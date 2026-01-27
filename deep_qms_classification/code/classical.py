"""
Classical Reduction: Markov Chains as QMS

This module verifies that for classical Markov chains embedded as QMS:
- δ_cen = ℓ - 1 (number of connected components minus 1)
- The classical deficiency formula is recovered

A classical Markov chain with rate matrix Q = (q_ij) is embedded as:
- H = 0 (no coherent dynamics)
- L_{ij} = √q_{ij} |j⟩⟨i| for each transition i → j

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Set, Dict
from dataclasses import dataclass

from algebra import analyze_interaction_algebra
from spectrum import analyze_lindbladian_spectrum
from structural import analyze_structure, count_connected_components


def dagger(A: np.ndarray) -> np.ndarray:
    return A.conj().T


def ket(n: int, i: int) -> np.ndarray:
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


# ============================================================================
# Classical Markov Chain Construction
# ============================================================================

def embed_markov_chain(Q: np.ndarray) -> Tuple[np.ndarray, List[np.ndarray]]:
    """
    Embed a classical Markov chain as a QMS.

    Parameters:
        Q: Rate matrix (n×n) with Q_ij = rate from i to j for i≠j,
           Q_ii = -Σ_{j≠i} Q_ij

    Returns:
        (H, jump_ops) where H = 0 and jump_ops = [√q_ij |j⟩⟨i| for i≠j]
    """
    n = Q.shape[0]
    H = np.zeros((n, n), dtype=complex)

    jump_ops = []
    for i in range(n):
        for j in range(n):
            if i != j and Q[i, j] > 0:
                # Transition i → j with rate Q[i,j]
                L = np.sqrt(Q[i, j]) * (ket(n, j) @ dagger(ket(n, i)))
                jump_ops.append(L)

    return H, jump_ops


def extract_graph_edges(Q: np.ndarray, tol: float = 1e-10) -> Set[Tuple[int, int]]:
    """
    Extract edges from rate matrix.
    Edge (i, j) exists if Q[i, j] > 0 (transition i → j).
    """
    n = Q.shape[0]
    edges = set()
    for i in range(n):
        for j in range(n):
            if i != j and Q[i, j] > tol:
                edges.add((i, j))
    return edges


def count_linkage_classes(Q: np.ndarray, tol: float = 1e-10) -> int:
    """
    Count the number of connected components (linkage classes).
    Treats the graph as undirected.
    """
    n = Q.shape[0]
    edges = extract_graph_edges(Q, tol)

    # Make undirected
    undirected_edges = set()
    for (i, j) in edges:
        undirected_edges.add((i, j))
        undirected_edges.add((j, i))

    return count_connected_components(n, undirected_edges)


@dataclass
class ClassicalChainInfo:
    """Information about a classical Markov chain."""
    n: int                    # Number of states
    n_edges: int              # Number of transitions
    n_linkage_classes: int    # ℓ = number of connected components
    expected_delta: int       # ℓ - 1
    actual_delta_cen: int
    actual_delta_Q: int
    classical_matches: bool


def analyze_classical_chain(Q: np.ndarray, name: str = "",
                           tol: float = 1e-10) -> ClassicalChainInfo:
    """
    Analyze a classical Markov chain and verify classical reduction.
    """
    n = Q.shape[0]

    # Embed as QMS
    H, jump_ops = embed_markov_chain(Q)

    # Count graph structure
    edges = extract_graph_edges(Q, tol)
    n_edges = len(edges)
    n_classes = count_linkage_classes(Q, tol)

    # Compute invariants
    alg_info = analyze_interaction_algebra(H, jump_ops, tol)
    spec_info = analyze_lindbladian_spectrum(H, jump_ops, tol)

    expected = n_classes - 1
    matches = (alg_info.central_deficiency == expected and
               spec_info.quantum_deficiency == expected)

    return ClassicalChainInfo(
        n=n,
        n_edges=n_edges,
        n_linkage_classes=n_classes,
        expected_delta=expected,
        actual_delta_cen=alg_info.central_deficiency,
        actual_delta_Q=spec_info.quantum_deficiency,
        classical_matches=matches
    )


# ============================================================================
# Standard Classical Examples
# ============================================================================

def birth_death_chain(n: int, birth_rate: float = 1.0,
                      death_rate: float = 1.0) -> np.ndarray:
    """
    Birth-death chain on {0, 1, ..., n-1}.
    Transitions: i → i+1 (birth) and i → i-1 (death).
    """
    Q = np.zeros((n, n))
    for i in range(n):
        if i < n - 1:
            Q[i, i + 1] = birth_rate
        if i > 0:
            Q[i, i - 1] = death_rate
        Q[i, i] = -Q[i, :].sum()
    return Q


def complete_graph_chain(n: int, rate: float = 1.0) -> np.ndarray:
    """
    Markov chain on complete graph (all-to-all transitions).
    """
    Q = rate * np.ones((n, n))
    np.fill_diagonal(Q, 0)
    for i in range(n):
        Q[i, i] = -Q[i, :].sum()
    return Q


def cycle_chain(n: int, rate: float = 1.0, bidirectional: bool = True) -> np.ndarray:
    """
    Markov chain on cycle graph: 0 → 1 → 2 → ... → n-1 → 0.
    """
    Q = np.zeros((n, n))
    for i in range(n):
        Q[i, (i + 1) % n] = rate
        if bidirectional:
            Q[i, (i - 1) % n] = rate
    for i in range(n):
        Q[i, i] = -Q[i, :].sum()
    return Q


def two_component_chain(n1: int, n2: int, rate: float = 1.0) -> np.ndarray:
    """
    Two disconnected components of sizes n1 and n2.
    Each component is a complete graph.
    """
    n = n1 + n2
    Q = np.zeros((n, n))

    # Component 1: complete graph on {0, ..., n1-1}
    for i in range(n1):
        for j in range(n1):
            if i != j:
                Q[i, j] = rate

    # Component 2: complete graph on {n1, ..., n-1}
    for i in range(n1, n):
        for j in range(n1, n):
            if i != j:
                Q[i, j] = rate

    for i in range(n):
        Q[i, i] = -Q[i, :].sum()
    return Q


def three_component_chain() -> np.ndarray:
    """
    Three disconnected components: {0}, {1,2}, {3,4,5}.
    """
    n = 6
    Q = np.zeros((n, n))

    # Component 1: singleton {0}
    # (no transitions)

    # Component 2: {1, 2}
    Q[1, 2] = 1.0
    Q[2, 1] = 1.0

    # Component 3: {3, 4, 5} complete
    for i in [3, 4, 5]:
        for j in [3, 4, 5]:
            if i != j:
                Q[i, j] = 1.0

    for i in range(n):
        Q[i, i] = -Q[i, :].sum()
    return Q


# ============================================================================
# Classical Reduction Verification
# ============================================================================

def verify_classical_reduction(verbose: bool = True) -> List[ClassicalChainInfo]:
    """
    Verify δ_cen = ℓ - 1 for various classical Markov chains.
    """
    examples = [
        ("Birth-Death (3)", birth_death_chain(3)),
        ("Birth-Death (5)", birth_death_chain(5)),
        ("Complete Graph (3)", complete_graph_chain(3)),
        ("Complete Graph (4)", complete_graph_chain(4)),
        ("Cycle (4, bidirectional)", cycle_chain(4, bidirectional=True)),
        ("Cycle (5, unidirectional)", cycle_chain(5, bidirectional=False)),
        ("Two Components (2+2)", two_component_chain(2, 2)),
        ("Two Components (2+3)", two_component_chain(2, 3)),
        ("Three Components", three_component_chain()),
    ]

    results = []
    for name, Q in examples:
        info = analyze_classical_chain(Q, name)
        results.append((name, info))

    if verbose:
        print("=" * 70)
        print("CLASSICAL REDUCTION VERIFICATION")
        print("=" * 70)
        print()
        print(f"{'Name':<30} {'n':>3} {'ℓ':>3} {'δ_exp':>6} {'δ_cen':>6} {'δ_Q':>5} {'Match':>6}")
        print("-" * 70)

        for name, info in results:
            match_str = "✓" if info.classical_matches else "✗"
            print(f"{name:<30} {info.n:>3} {info.n_linkage_classes:>3} "
                  f"{info.expected_delta:>6} {info.actual_delta_cen:>6} "
                  f"{info.actual_delta_Q:>5} {match_str:>6}")

        print()
        n_total = len(results)
        n_pass = sum(1 for _, info in results if info.classical_matches)
        print(f"Passed: {n_pass}/{n_total}")

        if n_pass == n_total:
            print("\n*** CLASSICAL REDUCTION VERIFIED: δ_cen = ℓ - 1 ***")
        else:
            print("\n*** WARNING: Some cases failed! ***")
            for name, info in results:
                if not info.classical_matches:
                    print(f"  Failed: {name}")
                    print(f"    Expected δ = ℓ - 1 = {info.expected_delta}")
                    print(f"    Got δ_cen = {info.actual_delta_cen}, δ_Q = {info.actual_delta_Q}")

    return [info for _, info in results]


# ============================================================================
# Detailed Analysis
# ============================================================================

def detailed_classical_analysis(Q: np.ndarray, name: str = ""):
    """
    Print detailed analysis of a classical Markov chain embedding.
    """
    print(f"\n{'='*60}")
    print(f"DETAILED ANALYSIS: {name}")
    print("=" * 60)

    n = Q.shape[0]
    print(f"\nRate matrix Q ({n}×{n}):")
    print(Q)

    H, jump_ops = embed_markov_chain(Q)
    print(f"\nEmbedded as QMS with {len(jump_ops)} jump operators")

    edges = extract_graph_edges(Q)
    print(f"\nGraph edges: {edges}")
    print(f"Number of edges: {len(edges)}")

    n_classes = count_linkage_classes(Q)
    print(f"Number of linkage classes: {n_classes}")

    alg_info = analyze_interaction_algebra(H, jump_ops)
    print(f"\nAlgebra analysis:")
    print(f"  dim(A_int) = {alg_info.dim_algebra}")
    print(f"  dim(Z(A_int)) = {alg_info.dim_center}")
    print(f"  δ_cen = {alg_info.central_deficiency}")

    spec_info = analyze_lindbladian_spectrum(H, jump_ops)
    print(f"\nSpectral analysis:")
    print(f"  δ_Q = {spec_info.quantum_deficiency}")
    print(f"  Spectral gap = {spec_info.spectral_gap:.4f}")

    print(f"\nClassical formula verification:")
    print(f"  Expected: δ = ℓ - 1 = {n_classes - 1}")
    print(f"  Actual: δ_cen = {alg_info.central_deficiency}, δ_Q = {spec_info.quantum_deficiency}")
    if alg_info.central_deficiency == n_classes - 1:
        print("  ✓ Classical reduction holds!")
    else:
        print("  ✗ Mismatch!")


if __name__ == "__main__":
    verify_classical_reduction(verbose=True)

    # Detailed analysis of specific examples
    print("\n" + "=" * 70)
    print("DETAILED EXAMPLES")
    print("=" * 70)

    detailed_classical_analysis(two_component_chain(2, 2), "Two Components (2+2)")
    detailed_classical_analysis(three_component_chain(), "Three Components")
