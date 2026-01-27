"""
Deep Comparison: δ_cen vs δ_struct

Phase 1 of the research plan: systematically compare central deficiency
with structural deficiency across many examples.

Key question: Does δ_cen = δ_struct always? If not, characterize the gap.

Author: Paolo Vella
"""

import numpy as np
from typing import List, Tuple, Dict
from dataclasses import dataclass

from algebra import analyze_interaction_algebra, InteractionAlgebraInfo
from spectrum import analyze_lindbladian_spectrum, LindbladianSpectrumInfo
from structural import (
    analyze_structure, StructuralInfo,
    extract_graph_from_lindbladian, compute_test_set,
    structural_deficiency
)


def dagger(A: np.ndarray) -> np.ndarray:
    return A.conj().T


def ket(n: int, i: int) -> np.ndarray:
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


def projector(n: int, i: int) -> np.ndarray:
    v = ket(n, i)
    return v @ dagger(v)


# Pauli matrices
sigma_x = np.array([[0, 1], [1, 0]], dtype=complex)
sigma_y = np.array([[0, -1j], [1j, 0]], dtype=complex)
sigma_z = np.array([[1, 0], [0, -1]], dtype=complex)


@dataclass
class ComparisonResult:
    """Result of comparing δ_cen and δ_struct."""
    name: str
    n: int
    delta_cen: int
    delta_struct: int
    delta_Q: int
    algebra_dim: int
    center_dim: int
    commutant_dim: int
    test_set_size: int
    are_equal: bool
    notes: str


def compare_example(name: str,
                    H: np.ndarray,
                    jump_ops: List[np.ndarray],
                    notes: str = "") -> ComparisonResult:
    """Run full comparison on an example."""
    n = H.shape[0]

    # Algebra analysis
    alg_info = analyze_interaction_algebra(H, jump_ops)

    # Spectrum analysis
    spec_info = analyze_lindbladian_spectrum(H, jump_ops)

    # Structural analysis
    struct_info = analyze_structure(H, jump_ops)

    return ComparisonResult(
        name=name,
        n=n,
        delta_cen=alg_info.central_deficiency,
        delta_struct=struct_info.structural_deficiency,
        delta_Q=spec_info.quantum_deficiency,
        algebra_dim=alg_info.dim_algebra,
        center_dim=alg_info.dim_center,
        commutant_dim=struct_info.commutant_dim,
        test_set_size=struct_info.test_set_size,
        are_equal=(alg_info.central_deficiency == struct_info.structural_deficiency),
        notes=notes
    )


# ============================================================================
# Test Case Collection
# ============================================================================

def test_cases() -> List[ComparisonResult]:
    """Generate all test cases for comparison."""
    results = []

    # === 2-Level Systems ===

    # 1. Amplitude damping
    H = projector(2, 1)
    L = np.sqrt(0.5) * (ket(2, 0) @ dagger(ket(2, 1)))
    results.append(compare_example(
        "2L: Amplitude Damping", H, [L],
        "Standard decay, should have δ=0"
    ))

    # 2. Pure dephasing (diagonal L)
    H = sigma_z
    L = np.sqrt(0.5) * sigma_z
    results.append(compare_example(
        "2L: Pure Dephasing (σz)", H, [L],
        "Diagonal L, abelian algebra"
    ))

    # 3. Coherent only (no dissipation)
    H = sigma_x
    results.append(compare_example(
        "2L: Coherent Only (σx)", H, [],
        "No jump operators, just coherent evolution"
    ))

    # 4. Thermal bath
    omega = 1.0
    beta = 1.0
    gamma_down = 0.5
    gamma_up = gamma_down * np.exp(-beta * omega)
    H = omega * projector(2, 1)
    L_down = np.sqrt(gamma_down) * (ket(2, 0) @ dagger(ket(2, 1)))
    L_up = np.sqrt(gamma_up) * (ket(2, 1) @ dagger(ket(2, 0)))
    results.append(compare_example(
        "2L: Thermal Bath", H, [L_down, L_up],
        "Up and down transitions"
    ))

    # 5. Off-diagonal jump only
    H = np.zeros((2, 2), dtype=complex)
    L = sigma_x  # Off-diagonal
    results.append(compare_example(
        "2L: Off-diagonal L (σx)", H, [L],
        "Non-diagonal jump operator"
    ))

    # === 3-Level Systems ===

    # 6. Pure dephasing 3-level
    H = np.diag([1.0, 2.0, 3.0]).astype(complex)
    L = np.diag([0.5, 0.7, 0.3]).astype(complex)
    results.append(compare_example(
        "3L: Pure Dephasing", H, [L],
        "All diagonal, δ=2 expected"
    ))

    # 7. V-system (cascade decay)
    H = np.diag([0.0, 1.0, 2.0]).astype(complex)
    L1 = np.sqrt(0.5) * (ket(3, 0) @ dagger(ket(3, 1)))  # 1→0
    L2 = np.sqrt(0.5) * (ket(3, 1) @ dagger(ket(3, 2)))  # 2→1
    results.append(compare_example(
        "3L: V-system (cascade)", H, [L1, L2],
        "Cascade 2→1→0"
    ))

    # 8. Lambda system (two paths to ground)
    H = np.diag([0.0, 1.0, 2.0]).astype(complex)
    L1 = np.sqrt(0.5) * (ket(3, 0) @ dagger(ket(3, 1)))  # 1→0
    L2 = np.sqrt(0.5) * (ket(3, 0) @ dagger(ket(3, 2)))  # 2→0
    results.append(compare_example(
        "3L: Lambda (both to ground)", H, [L1, L2],
        "Both excited states decay to ground"
    ))

    # 9. 3-cycle
    L1 = np.sqrt(0.5) * (ket(3, 1) @ dagger(ket(3, 0)))  # 0→1
    L2 = np.sqrt(0.5) * (ket(3, 2) @ dagger(ket(3, 1)))  # 1→2
    L3 = np.sqrt(0.5) * (ket(3, 0) @ dagger(ket(3, 2)))  # 2→0
    results.append(compare_example(
        "3L: Cycle 0→1→2→0", np.zeros((3, 3), dtype=complex), [L1, L2, L3],
        "Circular transitions"
    ))

    # === 4-Level Systems (Block Structure) ===

    # 10. Two 2×2 blocks (decoupled)
    H = np.zeros((4, 4), dtype=complex)
    H[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])
    L1 = np.zeros((4, 4), dtype=complex)
    L1[0, 1] = 1.0
    L2 = np.zeros((4, 4), dtype=complex)
    L2[2, 3] = 1.0
    results.append(compare_example(
        "4L: Two 2×2 blocks", H, [L1, L2],
        "Decoupled blocks, δ=1 expected"
    ))

    # 11. One large block
    H = np.array([
        [1, 0.5, 0, 0],
        [0.5, 2, 0.3, 0],
        [0, 0.3, 3, 0.2],
        [0, 0, 0.2, 4]
    ], dtype=complex)
    L = np.zeros((4, 4), dtype=complex)
    L[0, 3] = 1.0  # 3→0 decay
    results.append(compare_example(
        "4L: Connected chain", H, [L],
        "All connected via H"
    ))

    # 12. Diagonal only (4 levels)
    H = np.diag([1.0, 2.0, 3.0, 4.0]).astype(complex)
    L = np.diag([0.5, 0.7, 0.3, 0.9]).astype(complex)
    results.append(compare_example(
        "4L: Pure Dephasing", H, [L],
        "Diagonal, δ=3 expected"
    ))

    # === Edge Cases ===

    # 13. Identity Hamiltonian
    H = np.eye(2, dtype=complex)
    L = np.sqrt(0.5) * (ket(2, 0) @ dagger(ket(2, 1)))
    results.append(compare_example(
        "2L: H=I (trivial H)", H, [L],
        "H proportional to identity"
    ))

    # 14. Zero Hamiltonian, diagonal L
    H = np.zeros((3, 3), dtype=complex)
    L = np.diag([1.0, -1.0, 0.0]).astype(complex)
    results.append(compare_example(
        "3L: H=0, diagonal L", H, [L],
        "No coherent evolution"
    ))

    # 15. Complex phases in H
    H = np.array([[0, 1j], [-1j, 0]], dtype=complex)  # σy-like
    L = np.sqrt(0.5) * (ket(2, 0) @ dagger(ket(2, 1)))
    results.append(compare_example(
        "2L: σy Hamiltonian", H, [L],
        "Imaginary off-diagonal H"
    ))

    # 16. Multiple identical jumps
    L1 = np.sqrt(0.3) * (ket(2, 0) @ dagger(ket(2, 1)))
    L2 = np.sqrt(0.2) * (ket(2, 0) @ dagger(ket(2, 1)))
    results.append(compare_example(
        "2L: Two parallel jumps", np.zeros((2, 2), dtype=complex), [L1, L2],
        "Same transition, different rates"
    ))

    # 17. Rank-1 projective jump
    psi = (ket(2, 0) + ket(2, 1)) / np.sqrt(2)
    L = psi @ dagger(psi)  # |+⟩⟨+|
    results.append(compare_example(
        "2L: Projective L=|+⟩⟨+|", np.zeros((2, 2), dtype=complex), [L],
        "Rank-1 jump operator"
    ))

    # 18. Full matrix L
    L = (sigma_x + 1j * sigma_y + sigma_z) / np.sqrt(3)
    results.append(compare_example(
        "2L: Full matrix L", np.zeros((2, 2), dtype=complex), [L],
        "General 2×2 jump"
    ))

    return results


def run_comparison(verbose: bool = True) -> List[ComparisonResult]:
    """Run full comparison suite."""
    results = test_cases()

    if verbose:
        print("=" * 80)
        print("PHASE 1: Deep Comparison of δ_cen vs δ_struct")
        print("=" * 80)
        print()

        # Summary table header
        print(f"{'Name':<30} {'n':>2} {'δ_cen':>6} {'δ_struct':>8} {'δ_Q':>4} {'Equal':>6}")
        print("-" * 60)

        for r in results:
            eq_str = "✓" if r.are_equal else "✗"
            print(f"{r.name:<30} {r.n:>2} {r.delta_cen:>6} {r.delta_struct:>8} {r.delta_Q:>4} {eq_str:>6}")

        print()
        print("=" * 80)
        print("SUMMARY")
        print("=" * 80)

        n_total = len(results)
        n_equal = sum(1 for r in results if r.are_equal)
        n_differ = n_total - n_equal

        print(f"Total examples: {n_total}")
        print(f"δ_cen = δ_struct: {n_equal}")
        print(f"δ_cen ≠ δ_struct: {n_differ}")

        if n_differ > 0:
            print()
            print("Cases where δ_cen ≠ δ_struct:")
            for r in results:
                if not r.are_equal:
                    print(f"  - {r.name}: δ_cen={r.delta_cen}, δ_struct={r.delta_struct}")
                    print(f"    Notes: {r.notes}")
                    print(f"    dim(A_int)={r.algebra_dim}, dim(Z)={r.center_dim}, dim(C)={r.commutant_dim}")

        # Check if δ_cen ≤ δ_struct always
        all_le = all(r.delta_cen <= r.delta_struct for r in results)
        all_ge = all(r.delta_cen >= r.delta_struct for r in results)

        print()
        if all_le:
            print("OBSERVATION: δ_cen ≤ δ_struct in all cases")
        elif all_ge:
            print("OBSERVATION: δ_cen ≥ δ_struct in all cases")
        else:
            print("OBSERVATION: Neither δ_cen ≤ δ_struct nor δ_cen ≥ δ_struct holds universally")

    return results


def detailed_analysis(result: ComparisonResult, H: np.ndarray, jump_ops: List[np.ndarray]):
    """Print detailed analysis of a specific case."""
    print(f"\nDETAILED ANALYSIS: {result.name}")
    print("=" * 60)

    print(f"\nHamiltonian H:")
    print(H)

    print(f"\nJump operators:")
    for i, L in enumerate(jump_ops):
        print(f"L_{i}:")
        print(L)

    # Graph structure
    coherent_edges, jump_edges = extract_graph_from_lindbladian(H, jump_ops)
    print(f"\nGraph structure:")
    print(f"  Coherent edges: {coherent_edges}")
    print(f"  Jump edges: {jump_edges}")

    test_set = compute_test_set(H.shape[0], coherent_edges, jump_edges)
    print(f"  Test set size: {len(test_set)}")

    # Invariants
    print(f"\nInvariants:")
    print(f"  dim(A_int) = {result.algebra_dim}")
    print(f"  dim(Z(A_int)) = {result.center_dim}")
    print(f"  dim(C(S*(G))) = {result.commutant_dim}")
    print(f"  δ_cen = {result.delta_cen}")
    print(f"  δ_struct = {result.delta_struct}")
    print(f"  δ_Q = {result.delta_Q}")

    if not result.are_equal:
        print(f"\n  *** DIFFERENCE: δ_cen ≠ δ_struct ***")
        gap = result.delta_struct - result.delta_cen
        print(f"  Gap: δ_struct - δ_cen = {gap}")


if __name__ == "__main__":
    results = run_comparison(verbose=True)
