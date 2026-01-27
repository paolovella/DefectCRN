"""
Structural Deficiency Computation for QMS Classification

This module computes:
- The quantum network graph G from (H, {L_k})
- The test set S*(G)
- The structural commutant C(S*(G))
- The structural deficiency δ_struct

The key question: Does δ_cen = δ_struct always?

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Set, Optional
from dataclasses import dataclass


def dagger(A: np.ndarray) -> np.ndarray:
    """Conjugate transpose."""
    return A.conj().T


def matrix_unit(n: int, i: int, j: int) -> np.ndarray:
    """
    Create the matrix unit E_{ij} with 1 in position (i,j) and 0 elsewhere.
    """
    E = np.zeros((n, n), dtype=complex)
    E[i, j] = 1.0
    return E


def commutator(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Compute [A, B] = AB - BA."""
    return A @ B - B @ A


def extract_graph_from_lindbladian(H: np.ndarray,
                                   jump_ops: List[np.ndarray],
                                   tol: float = 1e-10) -> Tuple[Set[Tuple[int, int]], Set[Tuple[int, int]]]:
    """
    Extract the quantum network graph from a Lindbladian.

    Parameters:
        H: Hamiltonian (Hermitian matrix)
        jump_ops: List of jump operators
        tol: Numerical tolerance for detecting nonzero entries

    Returns:
        (coherent_edges, jump_edges) where:
        - coherent_edges: set of (i, j) where H_ij ≠ 0
        - jump_edges: set of (i, j) where some (L_k)_ji ≠ 0 (transition i → j)
    """
    n = H.shape[0]

    # Coherent edges from Hamiltonian
    coherent_edges = set()
    for i in range(n):
        for j in range(n):
            if i != j and np.abs(H[i, j]) > tol:
                coherent_edges.add((i, j))

    # Jump edges from jump operators
    # If (L_k)_ji ≠ 0, this represents transition i → j
    jump_edges = set()
    for L in jump_ops:
        for i in range(n):
            for j in range(n):
                if np.abs(L[j, i]) > tol:  # L_ji ≠ 0 means i → j transition
                    jump_edges.add((i, j))

    return coherent_edges, jump_edges


def compute_test_set(n: int,
                     coherent_edges: Set[Tuple[int, int]],
                     jump_edges: Set[Tuple[int, int]]) -> List[np.ndarray]:
    """
    Compute the test set S*(G).

    For coherent edges (i, j): include E_ij and E_ji
    For jump edges (i, j): include E_ji and E_ij

    The test set includes both directions for each edge type.

    Parameters:
        n: Matrix dimension
        coherent_edges: Set of coherent edges
        jump_edges: Set of jump edges

    Returns:
        List of matrix units in the test set
    """
    test_set_indices = set()

    # From coherent edges: both directions
    for (i, j) in coherent_edges:
        test_set_indices.add((i, j))
        test_set_indices.add((j, i))

    # From jump edges: both directions
    # If (i, j) is a jump edge (transition i → j), add E_ji and E_ij
    for (i, j) in jump_edges:
        test_set_indices.add((j, i))  # E_ji
        test_set_indices.add((i, j))  # E_ij

    # Convert to matrices
    test_set = [matrix_unit(n, i, j) for (i, j) in test_set_indices]

    return test_set


def compute_structural_commutant(n: int,
                                 test_set: List[np.ndarray],
                                 tol: float = 1e-10) -> List[np.ndarray]:
    """
    Compute the structural commutant C(S*(G)).

    This is the set of all matrices X such that [X, E] = 0 for all E in test_set.

    Parameters:
        n: Matrix dimension
        test_set: List of matrix units in S*(G)
        tol: Numerical tolerance

    Returns:
        Orthonormal basis for the structural commutant
    """
    if not test_set:
        # Empty test set means commutant is all matrices
        basis = []
        for i in range(n):
            for j in range(n):
                basis.append(matrix_unit(n, i, j))
        return basis

    # Build the constraint matrix
    # X commutes with all E in test_set iff vec([X, E]) = 0 for all E
    # [X, E] = XE - EX
    # vec([X, E]) = (E^T ⊗ I - I ⊗ E) vec(X)

    constraint_rows = []
    for E in test_set:
        # Commutator constraint: [X, E] = 0
        # (E^T ⊗ I - I ⊗ E) vec(X) = 0
        I_n = np.eye(n, dtype=complex)
        comm_op = np.kron(E.T, I_n) - np.kron(I_n, E)
        constraint_rows.append(comm_op)

    # Stack all constraints
    M = np.vstack(constraint_rows)

    # Find null space using SVD
    U, S, Vh = linalg.svd(M, full_matrices=True)

    # Null space vectors are rows of Vh with zero singular values
    null_mask = S < tol
    rank = np.sum(~null_mask)
    null_dim = Vh.shape[0] - rank

    if null_dim == 0:
        return []

    # Null space is spanned by last null_dim rows of Vh
    null_vectors = Vh[rank:, :]

    # Convert back to matrices
    commutant_basis = []
    for k in range(null_vectors.shape[0]):
        X_vec = null_vectors[k, :]
        X = X_vec.reshape((n, n), order='F')  # Column-major (Fortran order)
        commutant_basis.append(X)

    # Orthonormalize with Frobenius inner product
    return gram_schmidt_matrices(commutant_basis, tol)


def gram_schmidt_matrices(matrices: List[np.ndarray], tol: float = 1e-10) -> List[np.ndarray]:
    """
    Gram-Schmidt orthonormalization for matrices using Frobenius inner product.
    """
    result = []
    for M in matrices:
        v = M.copy().astype(complex)
        for basis_elem in result:
            coeff = np.trace(dagger(basis_elem) @ v)
            v = v - coeff * basis_elem

        norm = np.sqrt(np.abs(np.trace(dagger(v) @ v)))
        if norm > tol:
            result.append(v / norm)

    return result


def structural_deficiency(H: np.ndarray,
                          jump_ops: List[np.ndarray],
                          tol: float = 1e-10) -> int:
    """
    Compute the structural deficiency δ_struct = dim(C(S*(G))) - 1.

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        tol: Numerical tolerance

    Returns:
        Structural deficiency δ_struct
    """
    n = H.shape[0]

    # Extract graph
    coherent_edges, jump_edges = extract_graph_from_lindbladian(H, jump_ops, tol)

    # Compute test set
    test_set = compute_test_set(n, coherent_edges, jump_edges)

    # Compute structural commutant
    commutant_basis = compute_structural_commutant(n, test_set, tol)

    return len(commutant_basis) - 1


@dataclass
class StructuralInfo:
    """Complete structural information about a Lindbladian."""
    n_coherent_edges: int
    n_jump_edges: int
    test_set_size: int
    commutant_dim: int
    structural_deficiency: int
    graph_is_connected: bool


def analyze_structure(H: np.ndarray,
                      jump_ops: List[np.ndarray],
                      tol: float = 1e-10) -> StructuralInfo:
    """
    Complete structural analysis of a Lindbladian.
    """
    n = H.shape[0]

    coherent_edges, jump_edges = extract_graph_from_lindbladian(H, jump_ops, tol)
    test_set = compute_test_set(n, coherent_edges, jump_edges)
    commutant_basis = compute_structural_commutant(n, test_set, tol)

    # Check connectivity using union-find
    all_edges = coherent_edges | jump_edges | {(j, i) for (i, j) in jump_edges}
    is_connected = check_connected(n, all_edges)

    return StructuralInfo(
        n_coherent_edges=len(coherent_edges),
        n_jump_edges=len(jump_edges),
        test_set_size=len(test_set),
        commutant_dim=len(commutant_basis),
        structural_deficiency=len(commutant_basis) - 1,
        graph_is_connected=is_connected
    )


def check_connected(n: int, edges: Set[Tuple[int, int]]) -> bool:
    """Check if the graph is connected using BFS."""
    if n <= 1:
        return True

    # Build adjacency list
    adj = {i: set() for i in range(n)}
    for (i, j) in edges:
        adj[i].add(j)
        adj[j].add(i)

    # BFS from vertex 0
    visited = {0}
    queue = [0]
    while queue:
        v = queue.pop(0)
        for u in adj[v]:
            if u not in visited:
                visited.add(u)
                queue.append(u)

    return len(visited) == n


def count_connected_components(n: int, edges: Set[Tuple[int, int]]) -> int:
    """Count the number of connected components."""
    if n == 0:
        return 0

    # Build adjacency list
    adj = {i: set() for i in range(n)}
    for (i, j) in edges:
        adj[i].add(j)
        adj[j].add(i)

    visited = set()
    components = 0

    for start in range(n):
        if start not in visited:
            components += 1
            # BFS
            queue = [start]
            while queue:
                v = queue.pop(0)
                if v not in visited:
                    visited.add(v)
                    for u in adj[v]:
                        if u not in visited:
                            queue.append(u)

    return components


# ============================================================================
# Comparison with Central Deficiency
# ============================================================================

def compare_deficiencies(H: np.ndarray,
                         jump_ops: List[np.ndarray],
                         tol: float = 1e-10) -> Tuple[int, int, bool]:
    """
    Compare central deficiency and structural deficiency.

    Returns:
        (δ_cen, δ_struct, are_equal)
    """
    from algebra import central_deficiency as compute_delta_cen

    delta_cen = compute_delta_cen(H, jump_ops, tol)
    delta_struct = structural_deficiency(H, jump_ops, tol)

    return delta_cen, delta_struct, delta_cen == delta_struct


# ============================================================================
# Test Cases
# ============================================================================

def test_two_level_amplitude_damping():
    """
    Test: 2-level amplitude damping

    Jump operator L = √γ |0⟩⟨1| has nonzero entry L[0,1].
    This means jump edge 1 → 0.
    Test set: {E_01, E_10}
    Structural commutant: matrices commuting with E_01 and E_10 = scalar multiples of I
    Expected: δ_struct = 0
    """
    omega, gamma = 1.0, 0.5

    e0 = np.array([[1], [0]], dtype=complex)
    e1 = np.array([[0], [1]], dtype=complex)

    H = omega * (e1 @ e1.T.conj())
    L = np.sqrt(gamma) * (e0 @ e1.T.conj())

    info = analyze_structure(H, [L])
    delta_cen, delta_struct, equal = compare_deficiencies(H, [L])

    print("2-Level Amplitude Damping:")
    print(f"  Coherent edges: {info.n_coherent_edges}")
    print(f"  Jump edges: {info.n_jump_edges}")
    print(f"  Test set size: {info.test_set_size}")
    print(f"  Commutant dim: {info.commutant_dim}")
    print(f"  δ_struct = {delta_struct}")
    print(f"  δ_cen = {delta_cen}")
    print(f"  Equal: {equal}")
    print()

    return info


def test_pure_dephasing():
    """
    Test: 3-level pure dephasing

    H and L are both diagonal, so no off-diagonal entries.
    Test set: empty (no edges!)
    Structural commutant: all matrices (trivially)
    But that can't be right...

    Actually, diagonal L means L[j,i] = 0 for i ≠ j, so no jump edges.
    This gives δ_struct = n² - 1 = 8 for n=3.

    But δ_cen = 2 (center of diagonal algebra is diagonal = n-dim).

    This shows δ_struct ≠ δ_cen in general!
    """
    n = 3
    omega = np.array([1.0, 2.0, 3.0])
    gamma = np.array([0.5, 0.7, 0.3])

    H = np.diag(omega.astype(complex))
    L = np.diag(np.sqrt(gamma).astype(complex))

    info = analyze_structure(H, [L])
    delta_cen, delta_struct, equal = compare_deficiencies(H, [L])

    print("3-Level Pure Dephasing:")
    print(f"  Coherent edges: {info.n_coherent_edges}")
    print(f"  Jump edges: {info.n_jump_edges}")
    print(f"  Test set size: {info.test_set_size}")
    print(f"  Commutant dim: {info.commutant_dim}")
    print(f"  δ_struct = {delta_struct}")
    print(f"  δ_cen = {delta_cen}")
    print(f"  Equal: {equal}")
    print(f"  NOTE: This is a case where δ_struct ≠ δ_cen!")
    print()

    return info


def test_two_blocks():
    """
    Test: Two decoupled 2×2 blocks with full algebra in each block.
    """
    H = np.zeros((4, 4), dtype=complex)
    H[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])

    L1 = np.zeros((4, 4), dtype=complex)
    L1[0, 1] = 1.0

    L2 = np.zeros((4, 4), dtype=complex)
    L2[2, 3] = 1.0

    info = analyze_structure(H, [L1, L2])
    delta_cen, delta_struct, equal = compare_deficiencies(H, [L1, L2])

    print("Two Decoupled 2×2 Blocks:")
    print(f"  Coherent edges: {info.n_coherent_edges}")
    print(f"  Jump edges: {info.n_jump_edges}")
    print(f"  Test set size: {info.test_set_size}")
    print(f"  Commutant dim: {info.commutant_dim}")
    print(f"  δ_struct = {delta_struct}")
    print(f"  δ_cen = {delta_cen}")
    print(f"  Equal: {equal}")
    print()

    return info


def test_full_dephasing_with_offdiagonal():
    """
    Test: Dephasing with off-diagonal jump operator.

    This should give δ_struct = δ_cen.
    """
    n = 2
    H = np.array([[1, 0], [0, 2]], dtype=complex)

    # Dephasing operator with off-diagonal part
    L = np.array([[1, 0.5], [0.5, -1]], dtype=complex)

    info = analyze_structure(H, [L])
    delta_cen, delta_struct, equal = compare_deficiencies(H, [L])

    print("Dephasing with Off-Diagonal:")
    print(f"  Coherent edges: {info.n_coherent_edges}")
    print(f"  Jump edges: {info.n_jump_edges}")
    print(f"  Test set size: {info.test_set_size}")
    print(f"  Commutant dim: {info.commutant_dim}")
    print(f"  δ_struct = {delta_struct}")
    print(f"  δ_cen = {delta_cen}")
    print(f"  Equal: {equal}")
    print()

    return info


if __name__ == "__main__":
    print("=" * 60)
    print("Structural Deficiency Tests")
    print("=" * 60)
    print()

    test_two_level_amplitude_damping()
    test_pure_dephasing()
    test_two_blocks()
    test_full_dephasing_with_offdiagonal()

    print("=" * 60)
    print("KEY FINDING: δ_struct ≠ δ_cen in general!")
    print("Pure dephasing shows the difference clearly.")
    print("=" * 60)
