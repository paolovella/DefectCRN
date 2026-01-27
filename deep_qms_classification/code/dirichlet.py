"""
Dirichlet Form Computation for QMS Classification

This module computes:
- The GNS inner product ⟨A, B⟩_σ
- The Dirichlet form E(A, B)
- Detailed balance verification
- Candidate rank invariants

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Optional
from dataclasses import dataclass


def dagger(A: np.ndarray) -> np.ndarray:
    """Conjugate transpose."""
    return A.conj().T


def sqrtm_psd(A: np.ndarray) -> np.ndarray:
    """Matrix square root for positive semidefinite matrix."""
    return linalg.sqrtm(A)


def gns_inner_product(A: np.ndarray, B: np.ndarray, sigma: np.ndarray) -> complex:
    """
    Compute the GNS inner product ⟨A, B⟩_σ = Tr(σ^{1/2} A† σ^{1/2} B).

    This is the natural inner product for σ-detailed balance.

    Parameters:
        A, B: Matrices (operators)
        sigma: Faithful state (positive definite density matrix)

    Returns:
        The GNS inner product value
    """
    sigma_sqrt = sqrtm_psd(sigma)
    return np.trace(sigma_sqrt @ dagger(A) @ sigma_sqrt @ B)


def hilbert_schmidt_inner_product(A: np.ndarray, B: np.ndarray) -> complex:
    """
    Standard Hilbert-Schmidt inner product ⟨A, B⟩_HS = Tr(A† B).
    """
    return np.trace(dagger(A) @ B)


def construct_dual_lindbladian(H: np.ndarray,
                               jump_ops: List[np.ndarray]) -> callable:
    """
    Construct the dual Lindbladian L* (Heisenberg picture).

    L*(X) = i[H, X] + Σ_k (L_k† X L_k - (1/2){L_k† L_k, X})

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators

    Returns:
        Function L_star(X) computing the dual action
    """
    def L_star(X: np.ndarray) -> np.ndarray:
        n = H.shape[0]
        result = 1j * (H @ X - X @ H)  # i[H, X]

        for L_k in jump_ops:
            Lk_dag = dagger(L_k)
            Lk_dag_Lk = Lk_dag @ L_k

            result += Lk_dag @ X @ L_k
            result -= 0.5 * (Lk_dag_Lk @ X + X @ Lk_dag_Lk)

        return result

    return L_star


def check_detailed_balance(H: np.ndarray,
                           jump_ops: List[np.ndarray],
                           sigma: np.ndarray,
                           tol: float = 1e-8) -> Tuple[bool, float]:
    """
    Check if the Lindbladian satisfies σ-detailed balance.

    Condition: ⟨A, L*(B)⟩_σ = ⟨L*(A), B⟩_σ for all A, B

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        sigma: Candidate stationary state
        tol: Numerical tolerance

    Returns:
        (is_detailed_balance, max_violation)
    """
    n = H.shape[0]
    L_star = construct_dual_lindbladian(H, jump_ops)

    # Test on a basis of matrices
    max_violation = 0.0

    # Standard matrix basis E_{ij}
    for i in range(n):
        for j in range(n):
            E_ij = np.zeros((n, n), dtype=complex)
            E_ij[i, j] = 1.0

            for k in range(n):
                for l in range(n):
                    E_kl = np.zeros((n, n), dtype=complex)
                    E_kl[k, l] = 1.0

                    lhs = gns_inner_product(E_ij, L_star(E_kl), sigma)
                    rhs = gns_inner_product(L_star(E_ij), E_kl, sigma)

                    violation = np.abs(lhs - rhs)
                    max_violation = max(max_violation, violation)

    return max_violation < tol, max_violation


def compute_dirichlet_form(H: np.ndarray,
                           jump_ops: List[np.ndarray],
                           sigma: np.ndarray) -> callable:
    """
    Compute the Dirichlet form E(A, B) = -⟨A, L*(B)⟩_σ.

    For σ-detailed balance, this is symmetric and non-negative.

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        sigma: Faithful stationary state

    Returns:
        Function E(A, B) computing the Dirichlet form
    """
    L_star = construct_dual_lindbladian(H, jump_ops)

    def dirichlet_form(A: np.ndarray, B: np.ndarray) -> complex:
        return -gns_inner_product(A, L_star(B), sigma)

    return dirichlet_form


def dirichlet_form_matrix(H: np.ndarray,
                          jump_ops: List[np.ndarray],
                          sigma: np.ndarray) -> np.ndarray:
    """
    Construct the matrix representation of the Dirichlet form.

    In the standard basis {E_{ij}}, this gives the n²×n² matrix D
    such that E(A, B) = vec(A)† D vec(B).

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        sigma: Faithful stationary state

    Returns:
        The n²×n² Dirichlet form matrix
    """
    n = H.shape[0]
    E = compute_dirichlet_form(H, jump_ops, sigma)

    D = np.zeros((n*n, n*n), dtype=complex)

    for i in range(n):
        for j in range(n):
            E_ij = np.zeros((n, n), dtype=complex)
            E_ij[i, j] = 1.0
            idx_ij = i * n + j

            for k in range(n):
                for l in range(n):
                    E_kl = np.zeros((n, n), dtype=complex)
                    E_kl[k, l] = 1.0
                    idx_kl = k * n + l

                    D[idx_ij, idx_kl] = E(E_ij, E_kl)

    return D


def dirichlet_rank(H: np.ndarray,
                   jump_ops: List[np.ndarray],
                   sigma: np.ndarray,
                   tol: float = 1e-10) -> int:
    """
    Compute the rank of the Dirichlet form.

    This is a candidate for the "rank term" in deficiency.

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        sigma: Faithful stationary state
        tol: Numerical tolerance

    Returns:
        Rank of the Dirichlet form matrix
    """
    D = dirichlet_form_matrix(H, jump_ops, sigma)
    singular_values = linalg.svdvals(D)
    return int(np.sum(singular_values > tol))


def dissipator_rank(jump_ops: List[np.ndarray], tol: float = 1e-10) -> int:
    """
    Compute the rank of the dissipator D* = Σ_k L_k (·) L_k†.

    Alternative candidate for rank term.

    Parameters:
        jump_ops: List of jump operators
        tol: Numerical tolerance

    Returns:
        Rank of the dissipator
    """
    if not jump_ops:
        return 0

    n = jump_ops[0].shape[0]

    # Construct the dissipator superoperator matrix
    # D*(X) = Σ_k L_k† X L_k
    # vec(D*(X)) = Σ_k (L_k^T ⊗ L_k†) vec(X)
    D_super = np.zeros((n*n, n*n), dtype=complex)

    for L_k in jump_ops:
        Lk_dag = dagger(L_k)
        D_super += np.kron(L_k.T, Lk_dag)

    singular_values = linalg.svdvals(D_super)
    return int(np.sum(singular_values > tol))


@dataclass
class DirichletFormInfo:
    """Complete information about the Dirichlet form."""
    is_detailed_balance: bool
    max_db_violation: float
    dirichlet_rank: int
    dissipator_rank: int
    kernel_dimension: int  # dim ker(Dirichlet form)


def analyze_dirichlet_form(H: np.ndarray,
                           jump_ops: List[np.ndarray],
                           sigma: np.ndarray,
                           tol: float = 1e-10) -> DirichletFormInfo:
    """
    Complete analysis of the Dirichlet form.

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        sigma: Faithful stationary state
        tol: Numerical tolerance

    Returns:
        DirichletFormInfo with all computed data
    """
    is_db, violation = check_detailed_balance(H, jump_ops, sigma, tol)

    D = dirichlet_form_matrix(H, jump_ops, sigma)
    singular_values = linalg.svdvals(D)
    d_rank = int(np.sum(singular_values > tol))
    kernel_dim = D.shape[0] - d_rank

    diss_rank = dissipator_rank(jump_ops, tol)

    return DirichletFormInfo(
        is_detailed_balance=is_db,
        max_db_violation=violation,
        dirichlet_rank=d_rank,
        dissipator_rank=diss_rank,
        kernel_dimension=kernel_dim
    )


# ============================================================================
# Test Cases
# ============================================================================

def test_thermal_state():
    """
    Test: Thermal state with detailed balance.

    For a system at inverse temperature β with Hamiltonian H,
    the Gibbs state σ = e^{-βH}/Z satisfies detailed balance
    for the appropriate jump operators.
    """
    n = 2
    beta = 1.0
    omega = 1.0

    # Two-level system
    H = omega * np.array([[0, 0], [0, 1]], dtype=complex)

    # Thermal state
    Z = np.trace(linalg.expm(-beta * H))
    sigma = linalg.expm(-beta * H) / Z

    # For detailed balance, we need L_k = sqrt(γ_k) exp(-β E_k/2) |k⟩⟨k+1|
    # Simplified: use standard amplitude damping (won't satisfy DB perfectly)
    gamma_down = 0.5
    gamma_up = gamma_down * np.exp(-beta * omega)  # Detailed balance condition

    L_down = np.sqrt(gamma_down) * np.array([[0, 1], [0, 0]], dtype=complex)
    L_up = np.sqrt(gamma_up) * np.array([[0, 0], [1, 0]], dtype=complex)

    info = analyze_dirichlet_form(H, [L_down, L_up], sigma)

    print("Thermal Two-Level System:")
    print(f"  Detailed balance: {info.is_detailed_balance}")
    print(f"  Max DB violation: {info.max_db_violation:.2e}")
    print(f"  Dirichlet rank: {info.dirichlet_rank}")
    print(f"  Dissipator rank: {info.dissipator_rank}")
    print(f"  Kernel dim: {info.kernel_dimension}")
    print()

    return info


def test_pure_dephasing_dirichlet():
    """
    Test: Pure dephasing (commutes with H, satisfies detailed balance).
    """
    n = 3
    omega = np.array([1.0, 2.0, 3.0])

    H = np.diag(omega.astype(complex))

    # Uniform stationary state (maximally mixed)
    sigma = np.eye(n, dtype=complex) / n

    # Dephasing operators
    gamma = 0.1
    L = np.sqrt(gamma) * np.diag([1, -1, 0]).astype(complex)

    info = analyze_dirichlet_form(H, [L], sigma)

    print("Pure Dephasing (3-level):")
    print(f"  Detailed balance: {info.is_detailed_balance}")
    print(f"  Max DB violation: {info.max_db_violation:.2e}")
    print(f"  Dirichlet rank: {info.dirichlet_rank}")
    print(f"  Dissipator rank: {info.dissipator_rank}")
    print(f"  Kernel dim: {info.kernel_dimension}")
    print()

    return info


def test_non_detailed_balance():
    """
    Test: System that does NOT satisfy detailed balance.
    """
    n = 2

    H = np.array([[1, 0.5], [0.5, 2]], dtype=complex)
    L = np.array([[0, 1], [0, 0]], dtype=complex)  # Decay only

    # Try with uniform state (should fail detailed balance)
    sigma = np.eye(n, dtype=complex) / n

    info = analyze_dirichlet_form(H, [L], sigma)

    print("Non-Detailed-Balance System:")
    print(f"  Detailed balance: {info.is_detailed_balance}")
    print(f"  Max DB violation: {info.max_db_violation:.2e}")
    print(f"  Dirichlet rank: {info.dirichlet_rank}")
    print(f"  Dissipator rank: {info.dissipator_rank}")
    print()

    return info


if __name__ == "__main__":
    print("=" * 60)
    print("Dirichlet Form Tests")
    print("=" * 60)
    print()

    test_thermal_state()
    test_pure_dephasing_dirichlet()
    test_non_detailed_balance()
