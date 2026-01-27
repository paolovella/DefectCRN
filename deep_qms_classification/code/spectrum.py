"""
Lindbladian Spectrum Computation for QMS Classification

This module computes:
- The Lindbladian superoperator L
- The spectrum of L
- The peripheral spectrum (Re(λ) = 0)
- The asymptotic algebra A_∞

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Optional
from dataclasses import dataclass


def vec(A: np.ndarray) -> np.ndarray:
    """Vectorize a matrix (column-major order)."""
    return A.flatten('F')


def unvec(v: np.ndarray, n: int) -> np.ndarray:
    """Unvectorize to n×n matrix."""
    return v.reshape((n, n), order='F')


def dagger(A: np.ndarray) -> np.ndarray:
    """Conjugate transpose."""
    return A.conj().T


def construct_lindbladian(H: np.ndarray,
                          jump_ops: List[np.ndarray]) -> np.ndarray:
    """
    Construct the Lindbladian superoperator in matrix form.

    L(ρ) = -i[H, ρ] + Σ_k (L_k ρ L_k† - (1/2){L_k† L_k, ρ})

    In vectorized form: L|ρ⟩⟩ = L_super |ρ⟩⟩

    Parameters:
        H: Hamiltonian (n×n Hermitian)
        jump_ops: List of jump operators L_k

    Returns:
        L_super: The n²×n² superoperator matrix
    """
    n = H.shape[0]
    I = np.eye(n, dtype=complex)

    # Hamiltonian part: -i[H, ρ] = -i(H ρ - ρ H)
    # vec(-i H ρ) = -i (I ⊗ H) vec(ρ)
    # vec(-i (-ρ H)) = i (H^T ⊗ I) vec(ρ)
    L_H = -1j * (np.kron(I, H) - np.kron(H.T, I))

    # Dissipator part: Σ_k (L_k ρ L_k† - (1/2){L_k† L_k, ρ})
    L_D = np.zeros((n*n, n*n), dtype=complex)

    for L_k in jump_ops:
        Lk_dag = dagger(L_k)
        Lk_dag_Lk = Lk_dag @ L_k

        # L_k ρ L_k† → (L_k†.T ⊗ L_k) vec(ρ) = (L_k*.conj() ⊗ L_k)
        L_D += np.kron(L_k.conj(), L_k)

        # -(1/2) L_k† L_k ρ → -(1/2)(I ⊗ L_k† L_k)
        L_D -= 0.5 * np.kron(I, Lk_dag_Lk)

        # -(1/2) ρ L_k† L_k → -(1/2)((L_k† L_k)^T ⊗ I)
        L_D -= 0.5 * np.kron(Lk_dag_Lk.T, I)

    return L_H + L_D


def compute_spectrum(L_super: np.ndarray,
                     tol: float = 1e-10) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute the spectrum of the Lindbladian.

    Parameters:
        L_super: The n²×n² Lindbladian superoperator
        tol: Numerical tolerance

    Returns:
        eigenvalues: Array of eigenvalues
        eigenvectors: Matrix with eigenvectors as columns
    """
    eigenvalues, eigenvectors = linalg.eig(L_super)

    # Sort by real part (descending, so 0 comes first)
    idx = np.argsort(-eigenvalues.real)
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    return eigenvalues, eigenvectors


def peripheral_spectrum(eigenvalues: np.ndarray,
                        tol: float = 1e-10) -> np.ndarray:
    """
    Extract the peripheral spectrum {λ : Re(λ) = 0}.

    For a proper Lindbladian, all eigenvalues have Re(λ) ≤ 0.
    The peripheral spectrum corresponds to non-decaying modes.

    Parameters:
        eigenvalues: Array of Lindbladian eigenvalues
        tol: Numerical tolerance for Re(λ) ≈ 0

    Returns:
        Array of peripheral eigenvalues
    """
    peripheral_mask = np.abs(eigenvalues.real) < tol
    return eigenvalues[peripheral_mask]


def stationary_states(L_super: np.ndarray,
                      tol: float = 1e-10) -> List[np.ndarray]:
    """
    Find all stationary states (density matrices with L(ρ) = 0).

    Parameters:
        L_super: The Lindbladian superoperator
        tol: Numerical tolerance

    Returns:
        List of stationary density matrices
    """
    n_sq = L_super.shape[0]
    n = int(np.sqrt(n_sq))

    eigenvalues, eigenvectors = compute_spectrum(L_super, tol)

    stationary = []
    for i, lam in enumerate(eigenvalues):
        if np.abs(lam) < tol:
            # This is a stationary state
            rho_vec = eigenvectors[:, i]
            rho = unvec(rho_vec, n)

            # Normalize to be a density matrix (trace 1, positive)
            # First, make Hermitian
            rho = (rho + dagger(rho)) / 2

            # Check if positive semidefinite
            eigs = linalg.eigvalsh(rho)
            if np.all(eigs > -tol):
                # Normalize trace
                tr = np.trace(rho)
                if np.abs(tr) > tol:
                    stationary.append(rho / tr)

    return stationary


def quantum_deficiency(L_super: np.ndarray, tol: float = 1e-10) -> int:
    """
    Compute the quantum deficiency δ_Q = dim(ker L) - 1.

    Parameters:
        L_super: The Lindbladian superoperator
        tol: Numerical tolerance

    Returns:
        Quantum deficiency δ_Q
    """
    eigenvalues, _ = compute_spectrum(L_super, tol)

    # Count zero eigenvalues
    zero_count = np.sum(np.abs(eigenvalues) < tol)

    return int(zero_count - 1)


def peripheral_eigenspace_dimension(L_super: np.ndarray,
                                     tol: float = 1e-10) -> int:
    """
    Compute the dimension of the peripheral eigenspace.

    This is related to the asymptotic algebra A_∞.

    Parameters:
        L_super: The Lindbladian superoperator
        tol: Numerical tolerance

    Returns:
        Dimension of peripheral eigenspace
    """
    eigenvalues, _ = compute_spectrum(L_super, tol)
    peripheral = peripheral_spectrum(eigenvalues, tol)
    return len(peripheral)


@dataclass
class LindbladianSpectrumInfo:
    """Complete spectral information about a Lindbladian."""
    dimension: int  # n for n×n density matrices
    eigenvalues: np.ndarray
    peripheral_eigenvalues: np.ndarray
    spectral_gap: float  # -max{Re(λ) : Re(λ) < 0}
    quantum_deficiency: int
    peripheral_dim: int


def analyze_lindbladian_spectrum(H: np.ndarray,
                                  jump_ops: List[np.ndarray],
                                  tol: float = 1e-10) -> LindbladianSpectrumInfo:
    """
    Complete spectral analysis of a Lindbladian.

    Parameters:
        H: Hamiltonian
        jump_ops: List of jump operators
        tol: Numerical tolerance

    Returns:
        LindbladianSpectrumInfo with all spectral data
    """
    n = H.shape[0]
    L_super = construct_lindbladian(H, jump_ops)
    eigenvalues, _ = compute_spectrum(L_super, tol)

    peripheral = peripheral_spectrum(eigenvalues, tol)

    # Compute spectral gap
    non_peripheral = eigenvalues[np.abs(eigenvalues.real) >= tol]
    if len(non_peripheral) > 0:
        gap = -np.max(non_peripheral.real)
    else:
        gap = 0.0

    delta_Q = quantum_deficiency(L_super, tol)

    return LindbladianSpectrumInfo(
        dimension=n,
        eigenvalues=eigenvalues,
        peripheral_eigenvalues=peripheral,
        spectral_gap=gap,
        quantum_deficiency=delta_Q,
        peripheral_dim=len(peripheral)
    )


# ============================================================================
# Test Cases
# ============================================================================

def test_two_level_amplitude_damping():
    """
    Test: 2-level amplitude damping
    Expected: Unique stationary state (ground state), δ_Q = 0
    """
    omega, gamma = 1.0, 0.5

    e0 = np.array([[1], [0]], dtype=complex)
    e1 = np.array([[0], [1]], dtype=complex)

    H = omega * (e1 @ e1.T.conj())
    L = np.sqrt(gamma) * (e0 @ e1.T.conj())

    info = analyze_lindbladian_spectrum(H, [L])

    print("2-Level Amplitude Damping:")
    print(f"  Eigenvalues: {np.sort(info.eigenvalues.real)[:4]}...")
    print(f"  Peripheral: {info.peripheral_eigenvalues}")
    print(f"  Spectral gap: {info.spectral_gap:.4f}")
    print(f"  δ_Q = {info.quantum_deficiency}")
    print(f"  Expected: δ_Q = 0")
    print()

    return info


def test_pure_dephasing():
    """
    Test: 3-level pure dephasing
    Expected: Multiple stationary states (all diagonal), δ_Q = n-1 = 2
    """
    n = 3
    omega = np.array([1.0, 2.0, 3.0])
    gamma = np.array([0.5, 0.7, 0.3])

    H = np.diag(omega.astype(complex))
    L = np.diag(np.sqrt(gamma).astype(complex))

    info = analyze_lindbladian_spectrum(H, [L])

    print(f"{n}-Level Pure Dephasing:")
    print(f"  Eigenvalues (first 5): {np.sort(info.eigenvalues.real)[:5]}")
    print(f"  Peripheral: {info.peripheral_eigenvalues}")
    print(f"  Spectral gap: {info.spectral_gap:.4f}")
    print(f"  δ_Q = {info.quantum_deficiency}")
    print(f"  Expected: δ_Q = {n-1}")
    print()

    return info


def test_two_blocks():
    """
    Test: Two decoupled 2×2 blocks
    Expected: Two independent stationary states, δ_Q = 1
    """
    H = np.zeros((4, 4), dtype=complex)
    H[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])

    L1 = np.zeros((4, 4), dtype=complex)
    L1[0, 1] = 1.0

    L2 = np.zeros((4, 4), dtype=complex)
    L2[2, 3] = 1.0

    info = analyze_lindbladian_spectrum(H, [L1, L2])

    print("Two Decoupled 2×2 Blocks:")
    print(f"  Peripheral: {info.peripheral_eigenvalues}")
    print(f"  Spectral gap: {info.spectral_gap:.4f}")
    print(f"  δ_Q = {info.quantum_deficiency}")
    print(f"  Expected: δ_Q = 1")
    print()

    return info


if __name__ == "__main__":
    print("=" * 60)
    print("Lindbladian Spectrum Tests")
    print("=" * 60)
    print()

    test_two_level_amplitude_damping()
    test_pure_dephasing()
    test_two_blocks()
