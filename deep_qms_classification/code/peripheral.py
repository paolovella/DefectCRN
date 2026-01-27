"""
Peripheral Spectrum Analysis for QMS Classification

This module analyzes:
- The peripheral spectrum {λ : Re(λ) = 0} ∩ Spec(L)
- The phase group structure
- The asymptotic algebra A_∞

Key question: What is the structure of the peripheral spectrum?
Is it always a finite (abelian) group under multiplication?

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Set, Optional
from dataclasses import dataclass
from collections import defaultdict

from spectrum import construct_lindbladian, compute_spectrum


def dagger(A: np.ndarray) -> np.ndarray:
    return A.conj().T


def find_peripheral_eigenvalues(L_super: np.ndarray,
                                tol: float = 1e-10) -> np.ndarray:
    """
    Find all eigenvalues on the imaginary axis (Re(λ) ≈ 0).
    """
    eigenvalues, _ = compute_spectrum(L_super, tol)
    peripheral_mask = np.abs(eigenvalues.real) < tol
    return eigenvalues[peripheral_mask]


def extract_imaginary_parts(peripheral_eigenvalues: np.ndarray,
                            tol: float = 1e-10) -> np.ndarray:
    """
    Extract the imaginary parts (phases) of peripheral eigenvalues.
    """
    return peripheral_eigenvalues.imag


def find_phase_group_generators(phases: np.ndarray,
                                tol: float = 1e-10) -> List[float]:
    """
    Find generators for the additive group of phases.

    The phases form a finitely generated subgroup of ℝ.
    For finite-dimensional systems, this should be a discrete group
    (multiples of some base frequency).

    Returns list of fundamental frequencies.
    """
    if len(phases) == 0:
        return []

    # Remove duplicates and zero
    unique_phases = []
    for p in phases:
        is_new = True
        for up in unique_phases:
            if np.abs(p - up) < tol:
                is_new = False
                break
        if is_new and np.abs(p) > tol:
            unique_phases.append(p)

    if not unique_phases:
        return [0.0]

    # Find GCD-like structure using continued fractions
    # For rational multiples, find the base period
    unique_phases = sorted(unique_phases, key=abs)

    # Simple approach: find the smallest nonzero phase as candidate generator
    generators = []
    remaining = list(unique_phases)

    while remaining:
        # Find smallest absolute value
        min_idx = np.argmin([abs(p) for p in remaining])
        gen = remaining.pop(min_idx)

        if abs(gen) < tol:
            continue

        generators.append(gen)

        # Remove multiples of this generator
        new_remaining = []
        for p in remaining:
            ratio = p / gen
            if abs(ratio - round(ratio)) > tol:
                new_remaining.append(p)
        remaining = new_remaining

    return generators if generators else [0.0]


def analyze_phase_group_structure(phases: np.ndarray,
                                  tol: float = 1e-10) -> Tuple[int, List[float]]:
    """
    Analyze the structure of the phase group.

    Returns:
        (rank, generators) where:
        - rank is the rank of the free abelian group
        - generators are the fundamental frequencies
    """
    generators = find_phase_group_generators(phases, tol)
    generators = [g for g in generators if abs(g) > tol]
    return len(generators), generators


def check_group_closure(phases: np.ndarray, tol: float = 1e-10) -> bool:
    """
    Check if the phases form a group under addition (mod 2π).

    For a proper QMS, the peripheral phases should be closed under:
    - Addition (if λ, μ are phases, so is λ+μ)
    - Negation (if λ is a phase, so is -λ)
    """
    unique_phases = set()
    for p in phases:
        # Normalize to unique representative
        found = False
        for up in unique_phases:
            if np.abs(p - up) < tol:
                found = True
                break
        if not found:
            unique_phases.add(p)

    phase_list = list(unique_phases)

    # Check closure under addition
    for p1 in phase_list:
        for p2 in phase_list:
            p_sum = p1 + p2
            # Check if p_sum is in the set (mod 2π for periodic systems)
            found = False
            for p in phase_list:
                if np.abs(p_sum - p) < tol:
                    found = True
                    break
                # Also check mod 2π
                if np.abs((p_sum - p) % (2 * np.pi)) < tol:
                    found = True
                    break
            if not found and abs(p_sum) > tol:
                return False

    # Check closure under negation
    for p in phase_list:
        neg_found = False
        for q in phase_list:
            if np.abs(-p - q) < tol:
                neg_found = True
                break
        if not neg_found and abs(p) > tol:
            return False

    return True


@dataclass
class PeripheralSpectrumInfo:
    """Complete information about the peripheral spectrum."""
    n_peripheral: int
    eigenvalues: np.ndarray
    phases: np.ndarray
    unique_phases: np.ndarray
    phase_group_rank: int
    generators: List[float]
    is_trivial: bool  # Only λ=0
    has_oscillations: bool  # Non-zero imaginary parts


def analyze_peripheral_spectrum(H: np.ndarray,
                                jump_ops: List[np.ndarray],
                                tol: float = 1e-10) -> PeripheralSpectrumInfo:
    """
    Complete analysis of the peripheral spectrum.
    """
    L_super = construct_lindbladian(H, jump_ops)
    peripheral = find_peripheral_eigenvalues(L_super, tol)
    phases = extract_imaginary_parts(peripheral, tol)

    # Find unique phases
    unique_phases = []
    for p in phases:
        is_new = True
        for up in unique_phases:
            if np.abs(p - up) < tol:
                is_new = False
                break
        if is_new:
            unique_phases.append(p)
    unique_phases = np.array(unique_phases)

    rank, generators = analyze_phase_group_structure(phases, tol)

    is_trivial = len(peripheral) == 1 and np.abs(peripheral[0]) < tol
    has_oscillations = any(np.abs(p) > tol for p in phases)

    return PeripheralSpectrumInfo(
        n_peripheral=len(peripheral),
        eigenvalues=peripheral,
        phases=phases,
        unique_phases=unique_phases,
        phase_group_rank=rank,
        generators=generators,
        is_trivial=is_trivial,
        has_oscillations=has_oscillations
    )


# ============================================================================
# Test Cases
# ============================================================================

def ket(n: int, i: int) -> np.ndarray:
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


def test_ergodic_system():
    """
    Ergodic system with unique stationary state.
    Expected: only λ=0 on peripheral spectrum.
    """
    n = 2
    H = np.array([[0, 0], [0, 1]], dtype=complex)
    L = np.sqrt(0.5) * (ket(n, 0) @ dagger(ket(n, 1)))

    info = analyze_peripheral_spectrum(H, [L])

    print("Ergodic 2-Level:")
    print(f"  Peripheral eigenvalues: {info.eigenvalues}")
    print(f"  Phases: {info.phases}")
    print(f"  Is trivial: {info.is_trivial}")
    print(f"  Has oscillations: {info.has_oscillations}")
    print()

    return info


def test_pure_dephasing():
    """
    Pure dephasing: multiple stationary states, all with λ=0.
    No oscillatory behavior expected.
    """
    n = 3
    H = np.diag([1.0, 2.0, 3.0]).astype(complex)
    L = np.diag([0.5, 0.7, 0.3]).astype(complex)

    info = analyze_peripheral_spectrum(H, [L])

    print("Pure Dephasing (3-level):")
    print(f"  N peripheral: {info.n_peripheral}")
    print(f"  Phases: {info.phases}")
    print(f"  Phase group rank: {info.phase_group_rank}")
    print(f"  Generators: {info.generators}")
    print()

    return info


def test_coherent_oscillation():
    """
    System with coherent oscillation (off-diagonal H, no dissipation).
    Expected: oscillatory phases in peripheral spectrum.
    """
    n = 2
    omega = 1.0
    H = omega * np.array([[0, 1], [1, 0]], dtype=complex)  # σx

    info = analyze_peripheral_spectrum(H, [])

    print("Coherent Oscillation (σx):")
    print(f"  Peripheral eigenvalues: {info.eigenvalues}")
    print(f"  Phases: {info.phases}")
    print(f"  Phase group rank: {info.phase_group_rank}")
    print(f"  Generators: {info.generators}")
    print(f"  Has oscillations: {info.has_oscillations}")
    print()

    return info


def test_two_frequencies():
    """
    System with two distinct frequencies.
    """
    n = 3
    # H with two transition frequencies
    H = np.array([
        [0, 1, 0],
        [1, 1, 2],
        [0, 2, 3]
    ], dtype=complex)

    info = analyze_peripheral_spectrum(H, [])

    print("Two Frequencies:")
    print(f"  Peripheral eigenvalues: {info.eigenvalues}")
    print(f"  Phases: {info.phases}")
    print(f"  Unique phases: {info.unique_phases}")
    print(f"  Phase group rank: {info.phase_group_rank}")
    print(f"  Generators: {info.generators}")
    print()

    return info


def test_block_diagonal():
    """
    Block diagonal system with different frequencies in each block.
    """
    n = 4
    H = np.zeros((n, n), dtype=complex)
    # Block 1: frequency ω1
    omega1 = 1.0
    H[0:2, 0:2] = omega1 * np.array([[0, 1], [1, 0]])
    # Block 2: frequency ω2
    omega2 = 2.0
    H[2:4, 2:4] = omega2 * np.array([[0, 1], [1, 0]])

    info = analyze_peripheral_spectrum(H, [])

    print("Block Diagonal (two frequencies):")
    print(f"  Peripheral eigenvalues: {info.eigenvalues}")
    print(f"  Unique phases: {info.unique_phases}")
    print(f"  Phase group rank: {info.phase_group_rank}")
    print(f"  Generators: {info.generators}")
    print()

    return info


def test_damped_oscillator():
    """
    Damped oscillator: coherent oscillation + decay.
    The damping moves eigenvalues off the imaginary axis.
    """
    n = 2
    omega = 2.0
    gamma = 0.5

    H = omega * np.array([[0, 1], [1, 0]], dtype=complex)  # σx
    L = np.sqrt(gamma) * (ket(n, 0) @ dagger(ket(n, 1)))  # Decay

    info = analyze_peripheral_spectrum(H, [L])

    print("Damped Oscillator:")
    print(f"  Peripheral eigenvalues: {info.eigenvalues}")
    print(f"  Phases: {info.phases}")
    print(f"  Is trivial: {info.is_trivial}")
    print(f"  Has oscillations: {info.has_oscillations}")
    print()

    return info


if __name__ == "__main__":
    print("=" * 60)
    print("Peripheral Spectrum Analysis")
    print("=" * 60)
    print()

    test_ergodic_system()
    test_pure_dephasing()
    test_coherent_oscillation()
    test_two_frequencies()
    test_block_diagonal()
    test_damped_oscillator()

    print("=" * 60)
    print("OBSERVATIONS:")
    print("- Ergodic systems: trivial peripheral spectrum (only λ=0)")
    print("- Pure dephasing: multiple λ=0 (stationary states)")
    print("- Coherent systems: oscillatory phases from Hamiltonian")
    print("- Damping kills off-axis eigenvalues → pushes spectrum to Re<0")
    print("=" * 60)
