"""
Standard Test Cases for QMS Classification

This module provides a library of well-understood examples:
- Classical Markov chains (embedded as QMS)
- Standard quantum models (amplitude damping, dephasing)
- Block-structured systems
- Detailed balance examples

Each example includes expected values for all invariants.

Author: Paolo Vella
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass

from algebra import analyze_interaction_algebra, InteractionAlgebraInfo
from spectrum import analyze_lindbladian_spectrum, LindbladianSpectrumInfo
from dirichlet import analyze_dirichlet_form, DirichletFormInfo


@dataclass
class QMSExample:
    """A complete QMS example with expected invariants."""
    name: str
    description: str
    hamiltonian: np.ndarray
    jump_ops: List[np.ndarray]
    stationary_state: Optional[np.ndarray]  # For Dirichlet analysis
    expected_delta_Q: int
    expected_delta_cen: int
    expected_wedderburn_type: str  # e.g., "M_2", "M_2 ⊕ M_2", "ℂ^3"
    is_detailed_balance: bool
    classical_embedding: bool  # Is this a classical Markov chain?


def dagger(A: np.ndarray) -> np.ndarray:
    """Conjugate transpose."""
    return A.conj().T


# ============================================================================
# Helper Functions for Building Examples
# ============================================================================

def ket(n: int, i: int) -> np.ndarray:
    """Standard basis vector |i⟩ in ℂⁿ."""
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


def projector(n: int, i: int) -> np.ndarray:
    """Projector |i⟩⟨i|."""
    v = ket(n, i)
    return v @ dagger(v)


def transition_op(n: int, i: int, j: int, rate: float) -> np.ndarray:
    """
    Classical transition operator √rate |i⟩⟨j|.
    Represents transition j → i at rate 'rate'.
    """
    v_i = ket(n, i)
    v_j = ket(n, j)
    return np.sqrt(rate) * (v_i @ dagger(v_j))


# ============================================================================
# Classical Markov Chain Examples
# ============================================================================

def classical_two_state() -> QMSExample:
    """
    Classical two-state Markov chain: 0 ⇌ 1

    Rate matrix Q = [[-α,  α],
                     [ β, -β]]

    Embedded as: L_{01} = √α |0⟩⟨1|, L_{10} = √β |1⟩⟨0|

    Expected:
    - δ_Q = 0 (unique stationary state: π = (β, α)/(α+β))
    - δ_cen = 0 (A_int = M_2)
    """
    n = 2
    alpha, beta = 1.0, 0.5

    H = np.zeros((n, n), dtype=complex)
    L_01 = transition_op(n, 0, 1, alpha)  # 1 → 0
    L_10 = transition_op(n, 1, 0, beta)   # 0 → 1

    # Stationary state
    pi = np.array([beta, alpha]) / (alpha + beta)
    sigma = np.diag(pi.astype(complex))

    return QMSExample(
        name="Classical Two-State",
        description="Reversible two-state Markov chain 0 ⇌ 1",
        hamiltonian=H,
        jump_ops=[L_01, L_10],
        stationary_state=sigma,
        expected_delta_Q=0,
        expected_delta_cen=0,
        expected_wedderburn_type="M_2(ℂ)",
        is_detailed_balance=True,
        classical_embedding=True
    )


def classical_three_cycle() -> QMSExample:
    """
    Classical three-state cycle: 0 → 1 → 2 → 0

    Non-reversible (no detailed balance).

    Expected:
    - δ_Q = 0 (unique stationary: uniform)
    - δ_cen = 0 (A_int = M_3)
    """
    n = 3
    rate = 1.0

    H = np.zeros((n, n), dtype=complex)
    L_01 = transition_op(n, 1, 0, rate)  # 0 → 1
    L_12 = transition_op(n, 2, 1, rate)  # 1 → 2
    L_20 = transition_op(n, 0, 2, rate)  # 2 → 0

    sigma = np.eye(n, dtype=complex) / n

    return QMSExample(
        name="Classical Three-Cycle",
        description="Irreversible 3-cycle: 0 → 1 → 2 → 0",
        hamiltonian=H,
        jump_ops=[L_01, L_12, L_20],
        stationary_state=sigma,
        expected_delta_Q=0,
        expected_delta_cen=0,
        expected_wedderburn_type="M_3(ℂ)",
        is_detailed_balance=False,
        classical_embedding=True
    )


def classical_two_components() -> QMSExample:
    """
    Classical chain with two disconnected components:
    Component 1: {0, 1} with 0 ⇌ 1
    Component 2: {2, 3} with 2 ⇌ 3

    Expected:
    - δ_Q = 1 (two independent stationary states)
    - δ_cen = 1 (A_int = diag(M_2, M_2), center = ℂ ⊕ ℂ)
    """
    n = 4
    rate1, rate2 = 1.0, 0.5

    H = np.zeros((n, n), dtype=complex)

    # Component 1: 0 ⇌ 1
    L_01 = transition_op(n, 0, 1, rate1)
    L_10 = transition_op(n, 1, 0, rate1)

    # Component 2: 2 ⇌ 3
    L_23 = transition_op(n, 2, 3, rate2)
    L_32 = transition_op(n, 3, 2, rate2)

    # Block-diagonal stationary state
    sigma = np.diag([0.25, 0.25, 0.25, 0.25]).astype(complex)

    return QMSExample(
        name="Classical Two Components",
        description="Two disconnected 2-state chains: {0,1} and {2,3}",
        hamiltonian=H,
        jump_ops=[L_01, L_10, L_23, L_32],
        stationary_state=sigma,
        expected_delta_Q=1,
        expected_delta_cen=1,
        expected_wedderburn_type="M_2(ℂ) ⊕ M_2(ℂ)",
        is_detailed_balance=True,
        classical_embedding=True
    )


# ============================================================================
# Quantum Examples (Non-Classical)
# ============================================================================

def amplitude_damping_2level() -> QMSExample:
    """
    Two-level amplitude damping (spontaneous emission).

    H = ω |1⟩⟨1|
    L = √γ |0⟩⟨1|

    Expected:
    - δ_Q = 0 (unique ground state)
    - δ_cen = 0 (A_int = M_2)
    """
    n = 2
    omega, gamma = 1.0, 0.5

    H = omega * projector(n, 1)
    L = np.sqrt(gamma) * (ket(n, 0) @ dagger(ket(n, 1)))

    sigma = projector(n, 0)  # Ground state

    return QMSExample(
        name="Amplitude Damping (2-level)",
        description="Spontaneous emission: excited → ground",
        hamiltonian=H,
        jump_ops=[L],
        stationary_state=sigma,
        expected_delta_Q=0,
        expected_delta_cen=0,
        expected_wedderburn_type="M_2(ℂ)",
        is_detailed_balance=False,  # Not detailed balance without heating
        classical_embedding=False
    )


def pure_dephasing(n: int = 3) -> QMSExample:
    """
    n-level pure dephasing.

    H = diag(ω_1, ..., ω_n)
    L = diag(√γ_1, ..., √γ_n)

    All diagonal matrices commute with H and L,
    so A_int = diagonal matrices (abelian).

    Expected:
    - δ_Q = n-1 (all diagonal states are stationary)
    - δ_cen = n-1 (A_int = ℂⁿ, center = ℂⁿ)
    """
    omega = np.arange(1, n+1, dtype=float)
    gamma = np.linspace(0.5, 1.0, n)

    H = np.diag(omega.astype(complex))
    L = np.diag(np.sqrt(gamma).astype(complex))

    sigma = np.eye(n, dtype=complex) / n

    return QMSExample(
        name=f"Pure Dephasing ({n}-level)",
        description=f"Diagonal dephasing on {n}-level system",
        hamiltonian=H,
        jump_ops=[L],
        stationary_state=sigma,
        expected_delta_Q=n-1,
        expected_delta_cen=n-1,
        expected_wedderburn_type=f"ℂ^{n}",
        is_detailed_balance=True,
        classical_embedding=False
    )


def thermal_two_level() -> QMSExample:
    """
    Two-level system with thermal bath (detailed balance).

    H = ω |1⟩⟨1|
    L_down = √γ_down |0⟩⟨1|  (emission)
    L_up = √γ_up |1⟩⟨0|      (absorption)

    With γ_up/γ_down = exp(-βω) for detailed balance.

    Expected:
    - δ_Q = 0
    - δ_cen = 0
    """
    n = 2
    omega = 1.0
    beta = 1.0
    gamma_down = 0.5
    gamma_up = gamma_down * np.exp(-beta * omega)

    H = omega * projector(n, 1)
    L_down = np.sqrt(gamma_down) * (ket(n, 0) @ dagger(ket(n, 1)))
    L_up = np.sqrt(gamma_up) * (ket(n, 1) @ dagger(ket(n, 0)))

    # Thermal state
    Z = 1 + np.exp(-beta * omega)
    p0 = 1 / Z
    p1 = np.exp(-beta * omega) / Z
    sigma = np.diag([p0, p1]).astype(complex)

    return QMSExample(
        name="Thermal Two-Level",
        description="Two-level with thermal bath at β=1",
        hamiltonian=H,
        jump_ops=[L_down, L_up],
        stationary_state=sigma,
        expected_delta_Q=0,
        expected_delta_cen=0,
        expected_wedderburn_type="M_2(ℂ)",
        is_detailed_balance=True,
        classical_embedding=False
    )


def collective_dephasing(n: int = 3) -> QMSExample:
    """
    Collective dephasing with J = Σ_k |k⟩⟨k| k (total angular momentum).

    H = 0
    L = √γ J

    The interaction algebra is generated by J,
    which is a rank-1 operator.

    Expected:
    - δ_Q = n-1
    - δ_cen = n-1
    """
    J = np.diag(np.arange(n, dtype=complex))
    gamma = 0.5

    H = np.zeros((n, n), dtype=complex)
    L = np.sqrt(gamma) * J

    sigma = np.eye(n, dtype=complex) / n

    return QMSExample(
        name=f"Collective Dephasing ({n}-level)",
        description=f"Dephasing by total angular momentum on {n} levels",
        hamiltonian=H,
        jump_ops=[L],
        stationary_state=sigma,
        expected_delta_Q=n-1,
        expected_delta_cen=n-1,
        expected_wedderburn_type=f"ℂ^{n}",
        is_detailed_balance=True,
        classical_embedding=False
    )


def block_diagonal_quantum() -> QMSExample:
    """
    Block-diagonal quantum system (not classical).

    Block 1: 2×2 with amplitude damping
    Block 2: 2×2 with amplitude damping

    Quantum coherence within blocks, no coupling between blocks.

    Expected:
    - δ_Q = 1 (two stationary states)
    - δ_cen = 1 (A_int = M_2 ⊕ M_2)
    """
    n = 4

    # Block 1 Hamiltonian and jump
    H = np.zeros((n, n), dtype=complex)
    H[0:2, 0:2] = np.array([[0, 0.3], [0.3, 1]])  # With coherent coupling

    # Block 2 Hamiltonian
    H[2:4, 2:4] = np.array([[0, 0.2], [0.2, 1.5]])

    # Amplitude damping in block 1
    L1 = np.zeros((n, n), dtype=complex)
    L1[0, 1] = np.sqrt(0.5)

    # Amplitude damping in block 2
    L2 = np.zeros((n, n), dtype=complex)
    L2[2, 3] = np.sqrt(0.4)

    # Block-diagonal stationary state
    sigma = np.diag([0.5, 0, 0.5, 0]).astype(complex)

    return QMSExample(
        name="Block-Diagonal Quantum",
        description="Two 2×2 quantum blocks with amplitude damping",
        hamiltonian=H,
        jump_ops=[L1, L2],
        stationary_state=sigma,
        expected_delta_Q=1,
        expected_delta_cen=1,
        expected_wedderburn_type="M_2(ℂ) ⊕ M_2(ℂ)",
        is_detailed_balance=False,
        classical_embedding=False
    )


# ============================================================================
# Example Registry
# ============================================================================

def get_all_examples() -> List[QMSExample]:
    """Return all standard test cases."""
    return [
        # Classical embeddings
        classical_two_state(),
        classical_three_cycle(),
        classical_two_components(),
        # Quantum examples
        amplitude_damping_2level(),
        pure_dephasing(3),
        thermal_two_level(),
        collective_dephasing(3),
        block_diagonal_quantum(),
    ]


def get_classical_examples() -> List[QMSExample]:
    """Return only classical Markov chain embeddings."""
    return [ex for ex in get_all_examples() if ex.classical_embedding]


def get_detailed_balance_examples() -> List[QMSExample]:
    """Return examples satisfying detailed balance."""
    return [ex for ex in get_all_examples() if ex.is_detailed_balance]


# ============================================================================
# Testing and Verification
# ============================================================================

@dataclass
class ExampleAnalysis:
    """Complete analysis of an example."""
    example: QMSExample
    algebra_info: InteractionAlgebraInfo
    spectrum_info: LindbladianSpectrumInfo
    dirichlet_info: Optional[DirichletFormInfo]
    delta_Q_matches: bool
    delta_cen_matches: bool


def analyze_example(example: QMSExample, verbose: bool = True) -> ExampleAnalysis:
    """
    Run complete analysis on an example and compare with expected values.
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"Analyzing: {example.name}")
        print(f"{'='*60}")
        print(f"Description: {example.description}")

    # Interaction algebra
    alg_info = analyze_interaction_algebra(
        example.hamiltonian, example.jump_ops
    )

    # Spectrum
    spec_info = analyze_lindbladian_spectrum(
        example.hamiltonian, example.jump_ops
    )

    # Dirichlet (only if we have a stationary state)
    dir_info = None
    if example.stationary_state is not None:
        try:
            dir_info = analyze_dirichlet_form(
                example.hamiltonian, example.jump_ops, example.stationary_state
            )
        except Exception as e:
            if verbose:
                print(f"  Warning: Dirichlet analysis failed: {e}")

    # Check matches
    delta_Q_match = (spec_info.quantum_deficiency == example.expected_delta_Q)
    delta_cen_match = (alg_info.central_deficiency == example.expected_delta_cen)

    if verbose:
        print(f"\nResults:")
        print(f"  dim(A_int) = {alg_info.dim_algebra}")
        print(f"  dim(Z(A_int)) = {alg_info.dim_center}")
        print(f"  δ_cen = {alg_info.central_deficiency} (expected: {example.expected_delta_cen}) {'✓' if delta_cen_match else '✗'}")
        print(f"  δ_Q = {spec_info.quantum_deficiency} (expected: {example.expected_delta_Q}) {'✓' if delta_Q_match else '✗'}")
        print(f"  Expected type: {example.expected_wedderburn_type}")

        if dir_info:
            print(f"  Detailed balance: {dir_info.is_detailed_balance} (expected: {example.is_detailed_balance})")
            print(f"  Dirichlet rank: {dir_info.dirichlet_rank}")

    return ExampleAnalysis(
        example=example,
        algebra_info=alg_info,
        spectrum_info=spec_info,
        dirichlet_info=dir_info,
        delta_Q_matches=delta_Q_match,
        delta_cen_matches=delta_cen_match
    )


def run_all_tests(verbose: bool = True) -> List[ExampleAnalysis]:
    """Run analysis on all examples and report results."""
    examples = get_all_examples()
    results = []

    for ex in examples:
        result = analyze_example(ex, verbose)
        results.append(result)

    # Summary
    if verbose:
        print(f"\n{'='*60}")
        print("SUMMARY")
        print(f"{'='*60}")

        n_total = len(results)
        n_delta_Q_ok = sum(1 for r in results if r.delta_Q_matches)
        n_delta_cen_ok = sum(1 for r in results if r.delta_cen_matches)

        print(f"δ_Q correct: {n_delta_Q_ok}/{n_total}")
        print(f"δ_cen correct: {n_delta_cen_ok}/{n_total}")

        if n_delta_Q_ok < n_total or n_delta_cen_ok < n_total:
            print("\nFailed cases:")
            for r in results:
                if not r.delta_Q_matches or not r.delta_cen_matches:
                    print(f"  - {r.example.name}")
                    if not r.delta_Q_matches:
                        print(f"      δ_Q: got {r.spectrum_info.quantum_deficiency}, expected {r.example.expected_delta_Q}")
                    if not r.delta_cen_matches:
                        print(f"      δ_cen: got {r.algebra_info.central_deficiency}, expected {r.example.expected_delta_cen}")

    return results


if __name__ == "__main__":
    run_all_tests(verbose=True)
