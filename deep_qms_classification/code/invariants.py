"""
Complete Invariant Synthesis for QMS Classification

This module combines all computed invariants:
- δ_cen: Central deficiency (dim Z(A_int) - 1)
- δ_struct: Structural deficiency (dim C(S*(G)) - 1)
- δ_Q: Quantum deficiency (dim ker(L) - 1)
- Phase group structure
- Candidate rank terms

Goal: Find a complete set of classification invariants.

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass

from algebra import analyze_interaction_algebra, InteractionAlgebraInfo
from spectrum import (
    analyze_lindbladian_spectrum, LindbladianSpectrumInfo,
    construct_lindbladian
)
from structural import analyze_structure, StructuralInfo
from peripheral import analyze_peripheral_spectrum, PeripheralSpectrumInfo
from dirichlet import analyze_dirichlet_form, DirichletFormInfo


def dagger(A: np.ndarray) -> np.ndarray:
    return A.conj().T


# ============================================================================
# Candidate Rank Terms
# ============================================================================

def dissipator_image_rank(jump_ops: List[np.ndarray], tol: float = 1e-10) -> int:
    """
    Rank of the image of the dissipator D = Σ_k L_k (·) L_k†.

    This measures the "dimension" of the dissipative dynamics.
    """
    if not jump_ops:
        return 0

    n = jump_ops[0].shape[0]

    # Build the dissipator as a superoperator
    # D(X) = Σ_k L_k X L_k†
    # vec(D(X)) = Σ_k (L_k^* ⊗ L_k) vec(X)
    D_super = np.zeros((n*n, n*n), dtype=complex)
    for L in jump_ops:
        D_super += np.kron(L.conj(), L)

    # Rank of D_super
    singular_values = linalg.svdvals(D_super)
    return int(np.sum(singular_values > tol))


def lindbladian_rank(H: np.ndarray, jump_ops: List[np.ndarray],
                     tol: float = 1e-10) -> int:
    """
    Rank of the Lindbladian superoperator.
    """
    L_super = construct_lindbladian(H, jump_ops)
    singular_values = linalg.svdvals(L_super)
    return int(np.sum(singular_values > tol))


def constraint_codimension(H: np.ndarray, jump_ops: List[np.ndarray],
                           tol: float = 1e-10) -> int:
    """
    Codimension of the constraint space.

    The constraint space is the image of the Lindbladian.
    Its codimension is the dimension of the stationary space.
    """
    L_super = construct_lindbladian(H, jump_ops)
    n_sq = L_super.shape[0]
    rank = lindbladian_rank(H, jump_ops, tol)
    return n_sq - rank


def jump_span_dimension(jump_ops: List[np.ndarray], tol: float = 1e-10) -> int:
    """
    Dimension of span{L_k, L_k†} as a vector space.
    """
    if not jump_ops:
        return 0

    all_ops = []
    for L in jump_ops:
        all_ops.append(L)
        all_ops.append(dagger(L))

    # Gram-Schmidt to find dimension
    n = all_ops[0].shape[0]
    basis = []
    for M in all_ops:
        v = M.copy().astype(complex)
        for b in basis:
            coeff = np.trace(dagger(b) @ v)
            v = v - coeff * b
        norm = np.sqrt(np.abs(np.trace(dagger(v) @ v)))
        if norm > tol:
            basis.append(v / norm)

    return len(basis)


def generator_span_dimension(H: np.ndarray, jump_ops: List[np.ndarray],
                             tol: float = 1e-10) -> int:
    """
    Dimension of span{I, H, L_k, L_k†}.
    """
    n = H.shape[0]
    generators = [np.eye(n, dtype=complex), H]
    for L in jump_ops:
        generators.append(L)
        generators.append(dagger(L))

    # Gram-Schmidt
    basis = []
    for M in generators:
        v = M.copy().astype(complex)
        for b in basis:
            coeff = np.trace(dagger(b) @ v)
            v = v - coeff * b
        norm = np.sqrt(np.abs(np.trace(dagger(v) @ v)))
        if norm > tol:
            basis.append(v / norm)

    return len(basis)


# ============================================================================
# Complete Invariant Structure
# ============================================================================

@dataclass
class CompleteInvariants:
    """All computed invariants for a QMS."""
    # System size
    n: int

    # Main deficiencies
    delta_cen: int      # dim Z(A_int) - 1
    delta_struct: int   # dim C(S*(G)) - 1
    delta_Q: int        # dim ker(L) - 1

    # Algebra dimensions
    dim_algebra: int    # dim A_int
    dim_center: int     # dim Z(A_int)
    dim_commutant: int  # dim C(S*(G))

    # Candidate rank terms
    r_dissipator: int       # rank of dissipator
    r_lindbladian: int      # rank of Lindbladian
    r_constraint_codim: int # codim of constraint space = dim ker(L)
    r_jump_span: int        # dim span{L_k, L_k†}
    r_generator_span: int   # dim span{I, H, L_k, L_k†}

    # Peripheral spectrum
    n_peripheral: int       # number of peripheral eigenvalues
    phase_rank: int         # rank of phase group
    has_oscillations: bool

    # Spectral data
    spectral_gap: float

    # Computed combinations
    @property
    def delta_gap(self) -> int:
        """Gap between central and structural deficiency."""
        return self.delta_cen - self.delta_struct

    @property
    def classical_formula_attempt(self) -> int:
        """
        Attempt at classical formula: δ = n - ℓ - rank(S)

        For quantum: try δ_cen + (n² - dim_algebra)?
        """
        return self.delta_cen + (self.n * self.n - self.dim_algebra)


def compute_all_invariants(H: np.ndarray,
                           jump_ops: List[np.ndarray],
                           sigma: Optional[np.ndarray] = None,
                           tol: float = 1e-10) -> CompleteInvariants:
    """
    Compute all invariants for a given QMS.
    """
    n = H.shape[0]

    # Algebra analysis
    alg_info = analyze_interaction_algebra(H, jump_ops, tol)

    # Structural analysis
    struct_info = analyze_structure(H, jump_ops, tol)

    # Spectral analysis
    spec_info = analyze_lindbladian_spectrum(H, jump_ops, tol)

    # Peripheral analysis
    periph_info = analyze_peripheral_spectrum(H, jump_ops, tol)

    # Rank terms
    r_diss = dissipator_image_rank(jump_ops, tol)
    r_lind = lindbladian_rank(H, jump_ops, tol)
    r_codim = constraint_codimension(H, jump_ops, tol)
    r_jump = jump_span_dimension(jump_ops, tol)
    r_gen = generator_span_dimension(H, jump_ops, tol)

    return CompleteInvariants(
        n=n,
        delta_cen=alg_info.central_deficiency,
        delta_struct=struct_info.structural_deficiency,
        delta_Q=spec_info.quantum_deficiency,
        dim_algebra=alg_info.dim_algebra,
        dim_center=alg_info.dim_center,
        dim_commutant=struct_info.commutant_dim,
        r_dissipator=r_diss,
        r_lindbladian=r_lind,
        r_constraint_codim=r_codim,
        r_jump_span=r_jump,
        r_generator_span=r_gen,
        n_peripheral=periph_info.n_peripheral,
        phase_rank=periph_info.phase_group_rank,
        has_oscillations=periph_info.has_oscillations,
        spectral_gap=spec_info.spectral_gap
    )


def print_invariants(inv: CompleteInvariants, name: str = ""):
    """Pretty print all invariants."""
    print(f"\n{'='*60}")
    print(f"INVARIANTS: {name}" if name else "INVARIANTS")
    print("=" * 60)

    print(f"\nSystem: n = {inv.n}")

    print(f"\n--- Deficiencies ---")
    print(f"  δ_cen    = {inv.delta_cen}")
    print(f"  δ_struct = {inv.delta_struct}")
    print(f"  δ_Q      = {inv.delta_Q}")
    print(f"  gap      = δ_cen - δ_struct = {inv.delta_gap}")

    print(f"\n--- Algebra Dimensions ---")
    print(f"  dim(A_int)     = {inv.dim_algebra}")
    print(f"  dim(Z(A_int))  = {inv.dim_center}")
    print(f"  dim(C(S*(G)))  = {inv.dim_commutant}")

    print(f"\n--- Candidate Rank Terms ---")
    print(f"  rank(D)             = {inv.r_dissipator}")
    print(f"  rank(L)             = {inv.r_lindbladian}")
    print(f"  codim(Im L)         = {inv.r_constraint_codim}")
    print(f"  dim span{{L_k, L_k*}} = {inv.r_jump_span}")
    print(f"  dim span{{generators}} = {inv.r_generator_span}")

    print(f"\n--- Peripheral Spectrum ---")
    print(f"  # peripheral   = {inv.n_peripheral}")
    print(f"  phase rank     = {inv.phase_rank}")
    print(f"  has oscillations = {inv.has_oscillations}")
    print(f"  spectral gap   = {inv.spectral_gap:.4f}")

    print(f"\n--- Derived ---")
    print(f"  classical attempt = {inv.classical_formula_attempt}")


# ============================================================================
# Relationship Analysis
# ============================================================================

def check_invariant_relationships(examples: List[Tuple[str, np.ndarray, List[np.ndarray]]]):
    """
    Analyze relationships between invariants across examples.
    """
    print("\n" + "=" * 80)
    print("INVARIANT RELATIONSHIPS")
    print("=" * 80)

    all_inv = []
    for name, H, jumps in examples:
        inv = compute_all_invariants(H, jumps)
        all_inv.append((name, inv))

    # Check: Is δ_Q always determined by other invariants?
    print("\n1. Relationship: δ_Q vs other invariants")
    print("-" * 40)
    for name, inv in all_inv:
        # Try: δ_Q = δ_cen?
        eq_cen = inv.delta_Q == inv.delta_cen
        # Try: δ_Q = r_constraint_codim - 1?
        eq_codim = inv.delta_Q == inv.r_constraint_codim - 1
        print(f"  {name}: δ_Q={inv.delta_Q}, δ_cen={inv.delta_cen}, codim-1={inv.r_constraint_codim-1}")
        print(f"    δ_Q == δ_cen: {eq_cen}, δ_Q == codim-1: {eq_codim}")

    # Check: Is dim(A_int) + dim(Z) predictable?
    print("\n2. Relationship: dim(A_int) and dim(Z)")
    print("-" * 40)
    for name, inv in all_inv:
        ratio = inv.dim_center / inv.dim_algebra if inv.dim_algebra > 0 else 0
        print(f"  {name}: dim(A)={inv.dim_algebra}, dim(Z)={inv.dim_center}, ratio={ratio:.2f}")

    # Check: Rank term patterns
    print("\n3. Rank term patterns")
    print("-" * 40)
    for name, inv in all_inv:
        print(f"  {name}:")
        print(f"    r_dissipator={inv.r_dissipator}, r_lindbladian={inv.r_lindbladian}")
        print(f"    n²={inv.n**2}, n²-δ_Q-1={inv.n**2 - inv.delta_Q - 1}")


# ============================================================================
# Test Suite
# ============================================================================

def ket(n: int, i: int) -> np.ndarray:
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


def standard_examples() -> List[Tuple[str, np.ndarray, List[np.ndarray]]]:
    """Standard test cases with (name, H, jump_ops)."""
    examples = []

    # 1. Amplitude damping
    n = 2
    H = np.array([[0, 0], [0, 1]], dtype=complex)
    L = np.sqrt(0.5) * (ket(n, 0) @ dagger(ket(n, 1)))
    examples.append(("2L Amplitude Damping", H, [L]))

    # 2. Pure dephasing
    H = np.diag([1.0, 2.0, 3.0]).astype(complex)
    L = np.diag([0.5, 0.7, 0.3]).astype(complex)
    examples.append(("3L Pure Dephasing", H, [L]))

    # 3. Two blocks
    H = np.zeros((4, 4), dtype=complex)
    H[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])
    L1 = np.zeros((4, 4), dtype=complex)
    L1[0, 1] = 1.0
    L2 = np.zeros((4, 4), dtype=complex)
    L2[2, 3] = 1.0
    examples.append(("4L Two Blocks", H, [L1, L2]))

    # 4. Coherent only
    H = np.array([[0, 1], [1, 0]], dtype=complex)
    examples.append(("2L Coherent σx", H, []))

    # 5. Three-cycle
    n = 3
    L1 = np.sqrt(0.5) * (ket(n, 1) @ dagger(ket(n, 0)))
    L2 = np.sqrt(0.5) * (ket(n, 2) @ dagger(ket(n, 1)))
    L3 = np.sqrt(0.5) * (ket(n, 0) @ dagger(ket(n, 2)))
    examples.append(("3L Cycle", np.zeros((3, 3), dtype=complex), [L1, L2, L3]))

    return examples


if __name__ == "__main__":
    examples = standard_examples()

    for name, H, jumps in examples:
        inv = compute_all_invariants(H, jumps)
        print_invariants(inv, name)

    check_invariant_relationships(examples)
