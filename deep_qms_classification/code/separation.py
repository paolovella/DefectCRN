"""
Separation Examples for QMS Classification

Goal: Find examples with the same δ_Q but different Type(L).

This would show that δ_Q alone is not sufficient for classification,
and the Wedderburn type provides additional information.

Author: Paolo Vella
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Dict
from dataclasses import dataclass

from algebra import analyze_interaction_algebra, InteractionAlgebraInfo
from spectrum import analyze_lindbladian_spectrum
from invariants import compute_all_invariants, CompleteInvariants


def dagger(A: np.ndarray) -> np.ndarray:
    return A.conj().T


def ket(n: int, i: int) -> np.ndarray:
    v = np.zeros((n, 1), dtype=complex)
    v[i, 0] = 1.0
    return v


# ============================================================================
# Wedderburn Type Detection
# ============================================================================

def detect_wedderburn_type(dim_algebra: int, dim_center: int, n: int) -> str:
    """
    Infer the Wedderburn type from algebra dimensions.

    For A ≅ ⊕_α M_{d_α} ⊗ I_{m_α}:
    - dim A = Σ_α d_α² m_α²
    - dim Z(A) = number of blocks = Σ_α 1

    Common cases:
    - M_n(ℂ): dim = n², center = 1
    - ℂ^n (diagonal): dim = n, center = n
    - M_2 ⊕ M_2: dim = 8, center = 2 (for n=4)
    """
    if dim_center == 1:
        # Single block
        d = int(np.sqrt(dim_algebra))
        if d * d == dim_algebra:
            return f"M_{d}(ℂ)"
        else:
            return f"Unknown (dim={dim_algebra}, Z=1)"

    if dim_algebra == dim_center:
        # Abelian algebra (diagonal)
        return f"ℂ^{dim_center}"

    # Try to decompose
    # For n blocks of same size: dim = k * d² * m², center = k
    # Most common: k blocks of M_d
    k = dim_center  # number of blocks

    # Assume all blocks same size for simplicity
    dim_per_block = dim_algebra // k
    d = int(np.sqrt(dim_per_block))
    if d * d == dim_per_block:
        if k == dim_center:
            return f"{k} × M_{d}(ℂ)"

    return f"Mixed (dim={dim_algebra}, Z={dim_center})"


@dataclass
class SeparationExample:
    """A pair of examples for separation analysis."""
    name1: str
    name2: str
    H1: np.ndarray
    jumps1: List[np.ndarray]
    H2: np.ndarray
    jumps2: List[np.ndarray]
    inv1: CompleteInvariants
    inv2: CompleteInvariants
    same_delta_Q: bool
    different_type: bool
    is_separation: bool  # same δ_Q, different type


def compare_examples(name1: str, H1: np.ndarray, jumps1: List[np.ndarray],
                     name2: str, H2: np.ndarray, jumps2: List[np.ndarray]) -> SeparationExample:
    """
    Compare two examples to check if they form a separation pair.
    """
    inv1 = compute_all_invariants(H1, jumps1)
    inv2 = compute_all_invariants(H2, jumps2)

    type1 = detect_wedderburn_type(inv1.dim_algebra, inv1.dim_center, inv1.n)
    type2 = detect_wedderburn_type(inv2.dim_algebra, inv2.dim_center, inv2.n)

    same_delta = inv1.delta_Q == inv2.delta_Q
    diff_type = type1 != type2

    return SeparationExample(
        name1=name1,
        name2=name2,
        H1=H1,
        jumps1=jumps1,
        H2=H2,
        jumps2=jumps2,
        inv1=inv1,
        inv2=inv2,
        same_delta_Q=same_delta,
        different_type=diff_type,
        is_separation=same_delta and diff_type
    )


# ============================================================================
# Candidate Separation Pairs
# ============================================================================

def candidate_pairs() -> List[SeparationExample]:
    """
    Generate candidate separation pairs.

    Strategy: Find examples with same δ_Q but different algebra structure.
    """
    pairs = []

    # === Pair 1: Both δ_Q = 0, but different algebra dimension ===

    # Example A: 2-level amplitude damping (A_int = M_2)
    H1 = np.array([[0, 0], [0, 1]], dtype=complex)
    L1 = np.sqrt(0.5) * (ket(2, 0) @ dagger(ket(2, 1)))

    # Example B: 3-level ergodic (A_int = M_3)
    H2 = np.array([[0, 0.5, 0], [0.5, 1, 0.5], [0, 0.5, 2]], dtype=complex)
    L2a = np.sqrt(0.3) * (ket(3, 0) @ dagger(ket(3, 1)))
    L2b = np.sqrt(0.3) * (ket(3, 1) @ dagger(ket(3, 2)))

    pairs.append(compare_examples(
        "2L Amplitude Damping", H1, [L1],
        "3L Cascade", H2, [L2a, L2b]
    ))

    # === Pair 2: Both δ_Q = 1, different structure ===

    # Example A: 2-level pure dephasing (A_int = ℂ², abelian)
    H3 = np.diag([1.0, 2.0]).astype(complex)
    L3 = np.diag([0.5, -0.5]).astype(complex)

    # Example B: 4-level two blocks (A_int = M_2 ⊕ M_2)
    H4 = np.zeros((4, 4), dtype=complex)
    H4[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H4[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])
    L4a = np.zeros((4, 4), dtype=complex)
    L4a[0, 1] = 1.0
    L4b = np.zeros((4, 4), dtype=complex)
    L4b[2, 3] = 1.0

    pairs.append(compare_examples(
        "2L Dephasing", H3, [L3],
        "4L Two Blocks", H4, [L4a, L4b]
    ))

    # === Pair 3: Both δ_Q = 2, different structure ===

    # Example A: 3-level pure dephasing (A_int = ℂ³)
    H5 = np.diag([1.0, 2.0, 3.0]).astype(complex)
    L5 = np.diag([0.5, 0.7, 0.3]).astype(complex)

    # Example B: 6-level three blocks (A_int = M_2 ⊕ M_2 ⊕ M_2)
    H6 = np.zeros((6, 6), dtype=complex)
    H6[0:2, 0:2] = np.array([[1, 0.5], [0.5, 2]])
    H6[2:4, 2:4] = np.array([[3, 0.3], [0.3, 4]])
    H6[4:6, 4:6] = np.array([[5, 0.2], [0.2, 6]])
    L6a = np.zeros((6, 6), dtype=complex)
    L6a[0, 1] = 1.0
    L6b = np.zeros((6, 6), dtype=complex)
    L6b[2, 3] = 1.0
    L6c = np.zeros((6, 6), dtype=complex)
    L6c[4, 5] = 1.0

    pairs.append(compare_examples(
        "3L Dephasing", H5, [L5],
        "6L Three Blocks", H6, [L6a, L6b, L6c]
    ))

    # === Pair 4: Same dimension, same δ_Q, but different type? ===

    # Example A: 4-level dephasing (A_int = ℂ⁴, dim=4)
    H7 = np.diag([1.0, 2.0, 3.0, 4.0]).astype(complex)
    L7 = np.diag([0.5, 0.7, 0.3, 0.9]).astype(complex)

    # Example B: 4-level with M_2 ⊕ ℂ² structure?
    # Need: 2 blocks, one M_2 (dim 4) and one ℂ² (dim 2)
    # Total dim = 6, center = 2? Hmm, this doesn't give δ=3
    # Actually for δ=3, we need center dim = 4

    # Try: 4 blocks of ℂ (singleton blocks with jumps)
    H8 = np.zeros((4, 4), dtype=complex)
    L8a = np.zeros((4, 4), dtype=complex)
    L8a[0, 0] = 1.0  # Dephasing on state 0
    L8b = np.zeros((4, 4), dtype=complex)
    L8b[1, 1] = 1.0  # Dephasing on state 1
    L8c = np.zeros((4, 4), dtype=complex)
    L8c[2, 2] = 1.0
    L8d = np.zeros((4, 4), dtype=complex)
    L8d[3, 3] = 1.0

    pairs.append(compare_examples(
        "4L Diagonal Dephasing", H7, [L7],
        "4L Independent Dephasing", H8, [L8a, L8b, L8c, L8d]
    ))

    return pairs


def find_separations(verbose: bool = True) -> List[SeparationExample]:
    """
    Search for separation examples.
    """
    pairs = candidate_pairs()

    if verbose:
        print("=" * 80)
        print("SEPARATION EXAMPLE SEARCH")
        print("=" * 80)
        print()

        for i, pair in enumerate(pairs):
            print(f"\n--- Pair {i+1} ---")
            print(f"Example A: {pair.name1}")
            print(f"  n = {pair.inv1.n}")
            print(f"  dim(A_int) = {pair.inv1.dim_algebra}")
            print(f"  dim(Z) = {pair.inv1.dim_center}")
            print(f"  δ_Q = {pair.inv1.delta_Q}")
            type1 = detect_wedderburn_type(pair.inv1.dim_algebra,
                                           pair.inv1.dim_center, pair.inv1.n)
            print(f"  Type: {type1}")

            print(f"\nExample B: {pair.name2}")
            print(f"  n = {pair.inv2.n}")
            print(f"  dim(A_int) = {pair.inv2.dim_algebra}")
            print(f"  dim(Z) = {pair.inv2.dim_center}")
            print(f"  δ_Q = {pair.inv2.delta_Q}")
            type2 = detect_wedderburn_type(pair.inv2.dim_algebra,
                                           pair.inv2.dim_center, pair.inv2.n)
            print(f"  Type: {type2}")

            print(f"\nComparison:")
            print(f"  Same δ_Q: {pair.same_delta_Q}")
            print(f"  Different Type: {pair.different_type}")
            if pair.is_separation:
                print("  *** SEPARATION EXAMPLE FOUND! ***")

    # Summary
    separations = [p for p in pairs if p.is_separation]

    if verbose:
        print("\n" + "=" * 80)
        print("SUMMARY")
        print("=" * 80)
        print(f"Total pairs checked: {len(pairs)}")
        print(f"Separation examples found: {len(separations)}")

        if separations:
            print("\nSeparation pairs:")
            for sep in separations:
                print(f"  - {sep.name1} vs {sep.name2}")
                print(f"    Both have δ_Q = {sep.inv1.delta_Q}")
                type1 = detect_wedderburn_type(sep.inv1.dim_algebra,
                                               sep.inv1.dim_center, sep.inv1.n)
                type2 = detect_wedderburn_type(sep.inv2.dim_algebra,
                                               sep.inv2.dim_center, sep.inv2.n)
                print(f"    Types: {type1} vs {type2}")
        else:
            print("\nNo separation examples found in candidate set.")
            print("This suggests δ_Q may be closely tied to the Wedderburn type.")

    return separations


# ============================================================================
# Theoretical Analysis
# ============================================================================

def analyze_type_vs_delta():
    """
    Analyze the relationship between Wedderburn type and δ_Q.
    """
    print("\n" + "=" * 80)
    print("ANALYSIS: Wedderburn Type vs δ_Q")
    print("=" * 80)

    print("""
For A_int ≅ ⊕_{α=1}^k M_{d_α} ⊗ I_{m_α}:

1. dim Z(A_int) = k (number of blocks)
2. δ_cen = k - 1
3. δ_Q = δ_cen = k - 1 (by our main theorem)

So δ_Q determines k (number of blocks) but NOT the individual block sizes!

Examples with same δ_Q = 1 (i.e., k = 2 blocks):
- ℂ² (dim = 2): two 1×1 blocks
- M_2 ⊕ M_2 (dim = 8): two 2×2 blocks
- M_3 ⊕ M_3 (dim = 18): two 3×3 blocks

These are NOT equivalent as QMS (different dynamics) but have same δ_Q.

CONCLUSION: δ_Q alone does not classify QMS.
We need the full Wedderburn type {(d_α, m_α)}.
""")


if __name__ == "__main__":
    separations = find_separations(verbose=True)
    analyze_type_vs_delta()
