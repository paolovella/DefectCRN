"""
QMS Classification Computation Package

This package provides tools for classifying quantum Markov semigroups.

Modules:
- algebra: Interaction algebra computation (A_int, Z(A_int), δ_cen)
- spectrum: Lindbladian spectrum (eigenvalues, δ_Q, spectral gap)
- dirichlet: Dirichlet form and detailed balance
- examples: Standard test cases library

Author: Paolo Vella
"""

from .algebra import (
    compute_interaction_algebra,
    compute_center,
    central_deficiency,
    analyze_interaction_algebra,
    InteractionAlgebraInfo,
)

from .spectrum import (
    construct_lindbladian,
    compute_spectrum,
    peripheral_spectrum,
    quantum_deficiency,
    analyze_lindbladian_spectrum,
    LindbladianSpectrumInfo,
)

from .dirichlet import (
    gns_inner_product,
    check_detailed_balance,
    compute_dirichlet_form,
    dirichlet_rank,
    analyze_dirichlet_form,
    DirichletFormInfo,
)

from .examples import (
    QMSExample,
    get_all_examples,
    analyze_example,
    run_all_tests,
)

from .structural import (
    extract_graph_from_lindbladian,
    compute_test_set,
    compute_structural_commutant,
    structural_deficiency,
    analyze_structure,
    StructuralInfo,
)

from .comparison import (
    compare_example,
    run_comparison,
    ComparisonResult,
)

from .peripheral import (
    analyze_peripheral_spectrum,
    PeripheralSpectrumInfo,
)

from .invariants import (
    compute_all_invariants,
    CompleteInvariants,
)

from .classical import (
    embed_markov_chain,
    analyze_classical_chain,
    verify_classical_reduction,
)

from .separation import (
    find_separations,
    detect_wedderburn_type,
    SeparationExample,
)
