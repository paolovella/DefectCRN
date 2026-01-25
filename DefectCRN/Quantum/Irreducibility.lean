/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Algebra
import DefectCRN.Quantum.StationaryState
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
# Irreducibility (Primitivity) of Quantum Markov Semigroups
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- A Lindbladian is primitive if its commutant is trivial -/
def IsPrimitive (L : Lindbladian n) : Prop :=
  hasTrivialCommutant L

/-- A Lindbladian is irreducible if no non-trivial projection commutes with it -/
def IsIrreducible (L : Lindbladian n) : Prop :=
  ∀ P : Matrix (Fin n) (Fin n) ℂ,
    P * P = P → P.IsHermitian → IsInCommutant L P → (P = 0 ∨ P = 1)

/-- Primitive implies irreducible -/
theorem primitive_implies_irreducible (L : Lindbladian n) (h : IsPrimitive L) :
    IsIrreducible L := by
  intro P hProj hHerm hComm
  -- P is in the commutant, so P = c • I for some c
  obtain ⟨c, hc⟩ := h P hComm
  -- P² = P means (c • I)² = c • I, so c² = c
  have hc2 : c * c = c := by
    have hPP : (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) =
               c • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [← hc]; exact hProj
    simp only [smul_mul_smul_comm, mul_one, one_mul] at hPP
    -- (c * c) • 1 = c • 1, extract (0,0) entry
    have h00 : ((c * c) • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0 =
               (c • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0 := by rw [hPP]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact h00
  -- c² = c means c = 0 or c = 1
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by ring_nf; rw [sq, hc2]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · left; exact h0
    · right; exact sub_eq_zero.mp h1
  rcases hc01 with rfl | rfl
  · left; simp [hc]
  · right; simp [hc]

/-- Key lemma: Hermitian elements of the commutant of an irreducible Lindbladian are scalar.

    Proof sketch:
    1. H has spectral decomposition H = Σᵢ λᵢ Pᵢ where Pᵢ are orthogonal projections
    2. Each Pᵢ can be written as a polynomial in H (via Lagrange interpolation):
       Pⱼ = ∏_{k≠j} (H - μₖI) / (μⱼ - μₖ) for distinct eigenvalues μ₁, ..., μₘ
    3. Since H is in commutant, so is each Pᵢ:
       - By `commutant_closed_pow`, H^k is in commutant for all k
       - By linearity of commutant (it's a submodule), polynomials in H are in commutant
    4. Each Pᵢ is Hermitian and satisfies Pᵢ² = Pᵢ, so it's an orthogonal projection
    5. By irreducibility (definition), each Pᵢ ∈ {0, I}
    6. The Pᵢ are mutually orthogonal (PᵢPⱼ = 0 for i≠j) and sum to I
    7. These constraints imply exactly one Pᵢ = I (the others are 0)
    8. Therefore H = Σᵢ λᵢPᵢ = λₖ·I for the unique k where Pₖ = I

    The formal proof requires Lagrange interpolation machinery which is complex.
    The key building block (`commutant_closed_pow`) is proven above. -/
theorem hermitian_commutant_is_scalar (L : Lindbladian n) (h : IsIrreducible L)
    (H : Matrix (Fin n) (Fin n) ℂ) (hHerm : H.IsHermitian)
    (hComm : H ∈ commutantSubmodule L) : ∃ c : ℂ, H = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- The proof requires spectral theory and Lagrange interpolation
  -- Key steps proven in supporting infrastructure:
  -- - commutant_closed_pow: powers of H are in commutant
  -- - commutant_closed_mul: products of commutant elements are in commutant
  -- These imply any polynomial in H is in the commutant.
  -- Spectral projections are polynomials in H (Lagrange), hence in commutant.
  -- By irreducibility + orthogonality, H has only one eigenvalue, so H = λI.
  sorry

/-- Irreducible implies primitive.

    Proof:
    - Take any X in commutant
    - Decompose X = H + iK where H, K are Hermitian (both in commutant)
    - By hermitian_commutant_is_scalar, H = c·I and K = d·I for some c, d ∈ ℂ
    - Therefore X = (c + i·d)·I is scalar -/
theorem irreducible_implies_primitive (L : Lindbladian n) (h : IsIrreducible L) :
    IsPrimitive L := by
  unfold IsPrimitive hasTrivialCommutant
  intro X hX
  -- X = H + i·K where H, K are Hermitian and in commutant
  have hXdecomp := hermitian_decomposition X
  have hHerm := hermitianPart_isHermitian X
  have hSkew := skewHermitianPart_isHermitian X
  -- H and K are in commutant
  have hHComm := hermitianPart_mem_commutant L X hX
  have hKComm := skewHermitianPart_mem_commutant L X hX
  -- By the key lemma, H and K are scalar
  obtain ⟨cH, hcH⟩ := hermitian_commutant_is_scalar L h (hermitianPart X) hHerm hHComm
  obtain ⟨cK, hcK⟩ := hermitian_commutant_is_scalar L h (skewHermitianPart X) hSkew hKComm
  -- X = H + i·K = cH·I + i·(cK·I) = (cH + i·cK)·I
  use cH + Complex.I * cK
  rw [hXdecomp, hcH, hcK]
  simp only [smul_smul]
  rw [← add_smul, add_comm]

/-- Primitive and irreducible are equivalent -/
theorem primitive_iff_irreducible (L : Lindbladian n) :
    IsPrimitive L ↔ IsIrreducible L :=
  ⟨primitive_implies_irreducible L, irreducible_implies_primitive L⟩

/-- For primitive Lindbladians, any stationary density matrix is faithful.

    Proof sketch:
    1. For a PSD matrix ρ, the support projection P_supp is the projection
       onto the range of ρ (the orthogonal complement of ker(ρ)).
    2. ρ is faithful ⟺ P_supp = I ⟺ ker(ρ) = {0} ⟺ ρ is positive definite.
    3. Key insight: If L(ρ) = 0 and ρ is PSD, then P_supp commutes with all
       generators of L. This follows from the structure of the Lindblad equation:
       - For the Hamiltonian part: [H, ρ] has range ⊆ range(ρ)
       - For dissipators: L_k ρ L_k† has range ⊆ range(ρ) if L(ρ) = 0
    4. Since P_supp is a non-trivial projection in the commutant (or commutant-like),
       by primitivity (≡ irreducibility) we have P_supp ∈ {0, I}.
    5. Since Tr(ρ) = 1 > 0, we have ρ ≠ 0, so P_supp ≠ 0, thus P_supp = I.
    6. Therefore ρ is faithful.

    Reference: Frigerio (1978), Evans-Høegh-Krohn spectral analysis. -/
theorem primitive_stationary_is_faithful (L : Lindbladian n) (h : IsPrimitive L)
    (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ) :
    IsFaithful ρ := by
  -- The support projection P of ρ is in the commutant (by analysis of L(ρ)=0)
  -- By primitivity, P = 0 or P = I. Since Tr(ρ) = 1, we have P = I.
  sorry

/-- In a 1-dimensional subspace, elements with equal nonzero trace are equal. -/
theorem eq_of_mem_finrank_one_trace_eq {S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)}
    (hDim : Module.finrank ℂ S = 1) (x y : Matrix (Fin n) (Fin n) ℂ)
    (hx : x ∈ S) (hy : y ∈ S) (hxHerm : x.IsHermitian) (hyHerm : y.IsHermitian)
    (hxTr : x.trace = 1) (hyTr : y.trace = 1) : x = y := by
  -- In a 1-D space over ℂ, any element is a scalar multiple of a generator
  rw [finrank_eq_one_iff'] at hDim
  obtain ⟨⟨v, hv_mem⟩, hv0, hv⟩ := hDim
  -- Get scalar coefficients for x and y
  obtain ⟨cx, hcx⟩ := hv ⟨x, hx⟩
  obtain ⟨cy, hcy⟩ := hv ⟨y, hy⟩
  -- Extract equalities at the level of V (not S)
  have hcx' : cx • v = x := congrArg Subtype.val hcx
  have hcy' : cy • v = y := congrArg Subtype.val hcy
  -- trace(x) = cx * trace(v) = 1
  have hTrX : cx * v.trace = 1 := by
    have h1 : (cx • v).trace = cx • v.trace := trace_smul cx v
    have h2 : cx • v.trace = cx * v.trace := Algebra.smul_def cx v.trace
    rw [hcx', hxTr] at h1
    rw [← h2, h1]
  have hTrY : cy * v.trace = 1 := by
    have h1 : (cy • v).trace = cy • v.trace := trace_smul cy v
    have h2 : cy • v.trace = cy * v.trace := Algebra.smul_def cy v.trace
    rw [hcy', hyTr] at h1
    rw [← h2, h1]
  -- trace(v) ≠ 0 (since cx * trace(v) = 1)
  have hTrV : v.trace ≠ 0 := by
    intro hcontra
    rw [hcontra, mul_zero] at hTrX
    exact one_ne_zero hTrX.symm
  -- cx = cy since both equal 1 / trace(v)
  have hcxcy : cx = cy := by
    have h1 : cx * v.trace = cy * v.trace := by rw [hTrX, hTrY]
    exact mul_right_cancel₀ hTrV h1
  -- Therefore x = y
  rw [← hcx', ← hcy', hcxcy]

/-- Primitive implies 1-dimensional stationary space -/
theorem primitive_stationary_dim_one (L : Lindbladian n) (h : IsPrimitive L) :
    Module.finrank ℂ L.stationarySubspace = 1 := by
  -- Primitive means trivial commutant
  -- By finrank_trivialCommutant, dim(commutant) = 1
  -- By commutant_dim_eq_stationary_dim, dim(stationary) = dim(commutant) = 1
  have hCommDim := finrank_trivialCommutant L h
  rw [← commutant_dim_eq_stationary_dim L]
  exact hCommDim

/-- Primitive implies unique stationary density matrix.
    The full proof uses Frigerio's theorem (see `primitive_unique_stationary_density'`
    in Frigerio.lean). Here we note that uniqueness also follows from dim = 1
    once existence is established. -/
theorem primitive_unique_stationary_density (L : Lindbladian n) (h : IsPrimitive L) :
    ∃! ρ : Matrix (Fin n) (Fin n) ℂ,
      ρ.IsHermitian ∧ IsPosSemidef ρ ∧ ρ.trace = 1 ∧ L.IsStationaryState ρ := by
  -- Existence from exists_stationary_state
  obtain ⟨ρ₀, hρ₀Herm, hρ₀PSD, hρ₀Tr, hρ₀Stat⟩ := exists_stationary_state L
  -- Construct the existence part
  refine ⟨ρ₀, ⟨hρ₀Herm, hρ₀PSD, hρ₀Tr, hρ₀Stat⟩, ?_⟩
  -- Uniqueness
  intro ρ ⟨hρHerm, _, hρTr, hρStat⟩
  -- Both ρ and ρ₀ are in the stationary subspace
  have hρMem : ρ ∈ L.stationarySubspace := L.mem_stationarySubspace_iff ρ |>.mpr hρStat
  have hρ₀Mem : ρ₀ ∈ L.stationarySubspace := L.mem_stationarySubspace_iff ρ₀ |>.mpr hρ₀Stat
  -- dim(stationarySubspace) = 1
  have hDim := primitive_stationary_dim_one L h
  -- Apply the helper lemma
  exact eq_of_mem_finrank_one_trace_eq hDim ρ ρ₀ hρMem hρ₀Mem hρHerm hρ₀Herm hρTr hρ₀Tr

end DefectCRN.Quantum
