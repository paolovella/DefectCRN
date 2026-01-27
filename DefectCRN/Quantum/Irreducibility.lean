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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Lagrange

/-!
# Ergodicity and Irreducibility of Quantum Markov Semigroups

Terminology note: We use "ergodic" to mean Fix(L*) = ℂI (equivalently, trivial commutant).
In some QMS literature, "primitive" requires aperiodicity in addition to irreducibility.
We follow the convention of Carlen-Maas 2017 and use "ergodic" for this property.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators ComplexOrder
open Matrix

variable {n : ℕ} [NeZero n]

/-- A Lindbladian is ergodic if its commutant is trivial (Fix(L*) = ℂI).

    Equivalently: the Lindblad algebra generates all of M_n(ℂ).

    Terminology: We use "ergodic" rather than "primitive" to avoid confusion
    with the QMS literature where "primitive" sometimes requires aperiodicity. -/
def IsErgodic (L : Lindbladian n) : Prop :=
  hasTrivialCommutant L

/-- A Lindbladian is irreducible if no non-trivial projection commutes with it -/
def IsIrreducible (L : Lindbladian n) : Prop :=
  ∀ P : Matrix (Fin n) (Fin n) ℂ,
    P * P = P → P.IsHermitian → IsInCommutant L P → (P = 0 ∨ P = 1)

/-- Ergodic implies irreducible -/
theorem ergodic_implies_irreducible (L : Lindbladian n) (h : IsErgodic L) :
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

/-- Powers of a Hermitian matrix respect spectral decomposition.

    If H = U * D * U† where D = diagonal(eigenvals), then H^k = U * D^k * U†.
    This is proved by induction using the unitary property U† U = I. -/
theorem hermitian_pow_spectral (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (k : ℕ) :
    H ^ k = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
            (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) ^ k *
            star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  have hUU' : star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have hMem := hH.eigenvectorUnitary.prop
    rw [Matrix.mem_unitaryGroup_iff'] at hMem
    exact hMem
  have hUU : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
             star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have hMem := hH.eigenvectorUnitary.prop
    rw [Matrix.mem_unitaryGroup_iff] at hMem
    exact hMem
  have hSpec : H = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
                   Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
                   star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := hH.spectral_theorem
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.mul_one]
    exact hUU.symm
  | succ k ih =>
    rw [pow_succ, ih]
    conv_lhs => rhs; rw [hSpec]
    have h1 : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) ^ k *
              star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
               Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
               star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) =
              (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) ^ k *
              (star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
               (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by noncomm_ring
    rw [h1, hUU', Matrix.mul_one]
    have h2 : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) ^ k *
              Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
              (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              ((Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) ^ k *
               Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
              star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by noncomm_ring
    rw [h2, ← pow_succ]

/-- Polynomial evaluation on a Hermitian matrix respects spectral decomposition.

    For any polynomial p and Hermitian H = U * diagonal(λ) * U†, we have:
      aeval H p = U * diagonal(p(λ₁), ..., p(λₙ)) * U†

    This is a consequence of hermitian_pow_spectral: since H^k = U * D^k * U† for all k,
    and polynomial evaluation is a linear combination of powers, the result follows.
    The proof requires showing that p(diagonal(λ)) = diagonal(p(λ)). -/
theorem hermitian_aeval_spectral (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (p : Polynomial ℂ) :
    Polynomial.aeval H p = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun k => Polynomial.eval (hH.eigenvalues k : ℂ) p) *
      star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  -- The proof uses hermitian_pow_spectral and polynomial induction.
  have hUU : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
             star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have hMem := hH.eigenvectorUnitary.prop
    rw [Matrix.mem_unitaryGroup_iff] at hMem
    exact hMem
  induction p using Polynomial.induction_on with
  | h_C c =>
    -- Constant case: aeval H c = c • I = U * (c • I) * U†
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one]
    have hDiag : Matrix.diagonal (fun _ : Fin n => c) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h : i = j <;> simp [h]
    rw [hDiag, Matrix.mul_smul, smul_mul_assoc, Matrix.mul_one, hUU]
  | h_add f g hf hg =>
    -- Addition case: aeval H (f + g) = aeval H f + aeval H g
    rw [map_add, hf, hg]
    simp only [Polynomial.eval_add]
    have hDiagAdd : Matrix.diagonal (fun k => Polynomial.eval (↑(hH.eigenvalues k)) f +
                                              Polynomial.eval (↑(hH.eigenvalues k)) g) =
                    Matrix.diagonal (fun k => Polynomial.eval (↑(hH.eigenvalues k)) f) +
                    Matrix.diagonal (fun k => Polynomial.eval (↑(hH.eigenvalues k)) g) := by
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.add_apply]
      by_cases h : i = j <;> simp [h]
    rw [hDiagAdd]
    noncomm_ring
  | h_monomial k c _ =>
    -- Monomial case: aeval H (c * X^(k+1)) = c • H^(k+1)
    rw [_root_.map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hermitian_pow_spectral H hH (k + 1)]
    rw [Algebra.algebraMap_eq_smul_one]
    rw [smul_one_mul]
    rw [Matrix.diagonal_pow]
    -- Prove equality by matrix extensionality
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
               Function.comp_apply, Pi.pow_apply, smul_eq_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hlx : l = x
    · subst hlx
      simp only [↓reduceIte]
      -- Goal: c * (U i l * ev^(k+1) * U† l j) = U i l * (c * ev^(k+1)) * U† l j
      let u : ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) i l
      let v : ℂ := (star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) l j
      let e : ℂ := ↑(hH.eigenvalues l) ^ (k + 1)
      show c * (u * e * v) = u * (c * e) * v
      ring
    · simp only [if_neg hlx, mul_zero, zero_mul]

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
  -- Proof by contradiction: if H has distinct eigenvalues, we can construct
  -- a non-trivial spectral projection in the commutant, contradicting irreducibility.

  -- Step 1: Get eigenvalues from spectral theorem
  let eigenvals := hHerm.eigenvalues

  -- Step 2: Check if all eigenvalues are equal
  by_cases hAllEq : ∀ i j : Fin n, eigenvals i = eigenvals j
  · -- Case: All eigenvalues equal → H = λI
    -- The spectral theorem gives H = U * diag(λ) * U*
    -- If all λᵢ are equal to some λ, then diag(λ) = λI, so H = λI
    use (eigenvals 0 : ℂ)
    -- From spectral theorem: H = U * diagonal(eigenvals) * U*
    have hSpec := hHerm.spectral_theorem
    -- Since all eigenvalues are equal, diagonal(eigenvals) = eigenvals 0 • I
    have hDiag : Matrix.diagonal (RCLike.ofReal ∘ eigenvals) =
        (eigenvals 0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      simp only [Matrix.diagonal, Matrix.smul_apply, Matrix.one_apply, Function.comp_apply]
      by_cases hij : i = j
      · subst hij; simp [hAllEq i 0]
      · simp [hij]
    rw [hSpec, hDiag, Matrix.mul_smul, smul_mul_assoc]
    -- U * I * U* = U * U* = I for unitary U
    have hUU : (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
               star (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have hMem := hHerm.eigenvectorUnitary.prop
      rw [Matrix.mem_unitaryGroup_iff] at hMem
      exact hMem
    simp only [Matrix.mul_one, hUU]

  · -- Case: There exist distinct eigenvalues → derive contradiction
    push_neg at hAllEq
    obtain ⟨i, j, hij⟩ := hAllEq

    -- We construct a nontrivial spectral projection in the commutant.
    -- The spectral projection P_i for eigenvalue (eigenvals i) can be written
    -- as a polynomial in H via Lagrange interpolation, hence P_i ∈ commutant.
    --
    -- By irreducibility, P_i ∈ {0, I}, but P_i ≠ 0 and P_i ≠ I (since there
    -- are at least two distinct eigenvalues), giving a contradiction.

    -- Step 1: Define the spectral projection P directly from spectral decomposition
    -- P = U * E_ii * U† where E_ii has 1 at (i,i), 0 elsewhere
    let U := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    let Ustar := star U
    -- Define the indicator diagonal: 1 if eigenvalue equals eigenvals i, else 0
    let indicator : Fin n → ℂ := fun k => if eigenvals k = eigenvals i then 1 else 0
    let D := Matrix.diagonal indicator
    let P := U * D * Ustar

    -- Step 2: P is in commutant because P = p(H) for some polynomial p (Lagrange)
    -- The Lagrange basis polynomial evaluated at the distinct eigenvalues gives
    -- the indicator function, so aeval H p = P.
    -- We use commutant_closed_polynomial to conclude P ∈ commutant.
    --
    -- The formal Lagrange construction:
    -- Let S = image of eigenvals (the set of distinct eigenvalues as reals)
    -- Let v : S → ℂ be inclusion, and p := Lagrange.basis S v (eigenvals i)
    -- Then eval (eigenvals k) p = 1 if eigenvals k = eigenvals i, else 0
    -- So aeval H p = U * diagonal(indicator) * U† = P
    --
    -- For now, we accept that "spectral projections are polynomials in H"
    -- This is a standard result in linear algebra.

    -- Step 3: P is a Hermitian projection
    have hUU : Ustar * U = 1 := by
      have hMem := hHerm.eigenvectorUnitary.prop
      rw [Matrix.mem_unitaryGroup_iff'] at hMem
      exact hMem

    have hUinv : U * Ustar = 1 := by
      have hMem := hHerm.eigenvectorUnitary.prop
      rw [Matrix.mem_unitaryGroup_iff] at hMem
      exact hMem

    have hind_idem : ∀ k, indicator k * indicator k = indicator k := by
      intro k
      simp only [indicator]
      split_ifs with h <;> ring

    have hind_real : ∀ k, star (indicator k) = indicator k := by
      intro k
      simp only [indicator]
      split_ifs with h
      · simp [Complex.star_def]
      · simp [Complex.star_def]

    have hD2 : D * D = D := by
      have hD_diag : D = Matrix.diagonal indicator := rfl
      rw [hD_diag, Matrix.diagonal_mul_diagonal]
      simp only [hind_idem]

    have hP_proj : P * P = P := by
      simp only [P]
      have h1 : U * D * Ustar * (U * D * Ustar) = U * (D * (Ustar * U) * D) * Ustar := by
        noncomm_ring
      rw [h1, hUU, Matrix.mul_one, hD2]

    have hD_herm : Dᴴ = D := by
      have hD_diag : D = Matrix.diagonal indicator := rfl
      rw [hD_diag, Matrix.diagonal_conjTranspose]
      have h_star : star indicator = indicator := by
        funext k
        exact hind_real k
      rw [h_star]

    have hP_herm : P.IsHermitian := by
      unfold P
      rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul]
      -- Goal: (star U)ᴴ * (D * Uᴴ) = U * D * star U
      -- (star U)ᴴ = star (star U) = U
      -- Uᴴ = star U
      have h1 : (star U)ᴴ = U := star_star U
      have h2 : Uᴴ = star U := rfl
      rw [h1, h2, hD_herm, Matrix.mul_assoc]

    -- Step 4: P ≠ 0 and P ≠ I (since there are distinct eigenvalues)
    have hP_ne_zero : P ≠ 0 := by
      intro hP0
      -- If P = 0, then D = 0 (since U is invertible)
      have hD0 : D = 0 := by
        have h1 : Ustar * P * U = 0 := by rw [hP0]; simp
        simp only [P] at h1
        have h2 : Ustar * (U * D * Ustar) * U = D := by
          have h3 : Ustar * (U * D * Ustar) * U = (Ustar * U) * D * (Ustar * U) := by noncomm_ring
          rw [h3, hUU, Matrix.one_mul, Matrix.mul_one]
        rw [h2] at h1
        exact h1
      -- But D ii = 1, so D ≠ 0
      have hDii : D i i = 1 := by
        simp only [D, Matrix.diagonal_apply]
        simp only [indicator, ↓reduceIte]
      rw [hD0] at hDii
      simp at hDii

    have hP_ne_one : P ≠ 1 := by
      intro hP1
      -- If P = I, then D = I (since U is invertible)
      have hD1 : D = 1 := by
        have h1 : Ustar * P * U = 1 := by
          rw [hP1]
          have h3 : Ustar * 1 * U = Ustar * U := by noncomm_ring
          rw [h3, hUU]
        simp only [P] at h1
        have h2 : Ustar * (U * D * Ustar) * U = D := by
          have h3 : Ustar * (U * D * Ustar) * U = (Ustar * U) * D * (Ustar * U) := by noncomm_ring
          rw [h3, hUU, Matrix.one_mul, Matrix.mul_one]
        rw [h2] at h1
        exact h1
      -- But D j j = 0 (since eigenvals j ≠ eigenvals i)
      have hDjj : D j j = 0 := by
        simp only [D, Matrix.diagonal_apply]
        simp only [indicator, ↓reduceIte, hij.symm, ite_false]
      rw [hD1] at hDjj
      simp at hDjj

    -- Step 5: P ∈ commutant (by Lagrange interpolation argument)
    -- The spectral projection P is a polynomial in H, so by commutant_closed_polynomial, P ∈ commutant.
    -- The detailed Lagrange construction shows p(H) = P where p is the Lagrange basis polynomial.
    -- For the formal proof, we need to construct the polynomial explicitly and verify p(H) = P.
    -- This involves:
    --   1. Extract distinct eigenvalues as a Finset of ℂ
    --   2. Construct Lagrange.basis for eigenvals i on this set
    --   3. Show Polynomial.aeval H p = P using spectral theorem
    -- The key insight is that for any polynomial p, aeval H p = U * diagonal(p ∘ eigenvals) * U†
    -- and the Lagrange basis p satisfies p(eigenvals k) = indicator k.

    have hP_comm : IsInCommutant L P := by
      -- The spectral projection P can be written as p(H) for some polynomial p
      -- via Lagrange interpolation. By commutant_closed_polynomial, p(H) ∈ commutant.
      rw [← mem_commutantSubmodule_iff]
      classical
      -- Step 1: Define the set of distinct eigenvalues (as complex numbers)
      let distinctEigens : Finset ℂ := Finset.image (fun k => (eigenvals k : ℂ)) Finset.univ
      -- Step 2: The target eigenvalue is in this set
      have hi_mem : (eigenvals i : ℂ) ∈ distinctEigens :=
        Finset.mem_image_of_mem _ (Finset.mem_univ i)
      -- Step 3: id is injective on distinctEigens (trivially true)
      have h_inj : Set.InjOn (id : ℂ → ℂ) distinctEigens := Function.injective_id.injOn
      -- Step 4: Construct the Lagrange basis polynomial for eigenvalue (eigenvals i)
      -- This polynomial satisfies: p(λ) = 1 if λ = eigenvals i, else 0
      let p : Polynomial ℂ := Lagrange.basis distinctEigens id (eigenvals i : ℂ)
      -- Step 5: Show polynomial evaluates to indicator at all eigenvalue positions
      have hp_eval : ∀ k : Fin n, Polynomial.eval (eigenvals k : ℂ) p = indicator k := by
        intro k
        simp only [p, indicator, id_eq]
        by_cases hk : eigenvals k = eigenvals i
        · -- Case: eigenvals k = eigenvals i, so p evaluates to 1
          simp only [hk, ↓reduceIte]
          exact Lagrange.eval_basis_self h_inj hi_mem
        · -- Case: eigenvals k ≠ eigenvals i, so p evaluates to 0
          simp only [hk, ↓reduceIte]
          have hne : (eigenvals i : ℂ) ≠ (eigenvals k : ℂ) := by
            intro heq
            exact hk (RCLike.ofReal_injective heq.symm)
          have hk_mem : (eigenvals k : ℂ) ∈ distinctEigens :=
            Finset.mem_image_of_mem _ (Finset.mem_univ k)
          exact @Lagrange.eval_basis_of_ne ℂ _ ℂ _ distinctEigens id
            (eigenvals i : ℂ) (eigenvals k : ℂ) hne hk_mem
      -- Step 6: Show aeval H p = P using spectral theorem
      have hp_aeval : Polynomial.aeval H p = P := by
        rw [hermitian_aeval_spectral H hHerm p]
        simp only [P, U, Ustar]
        -- Show the diagonal matrices are equal
        have hD_eq : Matrix.diagonal (fun k => Polynomial.eval (hHerm.eigenvalues k : ℂ) p) = D := by
          ext a b
          simp only [Matrix.diagonal_apply, D]
          by_cases hab : a = b
          · subst hab
            simp only [↓reduceIte]
            exact hp_eval a
          · simp only [if_neg hab]
        rw [hD_eq]
      -- Step 7: Conclude P ∈ commutant using commutant_closed_polynomial
      rw [← hp_aeval]
      exact commutant_closed_polynomial L H hComm p

    -- Step 6: Apply irreducibility to get contradiction
    -- By IsIrreducible: any projection in commutant is 0 or I
    have hP01 := h P hP_proj hP_herm hP_comm
    rcases hP01 with hP0 | hP1
    · exact absurd hP0 hP_ne_zero
    · exact absurd hP1 hP_ne_one

/-- Irreducible implies ergodic.

    Proof:
    - Take any X in commutant
    - Decompose X = H + iK where H, K are Hermitian (both in commutant)
    - By hermitian_commutant_is_scalar, H = c·I and K = d·I for some c, d ∈ ℂ
    - Therefore X = (c + i·d)·I is scalar -/
theorem irreducible_implies_ergodic (L : Lindbladian n) (h : IsIrreducible L) :
    IsErgodic L := by
  unfold IsErgodic hasTrivialCommutant
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

/-- Ergodic and irreducible are equivalent -/
theorem ergodic_iff_irreducible (L : Lindbladian n) :
    IsErgodic L ↔ IsIrreducible L :=
  ⟨ergodic_implies_irreducible L, irreducible_implies_ergodic L⟩

/- NOTE ON FRIGERIO'S LEMMA:

    The claim "kernel projection of stationary state is in commutant" is FALSE in general.

    COUNTEREXAMPLE (Two-level amplitude damping):
      L = √γ |0⟩⟨1|,  H = ω|1⟩⟨1|

    This system:
    - IS ergodic (commutant = ℂI)
    - Has unique stationary state ρ = |0⟩⟨0| (rank 1, NOT faithful)
    - The kernel projection P = |1⟩⟨1| is NOT in the commutant
      (since [P, L†] = [|1⟩⟨1|, |1⟩⟨0|] = |1⟩⟨0| ≠ 0)

    The original Frigerio (1978) paper proves a DIFFERENT result:
    - For FAITHFUL stationary states, the dynamics satisfies detailed balance
    - This does NOT imply all stationary states are faithful

    The correct statement is:
    - Ergodic ⟹ unique stationary state (Theorem: ergodic_unique_stationary_density)
    - The unique stationary state may or may not be faithful
    - Faithfulness requires additional conditions (e.g., detailed balance) -/

/-- For Hermitian matrices, the quadratic form x† M x is real (im = 0).
    Proof: (x† M x)* = x† M† x = x† M x (using M = M†), so it equals its conjugate.
    A self-conjugate complex number has imaginary part zero. -/
theorem hermitian_quadForm_im_eq_zero {n : ℕ} [NeZero n]
    {M : Matrix (Fin n) (Fin n) ℂ} (hH : M.IsHermitian)
    (x : Fin n → ℂ) : Complex.im (star x ⬝ᵥ M.mulVec x) = 0 := by
  -- Show that x†Mx = star(x†Mx), which implies Im = 0
  -- Use the same pattern as in Mathlib's conj_symm for inner products
  have hSelfConj : star x ⬝ᵥ M.mulVec x = star (star x ⬝ᵥ M.mulVec x) := by
    -- star (star x ⬝ᵥ M *ᵥ x) = star (M *ᵥ x) ⬝ᵥ star (star x)  [star_dotProduct backwards]
    --                        = star (M *ᵥ x) ⬝ᵥ x               [star_star]
    --                        = (star x ᵥ* Mᴴ) ⬝ᵥ x              [star_mulVec]
    --                        = star x ⬝ᵥ Mᴴ *ᵥ x                [dotProduct_mulVec backwards]
    --                        = star x ⬝ᵥ M *ᵥ x                 [hH.eq: Mᴴ = M]
    -- Transform RHS: star (star x ⬝ᵥ M *ᵥ x)
    --              = star (M *ᵥ x) ⬝ᵥ star (star x)  [star_dotProduct]
    --              = star (M *ᵥ x) ⬝ᵥ x              [star_star]
    --              = (star x ᵥ* Mᴴ) ⬝ᵥ x             [star_mulVec]
    --              = star x ⬝ᵥ Mᴴ *ᵥ x               [dotProduct_mulVec backwards]
    --              = star x ⬝ᵥ M *ᵥ x                [hH.eq]
    conv_rhs =>
      rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec]
    -- Now RHS = (star x ᵥ* Mᴴ) ⬝ᵥ x
    rw [← Matrix.dotProduct_mulVec, hH.eq]
  -- A self-conjugate complex number has Im = 0
  have := congrArg Complex.im hSelfConj
  simp only [Complex.star_def, Complex.conj_im] at this
  -- this : im = -im, so im = 0
  linarith

/-- Our IsPosSemidef implies Mathlib's Matrix.PosSemidef -/
theorem isPosSemidef_to_matrixPosSemidef {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hPSD : IsPosSemidef ρ) : Matrix.PosSemidef ρ := by
  constructor
  · exact hPSD.1
  · intro x
    -- For Hermitian matrices, x† M x is real (im = 0) and we have re ≥ 0
    rw [RCLike.nonneg_iff]
    constructor
    · exact hPSD.2 x
    · exact hermitian_quadForm_im_eq_zero hPSD.1 x

/-- For PSD matrices, eigenvalues are non-negative.
    This uses Mathlib's Matrix.PosSemidef.eigenvalues_nonneg. -/
theorem posSemidef_eigenvalues_nonneg {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hHerm : ρ.IsHermitian) (hPSD : IsPosSemidef ρ) :
    ∀ k : Fin n, 0 ≤ hHerm.eigenvalues k := by
  intro k
  -- Convert to Mathlib's PosSemidef
  have hMPSD : Matrix.PosSemidef ρ := isPosSemidef_to_matrixPosSemidef hPSD
  -- Use Mathlib's eigenvalues_nonneg
  -- Note: hMPSD.1 is the IsHermitian witness from PosSemidef, which equals hHerm (same matrix)
  exact hMPSD.eigenvalues_nonneg k

/-- For Hermitian matrices with all positive eigenvalues, the quadratic form is
    strictly positive for nonzero vectors.

    Proof strategy:
    1. First show that PosSemidef (via eigenvalues_nonneg)
    2. Show det > 0 (product of positive eigenvalues)
    3. PosSemidef + det ≠ 0 implies PosDef (matrix is invertible)

    This is the converse of Matrix.PosDef.eigenvalues_pos. -/
theorem positive_eigenvalues_implies_pos_def {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hHerm : ρ.IsHermitian) (hall_pos : ∀ k : Fin n, 0 < hHerm.eigenvalues k) :
    IsPositiveDefinite ρ := by
  classical
  -- First, all eigenvalues are nonnegative (since they're positive)
  have hall_nonneg : ∀ k : Fin n, 0 ≤ hHerm.eigenvalues k := fun k => le_of_lt (hall_pos k)
  -- So ρ is positive semidefinite
  have hPSD : ρ.PosSemidef := hHerm.posSemidef_of_eigenvalues_nonneg hall_nonneg
  -- The determinant is positive (product of positive eigenvalues)
  have hDetPos : 0 < ρ.det := by
    rw [hHerm.det_eq_prod_eigenvalues]
    apply Finset.prod_pos
    intro i _
    exact RCLike.ofReal_pos.mpr (hall_pos i)
  -- So ρ is invertible
  have hIsUnit : IsUnit ρ := isUnit_iff_isUnit_det _ |>.mpr hDetPos.ne'.isUnit
  -- For PSD + invertible, the quadratic form is strictly positive for nonzero vectors
  -- This is because ker(ρ) = {0} for invertible ρ
  have hPosDef : ρ.PosDef := by
    refine ⟨hHerm, fun v hv => ?_⟩
    -- If v ≠ 0 and ρ is invertible, then ρv ≠ 0
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hIsUnit
    have hρv_ne : ρ *ᵥ v ≠ 0 := by
      intro h
      have h0 : ρ *ᵥ 0 = 0 := Matrix.mulVec_zero _
      have := hinj (h.trans h0.symm)
      exact hv this
    -- star v ⬝ᵥ ρ *ᵥ v ≥ 0 by PSD, and = 0 iff ρv = 0
    -- For Hermitian ρ, the quadratic form is real, so we can compare
    have hge := hPSD.2 v
    -- Since ρv ≠ 0 and ρ is Hermitian PSD, we have strict inequality
    -- The key: dotProduct_mulVec_zero_iff tells us star v ⬝ᵥ ρ *ᵥ v = 0 ↔ ρ *ᵥ v = 0
    cases' (hge.lt_or_eq) with hpos heq
    · exact hpos
    · exfalso
      have := hPSD.dotProduct_mulVec_zero_iff v |>.mp heq.symm
      exact hρv_ne this
  -- Convert to our definition
  exact ⟨hHerm, fun v hv => hPosDef.re_dotProduct_pos hv⟩

/- NOTE: The theorem "ergodic_stationary_is_faithful" was REMOVED because it is FALSE.

    COUNTEREXAMPLE: Two-level amplitude damping
      L = √γ |0⟩⟨1|,  H = ω|1⟩⟨1|

    This system is ergodic (commutant = ℂI) but the unique stationary state
    is |0⟩⟨0|, which is rank-1 (NOT faithful).

    The error in the original proof was assuming kernel_projection_mem_commutant,
    which is also false in general.

    CORRECT STATEMENT: Ergodic ⟹ unique stationary state (may or may not be faithful)
    See: ergodic_unique_stationary_density below. -/

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

/-- Ergodic with faithful stationary state implies 1-dimensional stationary space.

    The faithfulness hypothesis is needed for the Evans-Høegh-Krohn theorem
    which establishes commutant = ker(L*).

    For ergodic systems without faithful stationary states (e.g., amplitude damping
    with pure state |0⟩⟨0|), dim(stationary) = 1 still holds but requires
    a different proof (e.g., using spectral analysis). -/
theorem ergodic_stationary_dim_one (L : Lindbladian n) (h : IsErgodic L)
    (hFaith : HasFaithfulStationaryState L) :
    Module.finrank ℂ L.stationarySubspace = 1 := by
  -- Ergodic means trivial commutant
  -- By finrank_trivialCommutant, dim(commutant) = 1
  -- By commutant_dim_eq_stationary_dim, dim(stationary) = dim(commutant) = 1
  have hCommDim := finrank_trivialCommutant L h
  rw [← commutant_dim_eq_stationary_dim L hFaith]
  exact hCommDim

/-- Ergodic with faithful stationary state implies unique stationary density matrix.

    The full proof uses Frigerio's theorem (see `ergodic_unique_stationary_density'`
    in Frigerio.lean). Here we note that uniqueness also follows from dim = 1
    once existence is established.

    The faithfulness hypothesis is needed for the Evans-Høegh-Krohn theorem. -/
theorem ergodic_unique_stationary_density (L : Lindbladian n) (h : IsErgodic L)
    (hFaith : HasFaithfulStationaryState L) :
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
  have hDim := ergodic_stationary_dim_one L h hFaith
  -- Apply the helper lemma
  exact eq_of_mem_finrank_one_trace_eq hDim ρ ρ₀ hρMem hρ₀Mem hρHerm hρ₀Herm hρTr hρ₀Tr

end DefectCRN.Quantum
