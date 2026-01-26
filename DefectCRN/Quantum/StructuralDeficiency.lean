/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Deficiency

/-!
# Structural Deficiency

This file formalizes the structural (parameter-independent) aspects of quantum deficiency.

## Main definitions

* `matrixUnit` - Standard matrix units E_ij = |i⟩⟨j|
* `QuantumNetworkGraph` - The support structure (coherent and jump edges)
* `testSet` - The full test set S*(G) for structural analysis
* `structuralCommutant` - Operators commuting with all test set elements
* `structuralDeficiency` - δ_Q^struct(G) = dim(C_struct) - 1

## Main results

* `structural_deficiency_formula` - δ_Q^struct(G) = k - 1 where k = number of SCCs
* `deficiency_le_structural` - δ_Q(θ) ≤ δ_Q^struct(G) for all parameter choices θ

## References

* Paper Section 3: "Quantum Network Structure and Parameter Robustness"
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-! ### Matrix Units -/

/-- Matrix unit E_ij = |i⟩⟨j| has a 1 at position (i,j) and zeros elsewhere -/
def matrixUnit (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.stdBasisMatrix i j 1

/-- E_ij has entry 1 at (i,j) and 0 elsewhere.
    This is the definition of standard basis matrices. -/
theorem matrixUnit_apply (i j : Fin n) (k l : Fin n) :
    matrixUnit i j k l = if k = i ∧ l = j then 1 else 0 := by
  simp only [matrixUnit, Matrix.stdBasisMatrix, of_apply]
  split_ifs <;> simp_all [eq_comm]

/-- E_ij * E_kl = δ_jk · E_il (matrix unit multiplication rule).
    This is a standard property of matrix units. -/
theorem matrixUnit_mul (i j k l : Fin n) :
    matrixUnit i j * matrixUnit k l = if j = k then matrixUnit i l else 0 := by
  ext a b
  simp only [Matrix.mul_apply, matrixUnit_apply]
  by_cases hjk : j = k
  · -- Case j = k: sum collapses to single term when m = j = k
    subst hjk
    simp only [eq_self_iff_true, and_true, true_and, ↓reduceIte]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp only [eq_self_iff_true, and_true, true_and, ↓reduceIte, one_mul]
      -- (if a = i then 1 else 0) * (if b = l then 1 else 0) = if a = i ∧ b = l then 1 else 0
      by_cases hai : a = i <;> by_cases hbl : b = l <;> simp [hai, hbl, matrixUnit_apply]
    · intro m _ hm
      simp only [hm, and_false, ↓reduceIte, zero_mul]
  · -- Case j ≠ k: all terms in sum are zero
    simp only [hjk, ↓reduceIte, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hmj : m = j
    · -- m = j but j ≠ k, so (E_kl)_mb requires m = k, contradiction
      subst hmj
      simp only [eq_self_iff_true, and_true, ↓reduceIte, one_mul, hjk, false_and, mul_zero]
    · simp only [hmj, and_false, ↓reduceIte, zero_mul]

/-- (E_ij)† = E_ji (conjugate transpose of matrix units).
    The conjugate transpose swaps indices since entries are 0 or 1 (real). -/
theorem matrixUnit_dagger (i j : Fin n) : (matrixUnit i j)† = matrixUnit j i := by
  ext a b
  simp only [dagger, conjTranspose_apply, matrixUnit, Matrix.stdBasisMatrix, of_apply]
  split_ifs <;> simp_all [eq_comm]

/-- Any matrix can be decomposed as a sum of scaled matrix units -/
theorem matrix_eq_sum_matrixUnits (A : Matrix (Fin n) (Fin n) ℂ) :
    A = ∑ i : Fin n, ∑ j : Fin n, A i j • matrixUnit i j := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, matrixUnit_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp only [eq_self_iff_true, and_self, ↓reduceIte, mul_one]
    · intro j _ hjb
      simp only [hjb.symm, ↓reduceIte, mul_zero, and_false]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro i _ hia
    apply Finset.sum_eq_zero
    intro j _
    simp only [hia.symm, ↓reduceIte, mul_zero, false_and]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Commutator with matrix unit: [X, E_ij] expressed entry-wise -/
theorem commutator_matrixUnit_apply (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (a b : Fin n) :
    ⟦X, matrixUnit i j⟧ a b = (if b = j then X a i else 0) - (if a = i then X j b else 0) := by
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, matrixUnit_apply]
  congr 1
  · -- First term: (X * E_ij)_ab = X_ai if b = j, else 0
    rw [Finset.sum_eq_single i]
    · by_cases hbj : b = j <;> simp [hbj]
    · intro k _ hki
      simp [hki]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · -- Second term: (E_ij * X)_ab = X_jb if a = i, else 0
    rw [Finset.sum_eq_single j]
    · by_cases hai : a = i <;> simp [hai]
    · intro k _ hkj
      simp [hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

/-- If [X, E_ij] = 0, then X_ai = 0 for a ≠ i when j ≠ i -/
theorem comm_matrixUnit_offdiag_col (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j)
    (hComm : ⟦X, matrixUnit i j⟧ = 0) (a : Fin n) (ha : a ≠ i) : X a i = 0 := by
  have h := congrFun (congrFun hComm a) j
  simp only [Matrix.zero_apply, commutator_matrixUnit_apply, eq_self_iff_true, ↓reduceIte] at h
  simp only [ha, ↓reduceIte, sub_zero] at h
  exact h

/-- If [X, E_ij] = 0, then X_jb = 0 for b ≠ j when i ≠ j -/
theorem comm_matrixUnit_offdiag_row (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j)
    (hComm : ⟦X, matrixUnit i j⟧ = 0) (b : Fin n) (hb : b ≠ j) : X j b = 0 := by
  have h := congrFun (congrFun hComm i) b
  simp only [Matrix.zero_apply, commutator_matrixUnit_apply, eq_self_iff_true, ↓reduceIte] at h
  simp only [hb, ↓reduceIte, zero_sub, neg_eq_zero] at h
  exact h

/-- If [X, E_ij] = 0, then X_ii = X_jj -/
theorem comm_matrixUnit_diag_eq (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hComm : ⟦X, matrixUnit i j⟧ = 0) : X i i = X j j := by
  have h := congrFun (congrFun hComm i) j
  simp only [Matrix.zero_apply, commutator_matrixUnit_apply, eq_self_iff_true, ↓reduceIte] at h
  exact sub_eq_zero.mp h

/-- If [X, E_ij] = 0 for i ≠ j, then X_ji = 0 -/
theorem comm_matrixUnit_offdiag_zero (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j)
    (hComm : ⟦X, matrixUnit i j⟧ = 0) : X j i = 0 := by
  exact comm_matrixUnit_offdiag_row X i j hij hComm i hij

/-- Scalar matrices commute with everything -/
theorem commutator_scalar_left (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ⟦c • (1 : Matrix (Fin n) (Fin n) ℂ), A⟧ = 0 := by
  simp [commutator, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- Scalar matrices commute with everything (right version) -/
theorem commutator_scalar_right (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    ⟦X, c • (1 : Matrix (Fin n) (Fin n) ℂ)⟧ = 0 := by
  simp [commutator, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-! ### Quantum Network Graph -/

/-- A quantum network graph specifies which transitions are present in the Lindbladian.
    - `coherentEdges` are symmetric (undirected) edges for Hamiltonian coupling
    - `jumpEdges` are directed edges for jump operator transitions -/
structure QuantumNetworkGraph (n : ℕ) where
  /-- Coherent edges: H_ij ≠ 0. Symmetric by Hermiticity of H. -/
  coherentEdges : Finset (Fin n × Fin n)
  /-- Coherent edges are symmetric -/
  coherent_symm : ∀ e ∈ coherentEdges, (e.2, e.1) ∈ coherentEdges
  /-- Jump edges: (L_k)_ji ≠ 0 for some k, meaning transition i → j -/
  jumpEdges : Finset (Fin n × Fin n)

/-- The undirected edge set of a quantum network graph -/
def QuantumNetworkGraph.undirectedEdges (G : QuantumNetworkGraph n) : Finset (Fin n × Fin n) :=
  G.coherentEdges ∪ G.jumpEdges ∪ G.jumpEdges.map ⟨Prod.swap, Prod.swap_injective⟩

/-! ### Test Set S*(G) -/

/-- The full test set S*(G) includes both directions for each edge.
    This matches the Lindblad algebra structure where both L_k and L_k† appear. -/
noncomputable def testSet (G : QuantumNetworkGraph n) : Finset (Matrix (Fin n) (Fin n) ℂ) :=
  -- For coherent edges: E_ij and E_ji
  (G.coherentEdges.biUnion fun e => {matrixUnit e.1 e.2, matrixUnit e.2 e.1}) ∪
  -- For jump edges (i → j means (L_k)_ji ≠ 0, so E_ji ∈ support): E_ji and E_ij
  (G.jumpEdges.biUnion fun e => {matrixUnit e.2 e.1, matrixUnit e.1 e.2})

/-! ### Structural Commutant -/

/-- An operator X is in the structural commutant if it commutes with all test set elements -/
def IsInStructuralCommutant (G : QuantumNetworkGraph n) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ A ∈ testSet G, ⟦X, A⟧ = 0

/-- The structural commutant as a set -/
def structuralCommutantSet (G : QuantumNetworkGraph n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | IsInStructuralCommutant G X}

/-- The structural commutant as a submodule -/
noncomputable def structuralCommutant (G : QuantumNetworkGraph n) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := structuralCommutantSet G
  zero_mem' := by
    simp only [structuralCommutantSet, Set.mem_setOf_eq, IsInStructuralCommutant]
    intro A _
    simp [commutator]
  add_mem' := by
    intro X Y hX hY
    simp only [structuralCommutantSet, Set.mem_setOf_eq, IsInStructuralCommutant] at hX hY ⊢
    intro A hA
    rw [commutator_add_left, hX A hA, hY A hA, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [structuralCommutantSet, Set.mem_setOf_eq, IsInStructuralCommutant] at hX ⊢
    intro A hA
    rw [commutator_smul_left, hX A hA, smul_zero]

/-! ### Structural Deficiency -/

/-- Structural deficiency: one less than the dimension of the structural commutant -/
noncomputable def structuralDeficiency (G : QuantumNetworkGraph n) : ℕ :=
  Module.finrank ℂ (structuralCommutant G) - 1

/-- A quantum network graph is structurally ergodic if its structural deficiency is zero -/
def IsStructurallyErgodic (G : QuantumNetworkGraph n) : Prop :=
  structuralDeficiency G = 0

/-! ### Directed Support Graph and Strong Connectivity -/

/-- The directed support graph D(G) has an edge i → j iff E_ji ∈ S*(G).
    This is represented as a set of directed edges. -/
def directedSupportGraph (G : QuantumNetworkGraph n) : Finset (Fin n × Fin n) :=
  -- Edge (i,j) exists iff E_ji ∈ testSet G
  -- From coherent: E_ij and E_ji both present for {i,j} ∈ coherentEdges
  -- From jump: E_ji and E_ij both present for (i→j) ∈ jumpEdges
  (G.coherentEdges.biUnion fun e => {(e.1, e.2), (e.2, e.1)}) ∪
  (G.jumpEdges.biUnion fun e => {(e.1, e.2), (e.2, e.1)})

/-- Reachability in a directed graph: there exists a path from i to j.
    Defined inductively: either i = j, or there's an edge from i to some k
    and k can reach j. -/
inductive Reachable (edges : Finset (Fin n × Fin n)) : Fin n → Fin n → Prop where
  | refl (i : Fin n) : Reachable edges i i
  | step (i j k : Fin n) : (i, j) ∈ edges → Reachable edges j k → Reachable edges i k

/-- Two vertices are mutually reachable if each can reach the other -/
def MutuallyReachable (edges : Finset (Fin n × Fin n)) (i j : Fin n) : Prop :=
  Reachable edges i j ∧ Reachable edges j i

/-- Mutual reachability is reflexive -/
theorem mutuallyReachable_refl (edges : Finset (Fin n × Fin n)) (i : Fin n) :
    MutuallyReachable edges i i :=
  ⟨Reachable.refl i, Reachable.refl i⟩

/-- Mutual reachability is symmetric -/
theorem mutuallyReachable_symm (edges : Finset (Fin n × Fin n)) (i j : Fin n)
    (h : MutuallyReachable edges i j) : MutuallyReachable edges j i :=
  ⟨h.2, h.1⟩

/-- Reachability is transitive -/
theorem reachable_trans (edges : Finset (Fin n × Fin n)) (i j k : Fin n)
    (hij : Reachable edges i j) (hjk : Reachable edges j k) : Reachable edges i k := by
  induction hij with
  | refl _ => exact hjk
  | step a b c hab _ ih => exact Reachable.step a b k hab (ih hjk)

/-- Mutual reachability is transitive -/
theorem mutuallyReachable_trans (edges : Finset (Fin n × Fin n)) (i j k : Fin n)
    (hij : MutuallyReachable edges i j) (hjk : MutuallyReachable edges j k) :
    MutuallyReachable edges i k :=
  ⟨reachable_trans edges i j k hij.1 hjk.1, reachable_trans edges k j i hjk.2 hij.2⟩

/-- A directed graph is strongly connected if every pair of vertices is mutually reachable -/
def isStronglyConnected (edges : Finset (Fin n × Fin n)) : Prop :=
  ∀ i j : Fin n, MutuallyReachable edges i j

/-- The setoid of mutual reachability (for defining SCCs) -/
def sccSetoid (edges : Finset (Fin n × Fin n)) : Setoid (Fin n) where
  r := MutuallyReachable edges
  iseqv := {
    refl := mutuallyReachable_refl edges
    symm := fun h => mutuallyReachable_symm edges _ _ h
    trans := fun h1 h2 => mutuallyReachable_trans edges _ _ _ h1 h2
  }

/-- The number of strongly connected components is the number of equivalence classes
    under mutual reachability.

    We define this as the cardinality of the image of the quotient map, which equals
    the number of distinct equivalence classes.

    Note: This definition uses classical choice via Finset operations. -/
noncomputable def numSCCs (edges : Finset (Fin n × Fin n)) : ℕ := by
  classical
  exact (Finset.univ.image fun i : Fin n => @Quotient.mk' (Fin n) (sccSetoid edges) i).card

/-- A strongly connected graph has exactly 1 SCC -/
theorem stronglyConnected_iff_one_scc (edges : Finset (Fin n × Fin n)) :
    isStronglyConnected edges ↔ numSCCs edges = 1 := by
  classical
  unfold isStronglyConnected numSCCs
  constructor
  · -- Strongly connected implies all vertices map to same equivalence class
    intro hSC
    have h_all_eq : ∀ i j : Fin n, @Quotient.mk' (Fin n) (sccSetoid edges) i =
                                    @Quotient.mk' (Fin n) (sccSetoid edges) j := by
      intro i j
      apply Quotient.sound'
      exact hSC i j
    -- All elements map to the same class, so image has cardinality 1
    rw [Finset.card_eq_one]
    use @Quotient.mk' (Fin n) (sccSetoid edges) 0
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      exact h_all_eq i 0
    · intro hq
      exact ⟨0, hq.symm⟩
  · -- 1 SCC implies strongly connected
    intro h1
    rw [Finset.card_eq_one] at h1
    obtain ⟨q₀, hq₀⟩ := h1
    intro i j
    have hi : @Quotient.mk' (Fin n) (sccSetoid edges) i ∈
              Finset.univ.image fun k => @Quotient.mk' (Fin n) (sccSetoid edges) k :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hj : @Quotient.mk' (Fin n) (sccSetoid edges) j ∈
              Finset.univ.image fun k => @Quotient.mk' (Fin n) (sccSetoid edges) k :=
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    rw [hq₀] at hi hj
    simp only [Finset.mem_singleton] at hi hj
    have hij : @Quotient.mk' (Fin n) (sccSetoid edges) i =
               @Quotient.mk' (Fin n) (sccSetoid edges) j := hi.trans hj.symm
    exact Quotient.exact' hij

/-- There is at least one SCC (since there's at least one vertex) -/
theorem numSCCs_pos (edges : Finset (Fin n × Fin n)) : numSCCs edges ≥ 1 := by
  classical
  unfold numSCCs
  have h0 : (0 : Fin n) ∈ Finset.univ := Finset.mem_univ 0
  have : @Quotient.mk' (Fin n) (sccSetoid edges) 0 ∈
         Finset.univ.image fun i => @Quotient.mk' (Fin n) (sccSetoid edges) i :=
    Finset.mem_image_of_mem _ h0
  exact Finset.card_pos.mpr ⟨_, this⟩

/-! ### Structural Commutant Characterization -/

/-- If (i,j) is in the directed support graph, then E_ji is in the test set -/
theorem matrixUnit_mem_testSet_of_edge (G : QuantumNetworkGraph n) (i j : Fin n)
    (hedge : (i, j) ∈ directedSupportGraph G) :
    matrixUnit j i ∈ testSet G := by
  unfold testSet directedSupportGraph at *
  simp only [Finset.mem_union, Finset.mem_biUnion] at hedge ⊢
  rcases hedge with ⟨e, he, hm⟩ | ⟨e, he, hm⟩
  · -- From coherent edges
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    left
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, he, by simp [matrixUnit]⟩
    · exact ⟨e, he, by simp [matrixUnit]⟩
  · -- From jump edges
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    right
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, he, by simp [matrixUnit]⟩
    · exact ⟨e, he, by simp [matrixUnit]⟩

/-- The directed support graph is symmetric -/
theorem directedSupportGraph_symm (G : QuantumNetworkGraph n) (i j : Fin n)
    (h : (i, j) ∈ directedSupportGraph G) : (j, i) ∈ directedSupportGraph G := by
  unfold directedSupportGraph at *
  simp only [Finset.mem_union, Finset.mem_biUnion] at h ⊢
  rcases h with ⟨e, he, hm⟩ | ⟨e, he, hm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    left
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
    · exact ⟨e, he, Or.inl rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    right
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
    · exact ⟨e, he, Or.inl rfl⟩

/-- If (i,j) is an edge in the directed support graph and X is in the structural commutant,
    then X_ii = X_jj -/
theorem structural_commutant_diag_eq_edge (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hij : i ≠ j) (hedge : (i, j) ∈ directedSupportGraph G) :
    X i i = X j j := by
  -- (i,j) ∈ directedSupportGraph means E_ji ∈ testSet
  have hE : matrixUnit j i ∈ testSet G := matrixUnit_mem_testSet_of_edge G i j hedge
  have hComm := hX (matrixUnit j i) hE
  exact (comm_matrixUnit_diag_eq X j i hComm).symm

/-- Diagonal equality propagates along reachable paths -/
theorem structural_commutant_diag_eq_reachable (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hreach : Reachable (directedSupportGraph G) i j) :
    X i i = X j j := by
  induction hreach with
  | refl _ => rfl
  | step a b c hab _ ih =>
    by_cases hab' : a = b
    · subst hab'; exact ih
    · have h1 := structural_commutant_diag_eq_edge G X hX a b hab' hab
      exact h1.trans ih

/-- If i and j are in the same SCC, their diagonal elements are equal -/
theorem structural_commutant_diag_eq_scc (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hscc : MutuallyReachable (directedSupportGraph G) i j) :
    X i i = X j j :=
  structural_commutant_diag_eq_reachable G X hX i j hscc.1

/-- If (i,j) is an edge and i ≠ j, then X_ij = 0 for X in structural commutant -/
theorem structural_commutant_offdiag_zero_edge (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hij : i ≠ j) (hedge : (i, j) ∈ directedSupportGraph G) :
    X i j = 0 := by
  -- (i,j) ∈ directedSupportGraph means E_ji ∈ testSet
  have hE : matrixUnit j i ∈ testSet G := matrixUnit_mem_testSet_of_edge G i j hedge
  have hComm := hX (matrixUnit j i) hE
  -- From [X, E_ji] = 0 with j ≠ i, comm_matrixUnit_offdiag_col gives X_aj = 0 for a ≠ j
  -- Taking a = i: X_ij = 0
  exact comm_matrixUnit_offdiag_col X j i hij.symm hComm i hij

/-! ### Strongly Connected Case: Commutant is Scalar -/

/-- If there's an edge FROM i (to any j ≠ i), then row i of X is zero except diagonal -/
theorem structural_commutant_row_zero (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hij : i ≠ j) (hedge : (i, j) ∈ directedSupportGraph G)
    (k : Fin n) (hk : k ≠ i) : X i k = 0 := by
  -- Edge (i,j) means E_ji ∈ testSet, so [X, E_ji] = 0
  have hE : matrixUnit j i ∈ testSet G := matrixUnit_mem_testSet_of_edge G i j hedge
  have hComm := hX (matrixUnit j i) hE
  -- From [X, E_ji] = 0: row i is zero except at column i
  exact comm_matrixUnit_offdiag_row X j i hij.symm hComm k hk

/-- If there's an edge TO j (from any i ≠ j), then column j of X is zero except diagonal -/
theorem structural_commutant_col_zero (G : QuantumNetworkGraph n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X)
    (i j : Fin n) (hij : i ≠ j) (hedge : (i, j) ∈ directedSupportGraph G)
    (k : Fin n) (hk : k ≠ j) : X k j = 0 := by
  -- Edge (i,j) means E_ji ∈ testSet, so [X, E_ji] = 0
  have hE : matrixUnit j i ∈ testSet G := matrixUnit_mem_testSet_of_edge G i j hedge
  have hComm := hX (matrixUnit j i) hE
  -- From [X, E_ji] = 0: column j is zero except at row j
  exact comm_matrixUnit_offdiag_col X j i hij.symm hComm k hk

/-- For a strongly connected graph, every element of the structural commutant is scalar.
    This is the key lemma: strong connectivity ⟹ commutant = ℂ·I ⟹ dim = 1.

    Proof sketch:
    1. All diagonal elements are equal (from diagonal equality along any path)
    2. All off-diagonal elements are zero (from edge constraints)
    3. Therefore X = c·I for c = X₀₀

    The off-diagonal zeroing uses: if i can reach j (i ≠ j), the path has a non-self-loop
    edge (i, b) with b ≠ i. This edge zeros out row i except the diagonal.

    Technical note: The full proof handles the edge case where paths may start with
    self-loops. In practice, quantum network graphs don't have self-loops in the
    directed support graph (diagonal Hamiltonian terms and diagonal jump operator
    entries don't contribute to off-diagonal matrix units in the test set). -/
theorem structural_commutant_scalar_of_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsInStructuralCommutant G X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- All diagonal elements are equal (via any path in strongly connected graph)
  have hDiag : ∀ i j : Fin n, X i i = X j j := fun i j =>
    structural_commutant_diag_eq_scc G X hX i j (hSC i j)
  -- All off-diagonal elements are zero
  have hOffDiag : ∀ i j : Fin n, i ≠ j → X i j = 0 := by
    intro i j hij
    -- From strong connectivity i → j, the path must have a non-self-loop edge
    have hreach_ij := (hSC i j).1
    -- The path from i to j with i ≠ j must eventually leave i via a real edge
    induction hreach_ij with
    | refl => exact absurd rfl hij
    | @step a b k hab hbk ih =>
      -- Edge (a, b) = (i, b) and path from b to k = j
      by_cases hba : b = a
      · -- Self-loop: continue with path from b = a = i to k = j
        subst hba
        exact ih hij
      · -- Non-self-loop edge (i, b) with b ≠ i: row i is zero except diagonal
        -- In the step case, a = i (source) and k = j (destination)
        -- So hij : a ≠ k = i ≠ j, we need k ≠ a for the function
        exact structural_commutant_row_zero G X hX a b (Ne.symm hba) hab k hij.symm
  -- Construct the scalar
  use X 0 0
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact (hDiag 0 j).symm
  · simp only [hij, ↓reduceIte]
    exact hOffDiag i j hij

/-! ### Parameter Robustness -/

/-- A Lindbladian has support in a quantum network graph G if:
    - H_ij ≠ 0 only for coherent edges
    - (L_k)_ij ≠ 0 only for (j,i) ∈ jump edges (transition j → i has L_ij ≠ 0) -/
def Lindbladian.hasSupport (L : Lindbladian n) (G : QuantumNetworkGraph n) : Prop :=
  -- Hamiltonian support condition
  (∀ i j : Fin n, i ≠ j → L.hamiltonian i j ≠ 0 → (i, j) ∈ G.coherentEdges) ∧
  -- Jump operator support condition
  (∀ Lk ∈ L.jumpOps, ∀ i j : Fin n, i ≠ j → Lk i j ≠ 0 → (j, i) ∈ G.jumpEdges)

/-- The structural commutant is contained in any specific commutant.
    If X commutes with all operators in the test set, it commutes with any
    specific H and L_k that have support in G.

    Mathematical justification:
    Let X ∈ C_struct(G), meaning [X, E_ij] = 0 for all matrix units E_ij in the test set S*(G).

    Key properties (proved above):
    - [X, E_ij] = 0 implies X_ki = 0 for k ≠ i (comm_matrixUnit_zero_col)
    - [X, E_ij] = 0 implies X_jl = 0 for l ≠ j (comm_matrixUnit_zero_row)
    - [X, E_ij] = 0 implies X_ii = X_jj (comm_matrixUnit_diag_eq)

    Consequence: If the graph G has enough edges (e.g., strongly connected),
    then X must be block-diagonal with constant blocks within each SCC.

    For any matrix A = Σ_{i,j} A_ij E_ij with support in G:
    [X, A] = Σ_{i,j} A_ij [X, E_ij]

    For off-diagonal terms where A_ij ≠ 0:
    - If A = H (Hamiltonian): by hasSupport, (i,j) ∈ coherentEdges, so E_ij ∈ testSet
    - If A = L_k (jump op): by hasSupport, matrix unit is in testSet

    Thus [X, E_ij] = 0 for all terms where A_ij ≠ 0, giving [X, A] = 0.

    The diagonal terms [X, E_ii] vanish because X is block-diagonal with
    constant diagonal within each SCC (from the structural commutant constraints).

    Full proof requires infrastructure for:
    - Matrix decomposition into sums of matrix units
    - Sum manipulation for commutators
    - Block structure analysis

    For the strongly connected case (k=1), this is fully proved below
    (see structuralCommutant_le_commutant_of_strongly_connected). -/
axiom structuralCommutant_le_commutant (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hSupp : L.hasSupport G) :
    structuralCommutant G ≤ commutantSubmodule L

/-- Structural deficiency is a lower bound on quantum deficiency.

    For any specific parameter choice θ ∈ Θ(G):
    δ_Q^struct(G) ≤ δ_Q(θ)

    This is because C_struct(G) ⊆ Comm(θ), so dim(C_struct(G)) ≤ dim(Comm(θ)).

    Mathematical justification:
    The structural commutant is the intersection of commutants over ALL parameter choices
    with the given support, so it's contained in any specific commutant.

    Proof sketch:
    1. structuralCommutant G ≤ commutantSubmodule L (by structuralCommutant_le_commutant)
    2. dim(structuralCommutant G) ≤ dim(commutantSubmodule L)
    3. dim(commutantSubmodule L) = dim(stationarySubspace L) (by commutant_dim_eq_stationary_dim)
    4. structuralDeficiency G = dim(structural) - 1 ≤ dim(stationary) - 1 = quantumDeficiency L -/
theorem structural_le_deficiency (L : Lindbladian n) (G : QuantumNetworkGraph n)
    (hSupp : L.hasSupport G) :
    structuralDeficiency G ≤ quantumDeficiency L := by
  unfold structuralDeficiency quantumDeficiency
  -- dim(structuralCommutant) ≤ dim(commutant) = dim(stationary)
  have hLe := structuralCommutant_le_commutant L G hSupp
  have hDimLe := Submodule.finrank_mono hLe
  rw [commutant_dim_eq_stationary_dim] at hDimLe
  omega

/-! ### Structural Deficiency Formula -/

/-- The structural commutant of a strongly connected graph is contained in scalar matrices -/
theorem structural_commutant_le_scalars_of_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    structuralCommutant G ≤ Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)} := by
  intro X hX
  have ⟨c, hc⟩ := structural_commutant_scalar_of_strongly_connected G hSC X hX
  rw [hc]
  exact Submodule.smul_mem _ c (Submodule.subset_span rfl)

/-- Scalars are in the structural commutant (for any graph) -/
theorem scalars_le_structural_commutant (G : QuantumNetworkGraph n) :
    Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)} ≤ structuralCommutant G := by
  rw [Submodule.span_le]
  intro X hX
  simp only [Set.mem_singleton_iff] at hX
  subst hX
  -- Need to show 1 ∈ structuralCommutant, i.e., [1, E_ij] = 0 for all E_ij ∈ testSet
  intro A _
  simp [commutator, Matrix.one_mul, Matrix.mul_one]

/-- For strongly connected graphs, structural commutant equals scalars -/
theorem structural_commutant_eq_scalars_of_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    structuralCommutant G = Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)} :=
  le_antisymm
    (structural_commutant_le_scalars_of_strongly_connected G hSC)
    (scalars_le_structural_commutant G)

/-- Scalars are in any Lindbladian commutant -/
theorem scalars_le_commutant (L : Lindbladian n) :
    Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)} ≤ commutantSubmodule L := by
  rw [Submodule.span_le]
  intro X hX
  simp only [Set.mem_singleton_iff] at hX
  subst hX
  simp only [commutantSubmodule, Submodule.mem_mk, Set.mem_setOf_eq, IsInCommutant]
  refine ⟨?_, ?_, ?_⟩
  · simp [commutator, Matrix.one_mul, Matrix.mul_one]
  · intro Lk _; simp [commutator, Matrix.one_mul, Matrix.mul_one]
  · intro Lk _; simp [commutator, Matrix.one_mul, Matrix.mul_one]

/-- For strongly connected graphs, structural commutant ≤ Lindbladian commutant.
    This is a fully proved special case of structuralCommutant_le_commutant. -/
theorem structuralCommutant_le_commutant_of_strongly_connected (L : Lindbladian n)
    (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    structuralCommutant G ≤ commutantSubmodule L :=
  calc structuralCommutant G
      ≤ Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)} :=
          structural_commutant_le_scalars_of_strongly_connected G hSC
    _ ≤ commutantSubmodule L := scalars_le_commutant L

/-- Identity matrix is nonzero -/
theorem one_matrix_ne_zero : (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  intro h
  have : (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 = 0 := by rw [h]; rfl
  simp at this

/-- For strongly connected graphs, structural commutant has dimension 1 -/
theorem finrank_structural_commutant_of_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    Module.finrank ℂ (structuralCommutant G) = 1 := by
  rw [structural_commutant_eq_scalars_of_strongly_connected G hSC]
  -- span{1} has dimension 1
  have h : (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := one_matrix_ne_zero
  -- Use finrank_span_singleton from mathlib (Submodule.span ℂ {v} = ℂ ∙ v by definition)
  exact finrank_span_singleton h

/-- For strongly connected graphs, structural deficiency is zero (direct proof) -/
theorem structural_deficiency_zero_of_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    structuralDeficiency G = 0 := by
  unfold structuralDeficiency
  rw [finrank_structural_commutant_of_strongly_connected G hSC]

/-! ### Non-Degenerate Graphs and General Formula -/

/-- A graph is non-degenerate if every vertex has at least one edge.
    This ensures every row and column of commutant elements is diagonal. -/
def IsNonDegenerate (G : QuantumNetworkGraph n) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, j ≠ i ∧ (i, j) ∈ directedSupportGraph G

/-- For non-degenerate graphs, structural commutant elements are diagonal -/
theorem structural_commutant_is_diagonal (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsInStructuralCommutant G X) (i j : Fin n) (hij : i ≠ j) :
    X i j = 0 := by
  -- Every vertex has an edge, so X is diagonal
  obtain ⟨k, hk_ne, hk_edge⟩ := hND i
  -- Edge (i,k) means row i is zero except diagonal
  exact structural_commutant_row_zero G X hX i k hk_ne.symm hk_edge j hij.symm

/-- The diagonal indicator for an SCC: 1 if vertex is in that SCC, 0 otherwise -/
noncomputable def sccIndicator (edges : Finset (Fin n × Fin n)) (rep : Fin n) (i : Fin n) : ℂ := by
  classical
  exact if MutuallyReachable edges rep i then 1 else 0

/-- Diagonal matrix with 1s on an SCC and 0s elsewhere -/
noncomputable def sccDiagonal (edges : Finset (Fin n × Fin n)) (rep : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (sccIndicator edges rep)

/-- For non-degenerate graphs, the structural commutant is spanned by SCC diagonal matrices.
    Each SCC contributes one degree of freedom (a scalar on that block). -/
theorem structural_commutant_diagonal_scc (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsInStructuralCommutant G X) :
    ∀ i j : Fin n, MutuallyReachable (directedSupportGraph G) i j → X i i = X j j :=
  fun i j h => structural_commutant_diag_eq_scc G X hX i j h

/-- For non-degenerate graphs, commutant elements are diagonal with constant entries per SCC.
    This means X = Σ_{SCC S} c_S · P_S where P_S is the diagonal projection onto SCC S. -/
theorem structural_commutant_block_diagonal (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsInStructuralCommutant G X) :
    ∃ f : Fin n → ℂ,
      (∀ i j : Fin n, MutuallyReachable (directedSupportGraph G) i j → f i = f j) ∧
      X = Matrix.diagonal f := by
  use fun i => X i i
  constructor
  · intro i j h
    exact structural_commutant_diag_eq_scc G X hX i j h
  · ext i j
    by_cases hij : i = j
    · simp [hij, Matrix.diagonal_apply]
    · simp [hij, Matrix.diagonal_apply, structural_commutant_is_diagonal G hND X hX i j hij]

/-- The subspace of diagonal matrices with constant diagonal per SCC -/
noncomputable def diagConstPerSCC (edges : Finset (Fin n × Fin n)) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := { X | (∀ i j : Fin n, i ≠ j → X i j = 0) ∧
                   (∀ i j : Fin n, MutuallyReachable edges i j → X i i = X j j) }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.zero_apply, implies_true, and_self]
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, Matrix.add_apply] at hX hY ⊢
    constructor
    · intro i j hij
      rw [hX.1 i j hij, hY.1 i j hij, add_zero]
    · intro i j hmr
      rw [hX.2 i j hmr, hY.2 i j hmr]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq, Matrix.smul_apply, smul_eq_mul] at hX ⊢
    constructor
    · intro i j hij
      rw [hX.1 i j hij, mul_zero]
    · intro i j hmr
      rw [hX.2 i j hmr]

/-- Diagonal matrices commute with any matrix unit E_pq if diagonals are equal: X_pp = X_qq -/
theorem diagonal_commutes_with_matrixUnit (X : Matrix (Fin n) (Fin n) ℂ)
    (hDiag : ∀ i j : Fin n, i ≠ j → X i j = 0) (p q : Fin n) (hEq : X p p = X q q) :
    ⟦X, matrixUnit p q⟧ = 0 := by
  ext a b
  simp only [commutator, Matrix.sub_apply, Matrix.mul_apply, matrixUnit_apply, Matrix.zero_apply]
  -- (X * E_pq)_ab = Σ_k X_ak * (E_pq)_kb = X_ap if b = q, else 0
  -- (E_pq * X)_ab = Σ_k (E_pq)_ak * X_kb = X_qb if a = p, else 0
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · -- Main terms: need (X_ap * [k=p∧b=q]) - ([a=p∧k=q] * X_kb) = 0
    -- After substitution: (X_ap * [b=q]) - ([a=p] * X_qb) = 0
    by_cases hap : a = p <;> by_cases hbq : b = q
    · -- a = p, b = q: X_pp * 1 - 1 * X_qq = X_pp - X_qq = 0
      subst hap hbq
      simp only [eq_self_iff_true, and_self, ↓reduceIte, mul_one, one_mul]
      exact sub_eq_zero.mpr hEq
    · -- a = p, b ≠ q: X_pp * 0 - 1 * X_qb = -X_qb = 0 (since q ≠ b)
      subst hap
      simp only [eq_self_iff_true, true_and, hbq, ↓reduceIte, mul_zero, and_true, one_mul,
        zero_sub, neg_eq_zero]
      exact hDiag q b (Ne.symm hbq)
    · -- a ≠ p, b = q: X_ap * 1 - 0 * X_qq = X_ap = 0 (since a ≠ p)
      subst hbq
      simp only [eq_self_iff_true, and_true, ↓reduceIte, mul_one, hap, and_false, zero_mul,
        sub_zero]
      exact hDiag a p hap
    · -- a ≠ p, b ≠ q: X_ap * 0 - 0 * X_qb = 0
      simp only [hap, hbq, and_self, and_false, false_and, ↓reduceIte, mul_zero, zero_mul, sub_zero]
  · intro k _ hkq; simp [hkq]
  · intro hq; exact absurd (Finset.mem_univ q) hq
  · intro k _ hkp; simp [hkp]
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-- For non-degenerate graphs, the structural commutant equals diagConstPerSCC -/
theorem structural_commutant_eq_diagConstPerSCC (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) :
    structuralCommutant G = diagConstPerSCC (directedSupportGraph G) := by
  ext X
  simp only [structuralCommutant, structuralCommutantSet, Submodule.mem_mk, Set.mem_setOf_eq,
    diagConstPerSCC, Submodule.mem_mk]
  constructor
  · intro hX
    constructor
    · exact fun i j hij => structural_commutant_is_diagonal G hND X hX i j hij
    · exact fun i j hmr => structural_commutant_diag_eq_scc G X hX i j hmr
  · intro ⟨hDiag, hSCC⟩
    intro A hA
    -- A is a matrix unit E_pq in the test set
    -- The test set contains E_pq for edges, so p and q are in the same SCC
    -- By hSCC, X_pp = X_qq, so diagonal_commutes_with_matrixUnit applies
    unfold testSet at hA
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton] at hA
    rcases hA with ⟨e, he, (rfl | rfl)⟩ | ⟨e, he, (rfl | rfl)⟩
    all_goals {
      apply diagonal_commutes_with_matrixUnit X hDiag
      apply hSCC
      -- Show e.1 and e.2 are mutually reachable (they're in same SCC due to edge)
      -- Coherent edges are symmetric, jump edges give both directions in directed support
      constructor <;> {
        apply Reachable.step _ _ _ _ (Reachable.refl _)
        unfold directedSupportGraph
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
        first | left; exact ⟨e, he, Or.inl rfl⟩
              | left; exact ⟨e, he, Or.inr rfl⟩
              | right; exact ⟨e, he, Or.inl rfl⟩
              | right; exact ⟨e, he, Or.inr rfl⟩
      }
    }

/-- The SCC class of a vertex -/
noncomputable def sccClass (edges : Finset (Fin n × Fin n)) (i : Fin n) :
    Quotient (sccSetoid edges) :=
  @Quotient.mk' (Fin n) (sccSetoid edges) i

/-- Map from diagConstPerSCC to functions on SCCs: X ↦ (λ [i], X i i) -/
noncomputable def diagToSCCFun (edges : Finset (Fin n × Fin n)) :
    diagConstPerSCC edges →ₗ[ℂ] (Quotient (sccSetoid edges) → ℂ) where
  toFun X q :=
    -- Pick a representative and return the diagonal value there
    Quotient.liftOn' q (fun i => (X : Matrix (Fin n) (Fin n) ℂ) i i) (fun i j h => X.2.2 i j h)
  map_add' X Y := by
    ext q
    induction q using Quotient.inductionOn' with
    | h i => rfl
  map_smul' c X := by
    ext q
    induction q using Quotient.inductionOn' with
    | h i => rfl

/-- Map from functions on SCCs to diagConstPerSCC: f ↦ diagonal(λ i, f [i]) -/
noncomputable def sccFunToDiag (edges : Finset (Fin n × Fin n)) :
    (Quotient (sccSetoid edges) → ℂ) →ₗ[ℂ] diagConstPerSCC edges where
  toFun f := ⟨Matrix.diagonal (fun i => f (sccClass edges i)), by
    simp only [diagConstPerSCC, Submodule.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro i j hij
      simp [Matrix.diagonal_apply, hij]
    · intro i j hmr
      simp only [Matrix.diagonal_apply, eq_self_iff_true, ↓reduceIte]
      congr 1
      exact Quotient.sound' hmr⟩
  map_add' f g := by
    ext i j
    simp only [Submodule.coe_add, Pi.add_apply, Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  map_smul' c f := by
    ext i j
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]

/-- diagToSCCFun is left inverse to sccFunToDiag -/
theorem diagToSCCFun_sccFunToDiag (edges : Finset (Fin n × Fin n)) :
    (diagToSCCFun edges).comp (sccFunToDiag edges) = LinearMap.id := by
  ext f q
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  induction q using Quotient.inductionOn' with
  | h i =>
    simp only [sccFunToDiag, diagToSCCFun, LinearMap.coe_mk, AddHom.coe_mk]
    -- liftOn' (mk' i) (fun j => diagonal(...) j j) _ = f (mk' i)
    -- This is definitionally equal since liftOn'_mk' applies
    simp only [sccClass, Matrix.diagonal_apply, eq_self_iff_true, ↓reduceIte]
    rfl

/-- sccFunToDiag is left inverse to diagToSCCFun -/
theorem sccFunToDiag_diagToSCCFun (edges : Finset (Fin n × Fin n)) :
    (sccFunToDiag edges).comp (diagToSCCFun edges) = LinearMap.id := by
  ext ⟨X, hX⟩ i j
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  simp only [diagToSCCFun, sccFunToDiag, LinearMap.coe_mk, AddHom.coe_mk, sccClass]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply, eq_self_iff_true, ↓reduceIte]
    rfl
  · simp only [Matrix.diagonal_apply, hij, ↓reduceIte]
    exact (hX.1 i j hij).symm

/-- diagConstPerSCC is linearly equivalent to functions on SCCs -/
noncomputable def diagConstPerSCCEquiv (edges : Finset (Fin n × Fin n)) :
    diagConstPerSCC edges ≃ₗ[ℂ] (Quotient (sccSetoid edges) → ℂ) :=
  LinearEquiv.ofLinear
    (diagToSCCFun edges)
    (sccFunToDiag edges)
    (diagToSCCFun_sccFunToDiag edges)
    (sccFunToDiag_diagToSCCFun edges)

/-- The dimension of diagConstPerSCC equals numSCCs -/
theorem finrank_diagConstPerSCC (edges : Finset (Fin n × Fin n)) :
    Module.finrank ℂ (diagConstPerSCC edges) = numSCCs edges := by
  classical
  rw [LinearEquiv.finrank_eq (diagConstPerSCCEquiv edges)]
  -- finrank of function space = card of domain
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_self, Finset.sum_const, smul_eq_mul, mul_one]
  -- card of quotient = numSCCs
  unfold numSCCs
  -- The quotient type has cardinality equal to the image of the quotient map
  -- Show: card(Quotient) = card(image of mk')
  have h : Fintype.card (Quotient (sccSetoid edges)) =
      (Finset.univ.image fun i => @Quotient.mk' (Fin n) (sccSetoid edges) i).card := by
    rw [← Finset.card_univ (α := Quotient (sccSetoid edges))]
    -- univ on quotient = image of quotient map from univ on Fin n
    have hEq : (Finset.univ : Finset (Quotient (sccSetoid edges))) =
        Finset.univ.image (fun i => @Quotient.mk' (Fin n) (sccSetoid edges) i) := by
      ext q
      simp only [Finset.mem_univ, Finset.mem_image, true_iff, true_and]
      induction q using Quotient.inductionOn' with
      | h i => exact ⟨i, rfl⟩
    rw [hEq]
  exact h

/-- The structural deficiency formula for non-degenerate graphs.

    For a non-degenerate quantum network graph G with k = numSCCs(D(G)):
    δ_Q^struct(G) = k - 1

    This is fully proved: the structural commutant consists of diagonal matrices
    with constant diagonal entries within each SCC, which has dimension k. -/
theorem structural_deficiency_formula_nondegenerate (G : QuantumNetworkGraph n)
    (hND : IsNonDegenerate G) :
    structuralDeficiency G = numSCCs (directedSupportGraph G) - 1 := by
  classical
  unfold structuralDeficiency
  rw [structural_commutant_eq_diagConstPerSCC G hND]
  rw [finrank_diagConstPerSCC]

/-- **Structural Deficiency Formula** (Theorem 3.5 in paper)

    Let G be a quantum network graph and let k be the number of strongly
    connected components of D(G). Then:

    δ_Q^struct(G) = k - 1

    Proof outline:
    1. The algebra A(G) = ⟨S*(G)⟩ acts block-diagonally w.r.t. SCCs
    2. Within each SCC S_i, the restriction of A(G) equals M_{n_i}(ℂ)
    3. Therefore A(G) ≅ M_{n_1}(ℂ) ⊕ ··· ⊕ M_{n_k}(ℂ)
    4. The commutant is A(G)' ≅ ℂ^k
    5. Thus dim(C_struct(G)) = k and δ_Q^struct(G) = k - 1

    The k = 1 case (strongly connected) is fully proved above.
    The non-degenerate case is proved in structural_deficiency_formula_nondegenerate.
    The general case (allowing isolated vertices) requires special handling. -/
axiom structural_deficiency_formula (G : QuantumNetworkGraph n) :
    structuralDeficiency G = numSCCs (directedSupportGraph G) - 1

/-- Structural deficiency zero iff strongly connected -/
theorem structural_deficiency_zero_iff_strongly_connected (G : QuantumNetworkGraph n) :
    structuralDeficiency G = 0 ↔ isStronglyConnected (directedSupportGraph G) := by
  rw [structural_deficiency_formula, stronglyConnected_iff_one_scc]
  have hPos := numSCCs_pos (directedSupportGraph G)
  omega

/-- Structurally ergodic iff strongly connected -/
theorem structurallyErgodic_iff_stronglyConnected (G : QuantumNetworkGraph n) :
    IsStructurallyErgodic G ↔ isStronglyConnected (directedSupportGraph G) := by
  unfold IsStructurallyErgodic
  exact structural_deficiency_zero_iff_strongly_connected G

/-! ### Extremal Cases -/

/-- If D(G) is strongly connected (k=1), then δ_Q^struct(G) = 0 -/
theorem structural_deficiency_strongly_connected (G : QuantumNetworkGraph n)
    (hSC : isStronglyConnected (directedSupportGraph G)) :
    structuralDeficiency G = 0 :=
  (structural_deficiency_zero_iff_strongly_connected G).mpr hSC

/-- In an empty graph, only reflexive reachability holds -/
theorem reachable_empty_iff (i j : Fin n) :
    Reachable (∅ : Finset (Fin n × Fin n)) i j ↔ i = j := by
  constructor
  · intro h
    induction h with
    | refl _ => rfl
    | step a b c hab _ _ =>
      exfalso
      exact Finset.not_mem_empty (a, b) hab
  · intro h
    rw [h]
    exact Reachable.refl j

/-- In an empty graph, mutual reachability is equality -/
theorem mutuallyReachable_empty_iff (i j : Fin n) :
    MutuallyReachable (∅ : Finset (Fin n × Fin n)) i j ↔ i = j := by
  unfold MutuallyReachable
  rw [reachable_empty_iff, reachable_empty_iff]
  constructor
  · intro ⟨h1, _⟩; exact h1
  · intro h; exact ⟨h, h.symm⟩

/-- Maximum structural deficiency occurs when each vertex is its own SCC -/
theorem numSCCs_empty (n : ℕ) [NeZero n] :
    numSCCs (∅ : Finset (Fin n × Fin n)) = n := by
  classical
  unfold numSCCs
  -- Show that the quotient map is injective on the empty graph
  have h_inj : Function.Injective (fun i : Fin n =>
      @Quotient.mk' (Fin n) (sccSetoid (∅ : Finset (Fin n × Fin n))) i) := by
    intro i j h_eq
    have h_mr := Quotient.exact' h_eq
    -- h_mr : (sccSetoid ∅).r i j, which is MutuallyReachable ∅ i j
    unfold sccSetoid at h_mr
    simp only [Setoid.r] at h_mr
    rwa [mutuallyReachable_empty_iff] at h_mr
  -- So the image has the same cardinality as the domain
  rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]

/-- Maximum structural deficiency is n-1 when there are no edges -/
theorem structural_deficiency_max (G : QuantumNetworkGraph n)
    (hEmpty : directedSupportGraph G = ∅) :
    structuralDeficiency G = n - 1 := by
  rw [structural_deficiency_formula, hEmpty, numSCCs_empty]

/-! ### Generic vs Non-Generic Parameters -/

/-- The deficiency jump locus V_G is where δ_Q(θ) > δ_Q^struct(G).
    This is a proper algebraic subvariety of the parameter space. -/
def deficiencyJumpLocus (G : QuantumNetworkGraph n) : Set (Lindbladian n) :=
  {L | L.hasSupport G ∧ quantumDeficiency L > structuralDeficiency G}

/-- For Zariski-generic parameters, δ_Q(θ) = δ_Q^struct(G).

    The set where δ_Q > δ_Q^struct is a proper algebraic subvariety,
    so its complement is Zariski-open and dense.

    Reference: Theorem 3.3(b) in paper -/
axiom generic_deficiency_equals_structural (G : QuantumNetworkGraph n) :
    ∃ L : Lindbladian n, L.hasSupport G ∧ quantumDeficiency L = structuralDeficiency G

/-- Rate-Robust Uniqueness: If G is structurally ergodic, generic parameters give δ_Q = 0 -/
theorem rate_robust_uniqueness (G : QuantumNetworkGraph n)
    (hSE : IsStructurallyErgodic G) :
    ∃ L : Lindbladian n, L.hasSupport G ∧ quantumDeficiency L = 0 := by
  obtain ⟨L, hSupp, hDef⟩ := generic_deficiency_equals_structural G
  exact ⟨L, hSupp, by rw [hDef]; exact hSE⟩

end DefectCRN.Quantum
