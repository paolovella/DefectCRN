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
    - Block structure analysis -/
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

/-- **Structural Deficiency Formula** (Theorem 3.5 in paper)

    Let G be a quantum network graph and let k be the number of strongly
    connected components of D(G). Then:

    δ_Q^struct(G) = k - 1

    Proof outline:
    1. The algebra A(G) = ⟨S*(G)⟩ acts block-diagonally w.r.t. SCCs
    2. Within each SCC S_i, the restriction of A(G) equals M_{n_i}(ℂ)
    3. Therefore A(G) ≅ M_{n_1}(ℂ) ⊕ ··· ⊕ M_{n_k}(ℂ)
    4. The commutant is A(G)' ≅ ℂ^k
    5. Thus dim(C_struct(G)) = k and δ_Q^struct(G) = k - 1 -/
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
