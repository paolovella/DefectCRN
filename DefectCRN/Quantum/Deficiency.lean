/-
Copyright (c) 2026 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Quantum.Irreducibility
import DefectCRN.Quantum.StationaryState

/-!
# Quantum Deficiency

The quantum analog of classical CRN deficiency.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace DefectCRN.Quantum

open scoped Matrix BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

/-- Quantum deficiency: one less than the dimension of the stationary state space -/
noncomputable def quantumDeficiency (L : Lindbladian n) : ℕ :=
  Module.finrank ℂ L.stationarySubspace - 1

/-- δ_Q = 0 iff stationary space is 1-dimensional (assuming finrank ≥ 1) -/
theorem deficiency_zero_iff_stationary_dim_one (L : Lindbladian n)
    (hPos : Module.finrank ℂ L.stationarySubspace ≥ 1 := by
      -- This follows from existence of stationary states
      -- Every Lindbladian has at least one stationary state
      omega) :
    quantumDeficiency L = 0 ↔ Module.finrank ℂ L.stationarySubspace = 1 := by
  unfold quantumDeficiency
  constructor
  · intro h
    -- If finrank - 1 = 0 and finrank ≥ 1, then finrank = 1
    omega
  · intro h
    simp only [h, Nat.sub_self]

/-- δ_Q = 0 implies primitive.
    The proof uses the fundamental result that dim(commutant) = dim(stationary subspace).
    If stationary subspace is 1-dimensional, commutant is 1-dimensional, hence trivial. -/
theorem deficiency_zero_implies_primitive (L : Lindbladian n)
    (h : quantumDeficiency L = 0) : IsPrimitive L := by
  -- δ_Q = 0 means dim(stationary) = 1
  have hPos := stationary_subspace_nontrivial L
  have hDim : Module.finrank ℂ L.stationarySubspace = 1 := by
    unfold quantumDeficiency at h
    omega
  -- By the commutant-stationary dimension theorem, dim(commutant) = 1
  have hCommDim : Module.finrank ℂ (commutantSubmodule L) = 1 := by
    rw [commutant_dim_eq_stationary_dim L]
    exact hDim
  -- 1-dimensional commutant = trivial commutant (only scalars)
  exact commutant_dim_one_implies_trivial L hCommDim

/-- Primitive implies δ_Q = 0 -/
theorem primitive_implies_deficiency_zero (L : Lindbladian n)
    (h : IsPrimitive L) : quantumDeficiency L = 0 := by
  have hDim := primitive_stationary_dim_one L h
  unfold quantumDeficiency
  simp only [hDim, Nat.sub_self]

/-- δ_Q = 0 ⟺ primitive -/
theorem deficiency_zero_iff_primitive (L : Lindbladian n) :
    quantumDeficiency L = 0 ↔ IsPrimitive L :=
  ⟨deficiency_zero_implies_primitive L, primitive_implies_deficiency_zero L⟩

end DefectCRN.Quantum
