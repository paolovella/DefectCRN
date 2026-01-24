/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import DefectCRN.Cohomology.Foundations.InnerProducts

/-!
# Cochain Complex Structure for Graphs

This file defines the standard graph cochain complex structure, providing
the algebraic topology foundation for deficiency theory.

## Main Definitions

* `DirectedGraph` - A directed graph with source and target maps
* `coboundary0` - The coboundary map δ⁰ : C⁰(V) → C¹(E)
* `constantFunctions` - The space of constant functions (kernel of δ⁰ for connected graphs)

## Main Results

* `coboundary_constant_zero` - Constant functions are in ker(δ⁰)
-/

namespace DefectCRN.Cohomology.Foundations

open Finset BigOperators Matrix

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
variable [DecidableEq V] [DecidableEq E] [DecidableEq S]

set_option linter.unusedSectionVars false

/-! ## Directed Graph Structure -/

/-- A directed graph with vertex set V and edge set E -/
structure DirectedGraph (V E : Type*) where
  /-- The source vertex of each edge -/
  source : E → V
  /-- The target vertex of each edge -/
  target : E → V

/-! ## Coboundary Maps -/

/-- The coboundary map δ⁰ : C⁰(V) → C¹(E).
    For a function f : V → ℝ, (δ⁰f)(e) = f(target(e)) - f(source(e)). -/
def coboundary0 (G : DirectedGraph V E) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f := fun e => f (G.target e) - f (G.source e)
  map_add' f g := by
    ext e
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The kernel of δ⁰ for a connected graph is the constant functions -/
def constantFunctions (V : Type*) [Fintype V] : Submodule ℝ (V → ℝ) where
  carrier := {f | ∃ c : ℝ, ∀ v, f v = c}
  add_mem' := by
    intro f g ⟨cf, hf⟩ ⟨cg, hg⟩
    use cf + cg
    intro v
    simp only [Pi.add_apply, hf v, hg v]
  zero_mem' := by
    use 0
    intro v
    rfl
  smul_mem' := by
    intro r f ⟨c, hf⟩
    use r * c
    intro v
    simp only [Pi.smul_apply, smul_eq_mul, hf v]

/-- Constant functions are in the kernel of coboundary -/
theorem coboundary_constant_zero (G : DirectedGraph V E) (f : V → ℝ) (c : ℝ)
    (hf : ∀ v, f v = c) : coboundary0 G f = 0 := by
  ext e
  simp only [coboundary0, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  rw [hf (G.target e), hf (G.source e)]
  ring

/-! ## Connection to Incidence Matrix -/

/-- The incidence matrix B of a directed graph.
    B[v,e] = +1 if e ends at v, -1 if e starts at v, 0 otherwise. -/
def incidenceMatrix (G : DirectedGraph V E) : Matrix V E ℝ :=
  fun v e =>
    if v = G.target e then 1
    else if v = G.source e then -1
    else 0

/-! ## Kernel and Image Spaces -/

/-- The kernel of the coboundary map -/
def kerCoboundary0 (G : DirectedGraph V E) : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (coboundary0 G)

/-- The image of the coboundary map -/
def imCoboundary0 (G : DirectedGraph V E) : Submodule ℝ (E → ℝ) :=
  LinearMap.range (coboundary0 G)

/-- Constant functions are in ker(δ⁰) -/
theorem constant_in_ker_coboundary (G : DirectedGraph V E) :
    constantFunctions V ≤ kerCoboundary0 G := by
  intro f ⟨c, hf⟩
  simp only [kerCoboundary0, LinearMap.mem_ker]
  exact coboundary_constant_zero G f c hf

end DefectCRN.Cohomology.Foundations
