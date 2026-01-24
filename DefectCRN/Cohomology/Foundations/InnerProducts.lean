/-
Copyright (c) 2025 Paolo Vella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paolo Vella
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.InnerProductSpace.Basic
import DefectCRN.Basic

set_option linter.unusedSectionVars false

/-!
# Inner Products for Chemical Reaction Networks

This file defines the correct inner product structures for CRN theory,
fixing the Hodge orthogonality issue.

## Key Insight

Under ⟨x,y⟩_{W⁻¹} = ∑ᵢ xᵢyᵢ/Wᵢ:
  Orthogonal complement of im(B^T) is ker(B·W⁻¹), NOT ker(B·W)

Under ⟨x,y⟩_W = ∑ᵢ Wᵢxᵢyᵢ:
  Orthogonal complement of im(B^T) is ker(B)

## Main Definitions

* `innerW` - W-weighted inner product: ⟨x,y⟩_W = ∑ᵢ Wᵢxᵢyᵢ
* `innerWinv` - W⁻¹-weighted inner product: ⟨x,y⟩_{W⁻¹} = ∑ᵢ xᵢyᵢ/Wᵢ
-/

namespace DefectCRN.Cohomology.Foundations

open Finset BigOperators Matrix

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
variable [DecidableEq V] [DecidableEq E] [DecidableEq S]

/-! ## Inner Product Definitions -/

/-- W-weighted inner product on E → ℝ: ⟨x,y⟩_W = ∑ᵢ Wᵢxᵢyᵢ -/
noncomputable def innerW (W : E → ℝ) (x y : E → ℝ) : ℝ :=
  ∑ e : E, W e * x e * y e

/-- W⁻¹-weighted inner product on E → ℝ: ⟨x,y⟩_{W⁻¹} = ∑ᵢ xᵢyᵢ/Wᵢ -/
noncomputable def innerWinv (W : E → ℝ) (x y : E → ℝ) : ℝ :=
  ∑ e : E, x e * y e / W e

/-! ## Basic Properties -/

/-- innerW is symmetric -/
theorem innerW_comm (W : E → ℝ) (x y : E → ℝ) : innerW W x y = innerW W y x := by
  unfold innerW
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- innerWinv is symmetric -/
theorem innerWinv_comm (W : E → ℝ) (x y : E → ℝ) : innerWinv W x y = innerWinv W y x := by
  unfold innerWinv
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- innerW is bilinear in first argument -/
theorem innerW_add_left (W : E → ℝ) (x₁ x₂ y : E → ℝ) :
    innerW W (x₁ + x₂) y = innerW W x₁ y + innerW W x₂ y := by
  unfold innerW
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- innerW is bilinear in second argument -/
theorem innerW_add_right (W : E → ℝ) (x y₁ y₂ : E → ℝ) :
    innerW W x (y₁ + y₂) = innerW W x y₁ + innerW W x y₂ := by
  unfold innerW
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- innerW scalar multiplication -/
theorem innerW_smul_left (W : E → ℝ) (c : ℝ) (x y : E → ℝ) :
    innerW W (c • x) y = c * innerW W x y := by
  unfold innerW
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- innerW is non-negative when W > 0 -/
theorem innerW_nonneg (W : E → ℝ) (hW : ∀ e, W e > 0) (x : E → ℝ) :
    innerW W x x ≥ 0 := by
  unfold innerW
  apply Finset.sum_nonneg
  intro e _
  have hWe : W e > 0 := hW e
  have hsq : x e * x e ≥ 0 := mul_self_nonneg (x e)
  nlinarith

/-- innerW of zero is zero -/
theorem innerW_zero_left (W : E → ℝ) (y : E → ℝ) : innerW W 0 y = 0 := by
  unfold innerW
  simp only [Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

/-- innerW of zero is zero -/
theorem innerW_zero_right (W : E → ℝ) (x : E → ℝ) : innerW W x 0 = 0 := by
  unfold innerW
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-! ## Orthogonal Complements -/

/-- The image of B^T as a set -/
def rangeOfBt (B : Matrix V E ℝ) : Set (E → ℝ) :=
  {y | ∃ φ : V → ℝ, ∀ e, y e = ∑ v, B v e * φ v}

/-- The kernel of B -/
def kerOfB (B : Matrix V E ℝ) : Set (E → ℝ) :=
  {y | ∀ v, ∑ e, B v e * y e = 0}

/-- The kernel of B · diag(W⁻¹) -/
def kerOfBWinv (B : Matrix V E ℝ) (W : E → ℝ) : Set (E → ℝ) :=
  {y | ∀ v, ∑ e, B v e * (y e / W e) = 0}

/-- Zero is in the kernel of B -/
theorem zero_in_kerOfB (B : Matrix V E ℝ) : (0 : E → ℝ) ∈ kerOfB B := by
  intro v
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Zero is in the kernel of B·W⁻¹ -/
theorem zero_in_kerOfBWinv (B : Matrix V E ℝ) (W : E → ℝ) : (0 : E → ℝ) ∈ kerOfBWinv B W := by
  intro v
  simp only [Pi.zero_apply, zero_div, mul_zero, Finset.sum_const_zero]

/-- kerOfB is closed under addition -/
theorem kerOfB_add (B : Matrix V E ℝ) (x y : E → ℝ)
    (hx : x ∈ kerOfB B) (hy : y ∈ kerOfB B) : x + y ∈ kerOfB B := by
  intro v
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hx v, hy v, add_zero]

/-- kerOfB is closed under scalar multiplication -/
theorem kerOfB_smul (B : Matrix V E ℝ) (c : ℝ) (x : E → ℝ)
    (hx : x ∈ kerOfB B) : c • x ∈ kerOfB B := by
  intro v
  simp only [Pi.smul_apply, smul_eq_mul]
  calc ∑ e : E, B v e * (c * x e)
      = ∑ e : E, c * (B v e * x e) := by
          apply Finset.sum_congr rfl; intro e _; ring
    _ = c * ∑ e : E, B v e * x e := by rw [Finset.mul_sum]
    _ = c * 0 := by rw [hx v]
    _ = 0 := by ring

/-! ## Key Insight: Different Orthogonal Complements

The CRITICAL observation is that under the W⁻¹ inner product,
the orthogonal complement of im(B^T) is ker(B·diag(W⁻¹)), NOT ker(B).

This means:
- Under ⟨·,·⟩_W: (im B^T)^⊥ = ker(B)
- Under ⟨·,·⟩_{W⁻¹}: (im B^T)^⊥ = ker(B·W⁻¹)

For CRN theory with Onsager-Rayleigh, we use W⁻¹ inner product,
so the "cycle space" is ker(B·W⁻¹), not ker(B).
-/

/-- The orthogonal complement of im(B^T) under W⁻¹ inner product
    equals ker(B·W⁻¹). This is proven by direct calculation. -/
theorem innerWinv_orthogonal_complement_imBt
    (B : Matrix V E ℝ) (W : E → ℝ) (hW : ∀ e, W e > 0) (y : E → ℝ) :
    (∀ x ∈ rangeOfBt B, innerWinv W y x = 0) ↔ y ∈ kerOfBWinv B W := by
  constructor
  · intro horth v
    -- Test with x = B^T · δ_v (standard basis vector at v)
    let δ : V → ℝ := fun w => if w = v then 1 else 0
    have hδ_in : (fun e => ∑ w, B w e * δ w) ∈ rangeOfBt B := ⟨δ, fun _ => rfl⟩
    specialize horth _ hδ_in
    unfold innerWinv at horth
    -- Simplify: ∑ w, B w e * δ w = B v e
    have hsimpl : ∀ e, (∑ w : V, B w e * δ w) = B v e := by
      intro e
      have h1 : ∑ w : V, B w e * δ w = ∑ w : V, B w e * (if w = v then 1 else 0) := rfl
      rw [h1]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    -- horth : ∑ e, y e * (∑ w, B w e * δ w) / W e = 0
    -- After simplification: ∑ e, y e * B v e / W e = 0
    -- We need: ∑ e, B v e * (y e / W e) = 0
    have horth' : ∑ e : E, y e * B v e / W e = 0 := by
      have heq : ∑ e : E, y e * B v e / W e = ∑ e : E, y e * (∑ w : V, B w e * δ w) / W e := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hsimpl e]
      rw [heq]
      exact horth
    calc ∑ e : E, B v e * (y e / W e)
        = ∑ e : E, y e * B v e / W e := by
            apply Finset.sum_congr rfl; intro e _; ring
      _ = 0 := horth'
  · intro hker x ⟨φ, hφ⟩
    unfold innerWinv
    calc ∑ e : E, y e * x e / W e
        = ∑ e : E, y e * (∑ v, B v e * φ v) / W e := by
            apply Finset.sum_congr rfl; intro e _; rw [hφ e]
      _ = ∑ e : E, ∑ v, (y e / W e) * B v e * φ v := by
            apply Finset.sum_congr rfl; intro e _
            have hWe : W e ≠ 0 := ne_of_gt (hW e)
            calc y e * (∑ v, B v e * φ v) / W e
                = (∑ v, B v e * φ v) * (y e / W e) := by ring
              _ = ∑ v, B v e * φ v * (y e / W e) := by rw [Finset.sum_mul]
              _ = ∑ v, (y e / W e) * B v e * φ v := by
                    apply Finset.sum_congr rfl; intro v _; ring
      _ = ∑ v, ∑ e, (y e / W e) * B v e * φ v := Finset.sum_comm
      _ = ∑ v, (∑ e, B v e * (y e / W e)) * φ v := by
            apply Finset.sum_congr rfl; intro v _
            calc ∑ e : E, (y e / W e) * B v e * φ v
                = ∑ e : E, B v e * (y e / W e) * φ v := by
                    apply Finset.sum_congr rfl; intro e _; ring
              _ = (∑ e : E, B v e * (y e / W e)) * φ v := by rw [Finset.sum_mul]
      _ = ∑ v, 0 * φ v := by
            apply Finset.sum_congr rfl; intro v _
            rw [hker v, zero_mul]
      _ = 0 := by simp only [zero_mul, Finset.sum_const_zero]

end DefectCRN.Cohomology.Foundations
