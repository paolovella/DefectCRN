# The Classification Problem for Quantum Markov Semigroups

## 1. The Central Question

**What does it mean to classify finite-dimensional quantum Markov semigroups?**

This document establishes the precise mathematical framework for the classification
project, fixing definitions and goals before any computation.

---

## 2. Equivalence Relations

### 2.1 GKSL Gauge Equivalence

**Definition (GKSL Gauge):** Two Lindbladian representations (H, {Lₖ}) and (H', {L'ⱼ})
are *GKSL gauge equivalent* if they generate the same superoperator:

```
L_{H,{Lₖ}}(ρ) = L_{H',{L'ⱼ}}(ρ)  for all ρ
```

**Characterization (Lindblad-GKS):** This holds iff:
- H' = H + c·I + (1/2i) Σₖ (aₖ* Lₖ - aₖ Lₖ†)  for some real c, complex {aₖ}
- L'ⱼ = Σₖ Uⱼₖ Lₖ + bⱼ·I  for some unitary U, complex {bⱼ}

**Status:** We have axiomatized this as `gksl_gauge_freedom_of_equiv` in Lean.

### 2.2 Unitary Conjugacy

**Definition (Unitary Conjugacy):** Two Lindbladians L₁, L₂ on M_n(ℂ) are
*unitarily conjugate* if there exists U ∈ U(n) such that:

```
L₂(ρ) = U L₁(U† ρ U) U†  for all ρ
```

Equivalently: (H₂, {L₂ₖ}) = (U H₁ U†, {U L₁ₖ U†})

### 2.3 Combined Equivalence

**Definition (Full Equivalence):** L₁ ~ L₂ iff there exists:
- A unitary U ∈ U(n)
- A GKSL gauge transformation

such that the composed transformation maps L₁ to L₂.

**Our Choice:** We work with **Full Equivalence** as the primary relation,
but track GKSL gauge invariance separately for invariants.

---

## 3. The Classification Goal

### 3.1 Ideal Goal (Complete Invariants)

**Definition (Complete Invariants):** A collection of invariants I₁, I₂, ..., Iₘ
is *complete* for equivalence relation ~ if:

```
L₁ ~ L₂  ⟺  Iₖ(L₁) = Iₖ(L₂) for all k
```

### 3.2 Realistic Goal (Partial Classification)

Given the complexity of QMS, we aim for:

1. **Sufficient invariants** in a restricted regime
2. **Separation examples** showing invariants are non-redundant
3. **Classical reduction** showing our invariants generalize classical deficiency

### 3.3 The Invariants We Seek

| Invariant | Definition | Captures |
|-----------|------------|----------|
| Type(L) | Wedderburn signature of A_int | Block structure |
| δ_cen | dim Z(A_int) - 1 | "Block deficiency" |
| Phase(L) | Peripheral spectrum structure | Oscillatory dynamics |
| r_? | Rank term (TBD) | "Constraint deficiency" |

---

## 4. The Chosen Regime

### 4.1 Primary Regime: σ-Detailed Balance

**Definition (σ-Detailed Balance):** L satisfies σ-DB if there exists a
faithful state σ > 0 such that:

```
⟨A, L*(B)⟩_σ = ⟨L*(A), B⟩_σ
```

where ⟨A, B⟩_σ := Tr(σ^{1/2} A† σ^{1/2} B) is the GNS inner product.

**Why this regime:**
- Self-adjoint L* gives real spectrum
- Spectral gap exists under mild conditions
- Dirichlet form is well-defined (enables rank term)
- Classical Markov chains satisfy this (enables classical reduction)
- Cleanest mathematical structure

### 4.2 Secondary Regime: Faithful Stationary State

**Definition:** L has a faithful stationary state if ∃σ > 0 with L(σ) = 0.

**Properties:**
- Evans-Høegh-Krohn: commutantSubmodule = dualStationarySubspace
- Wedderburn structure theorem applies to A_int

### 4.3 Tertiary Regime: Primitive (Ergodic)

**Definition:** L is primitive (ergodic) iff:
- dim(ker L) = 1 (unique stationary state)
- equivalently: δ_Q = 0

**Properties:**
- Trivial commutant (= ℂ·I)
- Simplest case for classification

---

## 5. The Classification Conjecture

### 5.1 Statement (σ-Detailed Balance Regime)

**Conjecture:** Let L₁, L₂ be two Lindbladians on M_n(ℂ), both satisfying
σ-detailed balance for the same faithful state σ. Then:

```
L₁ ~ L₂  ⟺  (Type(L₁), Phase(L₁), r(L₁)) = (Type(L₂), Phase(L₂), r(L₂))
```

where r is the rank invariant (to be determined).

### 5.2 Subconjectures

**A. Type determines block structure:**
```
Type(L₁) = Type(L₂)  ⟺  A_int(L₁) ≅ A_int(L₂) as *-algebras
```

**B. Phase captures oscillations:**
```
Phase(L₁) = Phase(L₂)  ⟺  Spec_per(L₁) has same group structure as Spec_per(L₂)
```

**C. Rank determines constraints:**
```
r(L₁) = r(L₂)  ⟺  [some condition on dissipator structure]
```

---

## 6. Classical Reduction Requirement

### 6.1 Classical Embedding

A classical Markov chain on states {1, ..., n} with generator Q = (qᵢⱼ) embeds as:

```
H = 0
Lᵢⱼ = √qᵢⱼ |j⟩⟨i|  for i ≠ j with qᵢⱼ > 0
```

The Lindbladian acts on diagonal matrices (populations) by:
```
L(diag(p))_ii = Σⱼ qⱼᵢ pⱼ - (Σⱼ qᵢⱼ) pᵢ = (Qᵀp)ᵢ
```

### 6.2 Classical Deficiency

For a classical CRN with:
- n species
- ℓ linkage classes (connected components)
- S = stoichiometric matrix

The classical deficiency is:
```
δ_classical = n - ℓ - rank(S)
```

### 6.3 Reduction Theorem (Goal)

**Goal Theorem:** For classical Markov chains embedded as QMS:
```
δ_cen = ℓ - 1  (number of components minus 1)
r(L) = f(rank(S))  for some function f
δ_Q^{new} := δ_cen + g(r) = classical formula (appropriately translated)
```

---

## 7. Success Criteria

### 7.1 Minimum Publishable Unit

1. ✅ Basis-invariant block layer (A_int, δ_cen) - DONE IN LEAN
2. ⬜ Wedderburn type as computable invariant
3. ⬜ Clear classical reduction for δ_cen
4. ⬜ At least one separation example (same δ_Q, different Type)

### 7.2 Full Success

All of above, plus:
5. ⬜ Rank term r with classical reduction
6. ⬜ Classification theorem in σ-DB regime
7. ⬜ Lean formalization of classification

### 7.3 Negative Result (Still Publishable)

If no rank term exists:
- Prove obstruction theorem
- Characterize what classification is possible
- Show quantum deficiency is fundamentally different from classical

---

## 8. Key Open Questions

### Q1. Does δ_cen = δ_struct always?
- If yes: our work simplifies existing theory
- If no: find explicit counterexample, understand gap

### Q2. What is the right rank term?
- Candidate A: dim(Im(D*)) where D* = dissipative part of L*
- Candidate B: rank of Dirichlet form (requires σ-DB)
- Candidate C: codimension of constraints

### Q3. Is Type(L) a complete invariant for A_int?
- Does Type(L₁) = Type(L₂) imply A_int(L₁) ≅ A_int(L₂)?
- Or are there hidden invariants?

### Q4. What is the peripheral spectrum structure?
- Is G_per always a finite group? A finitely generated abelian group?
- How does it relate to symmetries?

---

## 9. Notation Summary

| Symbol | Definition |
|--------|------------|
| L | Lindbladian superoperator |
| (H, {Lₖ}) | GKSL representation |
| A_int | Interaction algebra Alg*(H, L₁, ..., Lₘ) |
| Z(A_int) | Center of interaction algebra |
| δ_cen | dim Z(A_int) - 1 |
| δ_Q | dim(ker L) - 1 (quantum deficiency) |
| Type(L) | Wedderburn type signature {(dₐ, mₐ)} |
| Phase(L) | Peripheral spectrum group structure |
| Spec_per(L) | {λ : Re(λ) = 0} ∩ Spec(L) |
| A_∞ | Asymptotic algebra (peripheral eigenspaces) |
| σ-DB | σ-detailed balance condition |

---

## 10. Next Steps

1. **Phase 0.2:** Set up Python computation environment
2. **Phase 0.3:** Build test case library with explicit (H, {Lₖ})
3. **Phase 1.1:** Implement A_int computation algorithm
4. **Phase 1.3:** Compare δ_cen vs δ_struct on all test cases

**Critical decision point:** End of Phase 3 - does rank term exist?
