import Mathlib

/-!
# Identifiability of directed-cycle and catenary linear compartmental models

Authors: Saber Ahmed, Natasha Crepeau, Paul R. Dessauer Jr., Alexis Edozie,
Odalys Garcia-Lopez, Tanisha Grimsley, Jordy Lopez Garcia, Viridiana Neri, and Anne Shiu.
Origin: [MSRI-UP 2022](https://people.tamu.edu/~annejls/).
Reference: S. Ahmed, N. Crepeau, P. R. Dessauer Jr., A. Edozie, O. Garcia-Lopez, T. Grimsley,
J. Lopez Garcia, V. Neri, and A. Shiu, *Identifiability of directed-cycle and catenary linear
compartmental models*, preprint (2025); arXiv:2412.05283v3.
-/

noncomputable section

namespace Ahmed2026Identifiability

open MeasureTheory Topology

/-- The parameters of the model: one per cycle edge and one per leak (Definition 2.1). Lean
vertex `i` labels source compartment `i.val + 1`. -/
abbrev ParameterIndex {n : ℕ} (leaks : Finset (Fin n)) :=
  Fin n ⊕ {i : Fin n // i ∈ leaks}

/-- The compartmental matrix for the directed cycle and its leaks (Definition 2.6). -/
def compartmentalMatrix {n : ℕ} (leaks : Finset (Fin n))
    (k : ParameterIndex leaks → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if i = j then -(k (Sum.inl j) + if h : j ∈ leaks then k (Sum.inr ⟨j, h⟩) else 0)
    else if i = finRotate n j then k (Sum.inl j) else 0

/-- The coefficient map for the given input and output `p`, via the adjugate entry for the
signed minor in (3) (Section 2.2). Constant coordinates are retained, as Remark 2.12 permits. -/
def coefficientMap {n : ℕ} (leaks : Finset (Fin n)) (input p : Fin n)
    (k : ParameterIndex leaks → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  let B := (compartmentalMatrix leaks k).charmatrix
  (fun d ↦ B.det.coeff d.val, fun d ↦ (B.adjugate p input).coeff d.val)

/-- **Conjecture 4.6**. For every identifiable directed-cycle model with input in compartment one
and one output, each specified equality between a leaking rate and an earlier nonleaking rate
defines a hyperplane in the singular locus (Definition 4.1). -/
theorem conjecture_4_6 {n : ℕ} (hn : 3 ≤ n) (leaks : Finset (Fin n)) (p : Fin n)
    (hidentifiable : ∀ᵐ k : ParameterIndex leaks → ℝ ∂volume,
      ∃ U : Set (ParameterIndex leaks → ℝ), U ∈ 𝓝 k ∧
        Set.InjOn (coefficientMap leaks ⟨0, by omega⟩ p) U)
    (a ℓ : Fin n) (ha : a < p) (hanot : a ∉ leaks)
    (hℓ : ℓ ∈ leaks) (hℓp : ℓ ≤ p)
    (k : ParameterIndex leaks → ℝ)
    (hplane : k (Sum.inl ℓ) + k (Sum.inr ⟨ℓ, hℓ⟩) = k (Sum.inl a)) :
    ¬Function.Injective (fderiv ℝ (coefficientMap leaks ⟨0, by omega⟩ p) k) := by
  sorry

end Ahmed2026Identifiability
