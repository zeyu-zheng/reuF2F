import Mathlib

/-!
# Parameter identifiability of linear-compartmental mammillary models

Authors: Katherine Clemens, Jonathan Martinez, Anne Shiu, Michaela Thompson,
and Benjamin Warren.
Origin: [Texas A&M University REU
2023](https://artsci.tamu.edu/mathematics/academics/undergraduate/research/reu/results/results-2023.html).
Reference: K. Clemens, J. Martinez, A. Shiu, M. Thompson, and B. Warren, *Parameter
identifiability of linear-compartmental mammillary models*, Bull. Math. Biol. **88** (2026),
article 12; arXiv:2506.21889v2.
-/

noncomputable section

namespace Clemens2026Parameter

open MeasureTheory

/-- Indices `(i, j)` for the rate from `j` to `i` in the leak-free star (Definitions 2.1-2.2
and (5)). Lean vertex `i` is source compartment `i.val + 1`. -/
abbrev ParameterIndex (n : ℕ) :=
  {ij : Fin n × Fin n //
    (ij.1.val = 0 ∧ ij.2.val ≠ 0) ∨ (ij.1.val ≠ 0 ∧ ij.2.val = 0)}

/-- The compartmental matrix of a leak-free mammillary model (Definition 2.3). -/
def compartmentalMatrix {n : ℕ} (k : ParameterIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if i = j then -∑ e : ParameterIndex n, if e.val.2 = j then k e else 0
    else if h : (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then
      k ⟨(i, j), h⟩
    else 0

/-- The coefficients of the input-output equation (3), using the adjugate entry
`(output, input)` for its signed minor (Section 2.2). Constant zero coordinates are retained;
they do not change any fiber. -/
def coefficientMap {n : ℕ} (input output : Fin n) (k : ParameterIndex n → ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let B := (compartmentalMatrix k).charmatrix
  (fun d ↦ B.det.coeff d.val, fun d ↦ (B.adjugate output input).coeff d.val)

/-- Almost every real parameter vector has a coefficient-map fiber whose projection onto the
specified parameter is finite (Definition 2.18(3)). -/
def GenericallyLocallyIdentifiable {n : ℕ} (input output : Fin n)
    (e : ParameterIndex n) : Prop :=
  ∀ᵐ k : ParameterIndex n → ℝ ∂volume,
    Set.Finite {v : ℝ | ∃ l : ParameterIndex n → ℝ,
      coefficientMap input output l = coefficientMap input output k ∧ l e = v}

/-- **Conjecture 3.18**. For every `n ≥ 5`, the parameters `k12`, `k13`, and every `ki1` of
`M_n(2,3)` are unidentifiable.

Definition 2.18 is used over all real rates, without positivity restrictions; unidentifiable is
the negation of generic local identifiability, not almost-everywhere infinite fibers. -/
theorem conjecture_3_18 {n : ℕ} (hn : 5 ≤ n) (e : ParameterIndex n)
    (he : e.val.2.val ≤ 2) :
    ¬GenericallyLocallyIdentifiable ⟨1, by omega⟩ ⟨2, by omega⟩ e := by
  sorry

end Clemens2026Parameter
