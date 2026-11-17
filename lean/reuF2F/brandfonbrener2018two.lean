import Mathlib

/-!
# Two-Vertex Generators of Jacobians of Graphs

Authors: David Brandfonbrener, Pat Devlin, Netanel Friedenberg, Yuxuan Ke,
Steffen Marcus, Henry Reichard, and Ethan Sciamma.
Origin: [Yale SUMRY 2017](https://sumry.yale.edu/pastprojects).
Reference: D. Brandfonbrener, P. Devlin, N. Friedenberg, Y. Ke, S. Marcus, H. Reichard, and
E. Sciamma, *Two-vertex generators of Jacobians of graphs*, arXiv:1708.03069.
-/

noncomputable section

namespace Brandfonbrener2018Two

open Filter
open scoped Topology NNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The subgroup `Div⁰(G)` of divisors with total coefficient zero (Section 2.1). -/
def degreeZeroDivisor (V : Type) [Fintype V] : AddSubgroup (V →₀ ℤ) :=
  (∑ v : V, Finsupp.applyAddHom v : (V →₀ ℤ) →+ ℤ).ker

open scoped Classical in
/-- The divisor produced by a firing script (Section 2.1). Mathlib's positive Laplacian has the
opposite sign to chip-firing, but the images generate the same subgroup. -/
def principalDivisor (G : SimpleGraph V) (f : V → ℤ) : V →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (-Matrix.mulVec (G.lapMatrix ℤ) f)

/-- The principal divisors, as a subgroup of `Div⁰(G)` (Section 2.1). -/
def principalSubgroup (G : SimpleGraph V) : AddSubgroup (degreeZeroDivisor V) :=
  (AddSubgroup.closure (Set.range (principalDivisor G))).comap (degreeZeroDivisor V).subtype

/-- The Jacobian `Jac(G) = Div⁰(G) / Prin(G)` (Section 2.1). -/
abbrev Jacobian (G : SimpleGraph V) :=
  degreeZeroDivisor V ⧸ principalSubgroup G

/-- The class `[δ_xy]`, represented by `-1` at `x` and `1` at `y`. -/
def deltaClass (G : SimpleGraph V) (x y : V) : Jacobian G :=
  QuotientAddGroup.mk
    (⟨Finsupp.single y (1 : ℤ) - Finsupp.single x (1 : ℤ), by
      simp [degreeZeroDivisor, Finset.sum_sub_distrib]⟩ : degreeZeroDivisor V)

/-- **Conjecture 6.1**. For fixed `p`, conditional on the Jacobian of `G(n,p)` being cyclic, a
fixed two-vertex class `[δ_xy]` generates the Jacobian with limiting probability `ζ(2)⁻¹`.

Here `0 < p < 1` is the contextual nondegenerate reading, finite cyclicity of the whole quotient
implements the connected-graph convention, and the conditional probability is a quotient of
labelled `G(n + 2, p)` probabilities with the fixed vertices `x, y : Fin 2`. -/
theorem conjecture_6_1_fixed_delta_generator_conditional_probability
    (p : ℝ≥0) (hp_pos : 0 < p) (hp_lt_one : (p : ℝ) < 1)
    (x y : Fin 2) (hxy : x ≠ y) :
    Tendsto
      (fun n : ℕ ↦
        (SimpleGraph.binomialRandom (Fin (n + 2))
            ⟨(p : ℝ), p.property, le_of_lt hp_lt_one⟩).real
          {G : SimpleGraph (Fin (n + 2)) |
            ∃ _hfin : Fintype (Jacobian G), IsAddCyclic (Jacobian G) ∧
              AddSubgroup.closure
                ({deltaClass G (⟨x.val, by omega⟩ : Fin (n + 2))
                  (⟨y.val, by omega⟩ : Fin (n + 2))} : Set (Jacobian G)) = ⊤} /
        (SimpleGraph.binomialRandom (Fin (n + 2))
            ⟨(p : ℝ), p.property, le_of_lt hp_lt_one⟩).real
          {G : SimpleGraph (Fin (n + 2)) |
            ∃ _hfin : Fintype (Jacobian G), IsAddCyclic (Jacobian G)})
      atTop (𝓝 ((riemannZeta (2 : ℂ))⁻¹.re)) := by
  sorry

end Brandfonbrener2018Two
