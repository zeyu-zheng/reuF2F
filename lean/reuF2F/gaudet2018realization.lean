import Mathlib

/-!
# Realization of Groups with Pairing as Jacobians of Finite Graphs

Authors: Louis Gaudet, David Jensen, Dhruv Ranganathan, Nicholas Wawrykow,
and Theodore Weisman.
Origin: [Yale SUMRY 2014](https://sumry.yale.edu/past-projects).
Reference: L. Gaudet, D. Jensen, D. Ranganathan, N. Wawrykow, and T. Weisman, *Realization of
groups with pairing as Jacobians of finite graphs*, arXiv:1410.5144.
-/

noncomputable section

namespace Gaudet2018Realization

variable {V E : Type}

/-- Divisors whose coefficients sum to zero (Section 2.1). -/
def degreeZeroDivisor (V : Type) [Fintype V] : AddSubgroup (V →₀ ℤ) :=
  (∑ v : V, Finsupp.applyAddHom v : (V →₀ ℤ) →+ ℤ).ker

open scoped Classical in
/-- The chip-firing divisor, with sign opposite to the source's positive Laplacian `div(f)`.
Parallel edges are counted individually. -/
def principalDivisor (G : Graph V E) [Fintype G.vertexSet] [Fintype G.edgeSet]
    (f : G.vertexSet → ℤ) : G.vertexSet →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun v ↦ ∑ e : G.edgeSet,
    if h : G.Inc e.val v.val then
      f ⟨h.other, h.isLink_other.right_mem⟩ - f v else 0

/-- The principal subgroup, pulled back to degree-zero divisors (Section 2.1). Changing the
Laplacian sign does not change this subgroup. -/
def principalSubgroup (G : Graph V E) [Fintype G.vertexSet] [Fintype G.edgeSet] :
    AddSubgroup (degreeZeroDivisor G.vertexSet) :=
  (AddSubgroup.closure (Set.range (principalDivisor G))).comap
    (degreeZeroDivisor G.vertexSet).subtype

/-- The Jacobian: degree-zero divisors modulo principal divisors (Section 2.1). -/
abbrev Jacobian (G : Graph V E) [Fintype G.vertexSet] [Fintype G.edgeSet] :=
  degreeZeroDivisor G.vertexSet ⧸ principalSubgroup G

/-- The value of the monodromy pairing on divisor representatives. The source's positive
Laplacian is `-principalDivisor G f`. -/
def MonodromyPairingValue (G : Graph V E) [Fintype G.vertexSet] [Fintype G.edgeSet]
    (x y : Jacobian G) (q : ℚ) : Prop :=
  ∃ (D₁ D₂ : degreeZeroDivisor G.vertexSet) (m : ℕ) (f : G.vertexSet → ℤ),
    0 < m ∧ QuotientAddGroup.mk D₁ = x ∧ QuotientAddGroup.mk D₂ = y ∧
      (-principalDivisor G f = fun v ↦ (m : ℤ) * (D₁ : G.vertexSet →₀ ℤ) v) ∧
        (∃ z : ℤ, q - (((m : ℚ)⁻¹) *
          (∑ v : G.vertexSet,
            ((D₂ : G.vertexSet →₀ ℤ) v : ℚ) * (f v : ℚ))) = z)

/-- **Conjecture 27** (after Proposition 26). For every `r, k ≥ 1`, no graph realizes
`(E_{2^r}) ^ k` as its Jacobian with monodromy pairing. -/
theorem conjecture_27_no_graph_realizes_exceptional_e_power
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ¬∃ (V E : Type) (G : Graph V E) (_ : Fintype G.vertexSet) (_ : Fintype G.edgeSet),
      G.Loopless ∧ G.toSimpleGraph.Connected ∧
        ∃ e : (Fin k → ZMod (2 ^ r) × ZMod (2 ^ r)) ≃+ Jacobian G,
          ∀ x y : Fin k → ZMod (2 ^ r) × ZMod (2 ^ r),
            MonodromyPairingValue G (e x) (e y)
              (∑ i : Fin k,
                ((x i).1.val * (y i).2.val + (x i).2.val * (y i).1.val : ℚ) /
                  (2 ^ r : ℚ)) := by
  sorry

end Gaudet2018Realization
