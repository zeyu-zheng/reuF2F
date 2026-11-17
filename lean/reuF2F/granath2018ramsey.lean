import Mathlib

/-!
# Ramsey theory on Steiner triples

Authors: Elliot Granath, Andras Gyarfas, Jerry Hardee, Trent Watson, and Xiaoze Wu.
Origin: [Budapest Semesters in Mathematics 2016](https://www.bsmath.hu/articles.html).
Reference: E. Granath, A. Gyarfas, J. Hardee, T. Watson, and X. Wu, *Ramsey theory on Steiner
triples*, J. Combin. Des. **26** (2018), no. 1, 5-11; doi:10.1002/jcd.21585.
-/

namespace Granath2018Ramsey

/-- A configuration: a partial Steiner triple system with no isolated points (Section 1). -/
def IsConfiguration {v : ℕ} (C : Hypergraph (Fin v)) : Prop :=
  C.vertexSet = Set.univ ∧
  (∀ b ∈ C.edgeSet, b.ncard = 3) ∧
  C.IsLinear ∧
  (∀ x : Fin v, ¬C.IsIsolated x)

/-- A Steiner triple system: triples covering every pair of distinct points exactly once
(Section 1). -/
def IsSteinerTripleSystem {n : ℕ} (S : Hypergraph (Fin n)) : Prop :=
  S.vertexSet = Set.univ ∧
  (∀ b ∈ S.edgeSet, b.ncard = 3) ∧
  ∀ x y : Fin n, x ≠ y → ∃! b, b ∈ S.edgeSet ∧ x ∈ b ∧ y ∈ b

/-- Every sufficiently large Steiner triple system contains an injective, not necessarily induced,
copy of the configuration (Section 1). -/
def Unavoidable {v : ℕ} (C : Hypergraph (Fin v)) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (n % 6 = 1 ∨ n % 6 = 3) →
    ∀ S : Hypergraph (Fin n), IsSteinerTripleSystem S →
      ∃ f : Fin v ↪ Fin n, ∀ b ∈ C.edgeSet, f '' b ∈ S.edgeSet

/-- Every `t`-coloring of the blocks of every sufficiently large STS contains a monochromatic copy
of the configuration (Section 1). -/
def IsRamsey {v : ℕ} (C : Hypergraph (Fin v)) (t : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (n % 6 = 1 ∨ n % 6 = 3) →
    ∀ S : Hypergraph (Fin n), IsSteinerTripleSystem S →
      ∀ color : S.edgeSet → Fin t,
        ∃ f : Fin v ↪ Fin n, ∃ i : Fin t, ∀ b ∈ C.edgeSet,
          ∃ hb : f '' b ∈ S.edgeSet, color ⟨f '' b, hb⟩ = i

/-- **Unnumbered conjecture** (Section 5, concluding conjecture). Every unavoidable configuration is
`t`-Ramsey for every positive `t`, with all sufficiently large STS as hosts. -/
theorem concluding_conjecture {v : ℕ} (C : Hypergraph (Fin v))
    (hC : IsConfiguration C) (hU : Unavoidable C) (t : ℕ) (ht : 0 < t) :
    IsRamsey C t := by
  sorry

end Granath2018Ramsey
