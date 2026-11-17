import Mathlib

/-!
# Domination in Direct Products of Complete Graphs

Author: Harish Vemuri.
Origin: [University of Minnesota Duluth REU 2019](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: H. Vemuri, *Domination in direct products of complete graphs*, Discrete Appl. Math.
**285** (2020), 473-482; arXiv:1908.02445v1.
-/

namespace Vemuri2020Domination

open Finset

/-- The total domination number: the least size of a finite set whose open neighborhoods cover
the graph (Section 1). The target graphs are finite without isolates. -/
noncomputable def totalDominationNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, #D = k ∧
    ∀ v : V, ∃ w ∈ D, G.Adj v w}

/-- The Jacobsthal function `g(n)`: the least positive interval length forcing an integer
coprime to `n` in every interval of positive integers (Section 1). -/
noncomputable def jacobsthal (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ a > 0,
    ∃ i : ℕ, i < m ∧ Nat.Coprime (a + i) n}

/-- **Conjecture 1.11** (p. 4). Every positive gap from Jacobsthal's function to total
domination occurs for integers with arbitrarily many distinct prime factors. -/
theorem conjecture_1_11 (j : ℕ) (hj : 0 < j) (K : ℕ) :
    ∃ n ≥ 2, K ≤ #n.primeFactors ∧
      totalDominationNumber (SimpleGraph.addCayley {x : ZMod n | IsUnit x}) + j ≤
        jacobsthal n := by
  sorry

end Vemuri2020Domination
