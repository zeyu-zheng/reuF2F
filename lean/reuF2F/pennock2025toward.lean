import Mathlib

/-!
# Toward Fair and Strategyproof Tournament Rules for Tournaments with Partially Transferable Utilities

Authors: David Pennock, Ariel Schvartzman, and Eric Xue.
Origin: [DIMACS REU 2021](https://archive.reu.dimacs.rutgers.edu/2021/ex20/public_html/).
Reference: D. Pennock, A. Schvartzman, and E. Xue, *Toward fair and strategyproof tournament
rules for tournaments with partially transferable utilities*, arXiv:2408.10346v1 (2024), 25 pp.
-/

namespace Pennock2025Toward

/-- A tournament: a complete asymmetric digraph (Definition 1). An edge points from winner to
loser. -/
def Tournament (n : ℕ) :=
  { G : Digraph (Fin n) //
    (∀ i j, G.Adj i j → ¬G.Adj j i) ∧
    (∀ i j, i ≠ j → G.Adj i j ∨ G.Adj j i) }

/-- A tournament rule: randomized winner-selection rules, one for each positive size
(Definition 2). -/
abbrev TournamentRule :=
  (n : PNat) → Tournament (n : ℕ) → PMF (Fin (n : ℕ))

/-- `S`-adjacency: only matches with both endpoints in the coalition change (Definition 7). -/
def SAdjacent {n : ℕ} (S : Set (Fin n)) (T T' : Tournament n) : Prop :=
  ∀ a b, a ≠ b → ¬(a ∈ S ∧ b ∈ S) →
    (T.val.Adj a b ↔ T'.val.Adj a b)

/-- **Conjecture 1**. A monotone, Condorcet-consistent, 2-NM_1 rule exists for every positive
size.

Adjacency follows the mutual-match reading of Definition 7's prose rather than its inconsistent
displayed complement condition; probability differences are taken in the reals, and no anonymity
condition is imposed. -/
theorem conjecture_1 :
    ∃ r : TournamentRule,
      (∀ (n : PNat) (T T' : Tournament (n : ℕ)) (i j : Fin (n : ℕ))
          (_ : i ≠ j) (_ : T ≠ T')
          (_ : SAdjacent {i, j} T T') (_ : T.val.Adj i j),
          (r n T' i).toReal ≤ (r n T i).toReal) ∧
      (∀ (n : PNat) (T : Tournament (n : ℕ)) (i : Fin (n : ℕ))
          (_ : ∀ j : Fin (n : ℕ), j ≠ i → T.val.Adj i j),
          r n T i = 1) ∧
      (∀ (n : PNat) (T T' : Tournament (n : ℕ)) (i j : Fin (n : ℕ))
          (_ : i ≠ j) (_ : T ≠ T') (_ : SAdjacent {i, j} T T'),
          (r n T' i).toReal + (r n T' j).toReal ≤
            (r n T i).toReal + (r n T j).toReal +
              max ((r n T i).toReal - (r n T' i).toReal)
                ((r n T j).toReal - (r n T' j).toReal)) := by
  sorry

end Pennock2025Toward
