import Mathlib

/-!
# Towards the Gaussianity of Random Zeckendorf Games

Authors: Justin Cheigh, Guilherme Zeus Dantas e Moura, Ryan Jeong, Jacob Lehmann
Duke, Wyatt Milgrim, Steven J. Miller, and Prakod Ngamlamai.
Origin: [Williams College SMALL REU 2022](https://arxiv.org/pdf/2210.11038v1#page=28).
Reference: J. Cheigh, G. Z. Dantas e Moura, R. Jeong, J. Lehmann Duke, W. Milgrim, S. J. Miller,
and P. Ngamlamai, *Towards the Gaussianity of random Zeckendorf games*, preprint (2022);
arXiv:2210.11038v1.
-/

namespace Cheigh2025Towards

open scoped Topology
open Finset

/-- A state of the Bergman game: a finitely supported integer-indexed chip tape (Baily et al.,
Definition 1.1). -/
abbrev State := ℤ →₀ ℕ

/-- All legal next states: combine chips at `i, i + 1` into `i + 2`, or split two
chips at `i` into `i - 2, i + 1` (Baily et al., Definition 1.1). -/
noncomputable def successors (s : State) : Finset State :=
  s.support.biUnion fun i ↦
    (if 0 < s (i + 1) then
      {s - Finsupp.single i 1 - Finsupp.single (i + 1) 1 +
        Finsupp.single (i + 2) 1}
    else {} : Finset State) ∪
    (if 2 ≤ s i then
      {s - Finsupp.single i 2 + Finsupp.single (i - 2) 1 +
        Finsupp.single (i + 1) 1}
    else {})

/-- A complete Bergman game from `N` chips at index zero, as its ordered states from the initial
to the terminal state (Baily et al., Definition 1.1; Section 1.2). -/
structure Game (N : ℕ) where
  /-- The ordered list of chip configurations visited by the game. -/
  states : List State
  starts : states.head? = some (Finsupp.single 0 N)
  legal : states.IsChain (fun s t ↦ t ∈ successors s)
  terminal : ∀ s, states.getLast? = some s → successors s = {}

/-- **Conjecture 6.1**. Each player's winning probability tends to one half for random Bergman
games, both when complete games are uniform and when available moves are uniform.

An odd number of moves means Player 1 wins, and an even number means Player 2 wins. -/
theorem conjecture_6_1 :
    let mass : Bool → (N : ℕ) → Game N → ℝ := fun byMove N g ↦
      if byMove then
        (g.states.dropLast.map (fun s ↦ 1 / (#(successors s) : ℝ))).prod
      else 1 / (Nat.card (Game N) : ℝ)
    ∀ (byMove : Bool) (parity : Fin 2),
      Filter.Tendsto
        (fun N : ℕ ↦ ∑' g : Game N,
          if (g.states.length - 1) % 2 = parity.val then mass byMove N g else 0)
        Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

end Cheigh2025Towards
