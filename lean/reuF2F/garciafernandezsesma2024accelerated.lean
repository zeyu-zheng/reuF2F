import Mathlib

/-!
# The Accelerated Zeckendorf Game

Authors: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon,
Risa Vandegrift, and Ajmain Yamin.
Origin: [Polymath Jr. 2022](https://geometrynyc.wixsite.com/polymathreu/results2022).
Reference: D. Garcia-Fernandezsesma, S. J. Miller, T. Rascon, R. Vandegrift, and A. Yamin,
*The accelerated Zeckendorf game*, Fibonacci Quart. **62** (2024), no. 1, 3-14.
-/

namespace GarciaFernandezSesma2024Accelerated

/-- One turn: any positive number of copies of one combining or splitting move on the finitely
supported Fibonacci-count state (Definition 1.2). -/
def LegalMove (s t : Finsupp ℕ ℕ) : Prop :=
  ∃ i m : ℕ, 0 < i ∧ 0 < m ∧
    ((m ≤ s i ∧ m ≤ s (i + 1) ∧
      t = s - Finsupp.single i m - Finsupp.single (i + 1) m +
        Finsupp.single (i + 2) m) ∨
     (2 * m ≤ s i ∧
      t = s - Finsupp.single i (2 * m) +
        if i = 1 then Finsupp.single 2 m
        else if i = 2 then Finsupp.single 1 m + Finsupp.single 3 m
        else Finsupp.single (i - 2) m + Finsupp.single (i + 1) m))

/-- A winning state: a move either ends the game or permits a winning continuation after every
opponent reply, the last player to move winning (Section 2.2). -/
inductive Winning : Finsupp ℕ ℕ → Prop
  | move {s t : Finsupp ℕ ℕ} (legal : LegalMove s t)
      (reply : ∀ u : Finsupp ℕ ℕ, LegalMove t u → Winning u) : Winning s

/-- **Conjecture 1.6**. Player 1 has a winning strategy in the two-player Accelerated
Zeckendorf Game starting from `n` copies of `F_1` for every `n > 9`. -/
theorem conjecture_1_6 (n : ℕ) (hn : 9 < n) :
    Winning (Finsupp.single 1 n) := by
  sorry

end GarciaFernandezSesma2024Accelerated
