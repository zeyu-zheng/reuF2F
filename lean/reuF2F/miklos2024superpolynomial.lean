import Mathlib

/-!
# Superpolynomial period lengths of the winning positions in the subtraction game

Authors: István Miklós and Logan Post.
Origin: [Budapest Semesters in Mathematics 2022](https://www.bsmath.hu/articles.html).
Reference: I. Miklós and L. Post, *Superpolynomial period lengths of the winning positions in the
subtraction game*, Internat. J. Game Theory **53** (2024), 1275-1313;
doi:10.1007/s00182-024-00911-5; arXiv:2312.02426v1.
-/

namespace Miklos2024Superpolynomial

/-- The window transition `F` for the moves `{a, b, c}`, appending the outcome of the next
position, with `true` meaning winning (Equations (1)-(2) and Definition 3).

The printed shift coordinates of Equation (3) are read consistently with Equations (1)-(2). -/
def nextState (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (v : Fin c → Bool) : Fin c → Bool :=
  fun i ↦
    if h : i.val + 1 < c then v ⟨i.val + 1, h⟩
    else !(v ⟨c - a, by omega⟩ && v ⟨c - b, by omega⟩ && v ⟨0, by omega⟩)

/-- The outcome sequence of the game with seed `S` (Definition 3).

`S i` is the seed value at position `i - c`, and the outcome at `n` is the last window entry
after `n + 1` transitions. -/
def winningSequence (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (S : Fin c → Bool) (n : ℕ) : Bool :=
  ((nextState a b c ha hab hbc)^[n + 1] S) ⟨c - 1, by omega⟩

/-- **Conjecture 4** (Section 7, p. 35). For moves `a < b < c` with `gcd(a, b, c) = 1`, every
seed yields an eventually periodic outcome sequence with period less than `c ^ 2`.

The least period is encoded as the existence of a positive eventual period below the bound, with
no restriction on the preperiod. -/
theorem conjecture_4 (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hcoprime : (a.gcd b).gcd c = 1) (S : Fin c → Bool) :
    ∃ p > 0, p < c ^ 2 ∧ ∃ N, ∀ n ≥ N,
      winningSequence a b c ha hab hbc S (n + p) = winningSequence a b c ha hab hbc S n := by
  sorry

end Miklos2024Superpolynomial
