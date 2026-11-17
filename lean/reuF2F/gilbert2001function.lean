import Mathlib

/-!
# Function Digraphs of Quadratic Maps Modulo p

Authors: Christie L. Gilbert, Joseph D. Kolesar, Clifford A. Reiter, and John D. Storey.
Origin: [Lafayette College REU 1996](https://math.lafayette.edu/opportunities/reu/publications/).
Reference: C. L. Gilbert, J. D. Kolesar, C. A. Reiter, and J. D. Storey, *Function digraphs of
quadratic maps modulo p*, Fibonacci Quart. **39** (2001), no. 1, 32-49.
-/

namespace Gilbert2001Function

/-- **Conjecture C** (Quadratic Digraph Isomorphism Conjecture; Section 4, p. 41). Over an odd
prime field, distinct canonical quadratic maps have isomorphic function digraphs only for the
parameter pair 11, 14 modulo 17.

Graph isomorphism is expressed by permutation conjugacy, as in Theorem 2 of the source. -/
theorem conjecture_c {p : ℕ} (hp : p.Prime) (hodd : Odd p) (a b : ZMod p) :
    (∃ e : Equiv.Perm (ZMod p),
      Function.Semiconj e (fun x ↦ x ^ 2 + a) (fun x ↦ x ^ 2 + b)) ↔
      a = b ∨
        (p = 17 ∧ ((a = 11 ∧ b = 14) ∨ (a = 14 ∧ b = 11))) := by
  sorry

end Gilbert2001Function
