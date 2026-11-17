import Mathlib

/-!
# Restricted Stacks as Functions

Author: Katalin Berlow.
Origin: [University of Minnesota Duluth REU 2020](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: K. Berlow, *Restricted stacks as functions*, Discrete Math. **344** (2021), 112571;
arXiv:2008.01164.
-/

namespace Berlow2021Restricted

/-- Classical containment of a length-three pattern as a subsequence with all pairwise order
relations preserved (Definition 1.2). -/
def Contains (p : Fin 3 → ℕ) (w : List ℕ) : Prop :=
  ∃ i : Fin 3 → Fin w.length, StrictMono i ∧
    ∀ a b, w[i a] < w[i b] ↔ p a < p b

open scoped Classical in
/-- The `T`-restricted stack sort: push greedily while the stack stays `T`-avoiding, otherwise
pop to the output (Definition 1.3). -/
noncomputable def stackSort (T : Finset (Fin 3 → ℕ)) (input : List ℕ) : List ℕ :=
  let step := fun (state : List ℕ × List ℕ × List ℕ) ↦
    let (remaining, stack, output) := state
    match remaining, stack with
    | [], [] => state
    | [], y :: ys => ([], ys, y :: output)
    | x :: xs, [] => (xs, [x], output)
    | x :: xs, y :: ys =>
      if ∃ p ∈ T, Contains p (x :: y :: ys) then
        (x :: xs, ys, y :: output)
      else
        (xs, x :: y :: ys, output)
  let result := step^[2 * input.length] (input, [], [])
  result.2.2.reverse

/-- **Conjecture 5.1** (arXiv v2, p. 14). For either specified pair of forbidden patterns, the
periodic permutations are exactly the identity and its reverse.

O. Zhang (2025), Conjecture 4.2, prints "inverse" for these pairs; the original "reverse" is
kept. -/
theorem conjecture_5_1 {n : ℕ} (π : Equiv.Perm (Fin n))
    (T : Finset (Fin 3 → ℕ))
    (hT : T = {![1, 3, 2], ![2, 1, 3]} ∨ T = {![2, 3, 1], ![2, 1, 3]}) :
    List.ofFn (fun i ↦ (π i).val + 1) ∈ Function.periodicPts (stackSort T) ↔
      π = Equiv.refl (Fin n) ∨ π = Fin.revPerm := by
  sorry

end Berlow2021Restricted
