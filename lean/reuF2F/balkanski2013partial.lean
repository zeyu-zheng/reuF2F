import Mathlib

/-!
# Partial Word DFAs

Authors: Eric Balkanski, F. Blanchet-Sadri, Matthew Kilgore, and B. J. Wyatt.
Origin: [UNCG REU 2012](https://home.uncg.edu/cmp/reu/summer2012/).
Reference: E. Balkanski, F. Blanchet-Sadri, M. Kilgore, and B. J. Wyatt, *Partial word DFAs*,
in CIAA 2013, Lecture Notes in Comput. Sci. **7982**, 36-47.
-/

noncomputable section

namespace Balkanski2013Partial

/-- Hole substitution: each hole independently becomes a letter from one fixed subset, while
ordinary letters stay unchanged (Section 1). -/
def holeSubstitution {α : Type} (S : Set α) (L : Language (Option α)) : Language α :=
  {w | ∃ u ∈ L, List.Forall₂ (fun o a ↦ match o with
    | none => a ∈ S
    | some b => a = b) u w}

/-- The minimum partial-word DFA state count, over all hole substitutions and complete DFAs
representing the language (Section 1). -/
def partialStateComplexity {α : Type} (L : Language α) : ℕ :=
  sInf {k | ∃ S : Set α, ∃ M : DFA (Option α) (Fin k),
    holeSubstitution S M.accepts = L}

/-- **Unnumbered conjecture** (Section 4, p. 47). Every count from `n` to `2 ^ n - 1` occurs as
the minimum complete-DFA size of a regular language whose minimum partial-word DFA size is `n`.

The alphabet may vary, and rejecting sink states are counted. -/
theorem state_complexity_spectrum (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hm : m ≤ 2 ^ n - 1) :
    ∃ k : ℕ, ∃ L : Language (Fin k),
      L.IsRegular ∧ partialStateComplexity L = n ∧
        Nat.card (Set.range L.leftQuotient) = m := by
  sorry

end Balkanski2013Partial
