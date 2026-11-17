import Mathlib

/-!
# Fast Algorithms for Finding Pattern Avoiders and Counting Pattern Occurrences in Permutations

Author: William Kuszmaul.
Origin: [University of Minnesota Duluth REU
2015](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: W. Kuszmaul, *Fast algorithms for finding pattern avoiders and counting pattern
occurrences in permutations*, Math. Comp. **87** (2018), 987-1011; arXiv:1509.08216v4.
-/

namespace Kuszmaul2017Fast

open Finset

/-- Order standardization (Definition 2.2). Letters are zero-based. -/
def standardize (w : List ℕ) : List ℕ :=
  w.map fun a ↦ (w.filter fun b ↦ b < a).length

/-- All length-`n` classical pattern avoiders (Definitions 2.5 and 2.8). -/
def avoiders (pattern : List ℕ) (n : ℕ) : Finset (List ℕ) :=
  {w ∈ (List.range n).permutations.toFinset |
    !(w.sublists.any fun s ↦ standardize s == pattern)}

/-- Removal of the `j`-th largest letter followed by standardization (Definition 2.12). -/
def down (w : List ℕ) (j : ℕ) : List ℕ :=
  standardize (w.filter fun a ↦ a != w.length - j)

/-- The `j` largest letters in their original order (Section 2). -/
def upfix (w : List ℕ) (j : ℕ) : List ℕ :=
  w.filter fun a ↦ w.length - j ≤ a

/-- Algorithm 1 with the incremental upfix shortcut, returning the decision and one entry charge
plus the number of visited layers (pp. 10-11). Each layer checks deletion membership before
the upfix shortcut. -/
def detectAvoider (pattern : List ℕ) (H : Finset (List ℕ))
    (w : List ℕ) : Bool × ℕ :=
  if w = pattern then (false, 1) else
    let rec
      /-- Scan the given layers, returning the decision and the number of visited layers. -/
      loop : List ℕ → Bool × ℕ
      | [] => (true, 0)
      | j :: js =>
        if down w j ∉ H then (false, 1)
        else if j ≤ pattern.length ∧
            standardize (upfix w j) ≠ standardize (upfix pattern j) then (true, 1)
        else
          let result := loop js
          (result.1, result.2 + 1)
    let result := loop (List.range' 1 (min (pattern.length + 1) w.length))
    (result.1, result.2 + 1)

/-- **Unnumbered conjecture** (after Algorithm 5, pp. 10-11). The upfix-short-circuited
detector has uniformly constant amortized work on each full insertion layer.

Cost is the source's wide-word/dictionary model with prior membership, inverse and
pattern-upfix data supplied, not bit complexity; the uniform constant and interleaved shortcut
follow the contextual source reading. -/
theorem detector_linear_batch_cost :
    ∃ C > (0 : ℝ),
      ∀ k > 0, ∀ pattern : Equiv.Perm (Fin k),
        ∀ n ≥ 2,
        let H := avoiders (List.ofFn fun i ↦ (pattern i).val) (n - 1)
        ((∑ w ∈ H.biUnion (fun u ↦ (Finset.range n).image fun i ↦ u.insertIdx i (n - 1)),
            (detectAvoider (List.ofFn fun i ↦ (pattern i).val) H w).2 : ℕ) : ℝ) ≤
          C * (n : ℝ) * (#H : ℝ) := by
  sorry

end Kuszmaul2017Fast
