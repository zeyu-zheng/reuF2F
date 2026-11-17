import Mathlib

/-!
# Sprague-Grundy Values of the R-Wythoff Game

Author: Albert Gu.
Origin: [University of Minnesota Duluth REU 2013](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: A. Gu, *Sprague-Grundy Values of the R-Wythoff Game*, Electron. J. Combin. **22**
(2015), no. 2, Paper 2.13, 15 pp.; doi:10.37236/4579.
-/

noncomputable section

namespace Gu2015Sprague

/-- The Sprague-Grundy value of R-Wythoff (Sections 1 and 1.2). Only a largest pile may be reduced
singly, and equal positive reductions may empty either pile. -/
def grundy (a b : ℕ) : ℕ :=
  sInf {g : ℕ |
    (b ≤ a → ∀ c : Fin a, grundy c.val b ≠ g) ∧
    (a ≤ b → ∀ d : Fin b, grundy a d.val ≠ g) ∧
    (∀ t : Fin (min a b + 1), 0 < t.val →
      grundy (a - t.val) (b - t.val) ≠ g)}
termination_by a + b
decreasing_by
  all_goals omega

/-- The smaller coordinate of the zero-indexed `n`th `g`-position (Section 1.2). Positions are
ordered increasingly by their smaller coordinate. -/
def lowerPosition (g n : ℕ) : ℕ :=
  Nat.nth (fun a ↦ ∃ b ≥ a, grundy a b = g) n

/-- The larger coordinate paired with `lowerPosition g n` (Section 1.2). These larger coordinates
are not independently sorted and may repeat. -/
def upperPosition (g n : ℕ) : ℕ :=
  sInf {b : ℕ | lowerPosition g n ≤ b ∧ grundy (lowerPosition g n) b = g}

/-- The Fibonacci-type sequence `F^(a,b)` with seeds `a`, `b` (Section 3.1). -/
def fibonacciSequence (a b : ℕ) : ℕ → ℕ :=
  ({ order := 2, coeffs := fun _ ↦ 1 } : LinearRecurrence ℕ).mkSol
    (fun i ↦ if i.val = 0 then a else b)

/-- **Conjecture 1** (Section 3.2). For `g > 3`, the paired `g`-positions eventually equal the
Beatty P-positions minus a common offset, except for alternating unit corrections along finitely
many disjoint Fibonacci sequences.

The printed overloaded `k` is separated into family count `r` and term index `t`, as in
Theorems 7 and 8 and the prose following the conjecture. -/
theorem conjecture_1 (g : ℕ) (hg : 3 < g) :
    let φ : ℝ := (1 + √5) / 2
    ∃ (N : ℕ) (C : ℤ) (r : ℕ) (a b : Fin r → ℕ) (x : Fin r → Fin 2),
      (∀ i j : Fin r, i ≠ j →
        Disjoint (Set.range (fibonacciSequence (a i) (b i)))
          (Set.range (fibonacciSequence (a j) (b j)))) ∧
      ∀ n ≥ N,
        (∀ (i : Fin r) (t : ℕ), n = fibonacciSequence (a i) (b i) t →
          (lowerPosition g n : ℤ) =
            Int.floor (φ * n) - (C + (-1 : ℤ) ^ (t + (x i).val)) ∧
          (upperPosition g n : ℤ) =
            Int.floor (φ ^ 2 * n) - (C + (-1 : ℤ) ^ (t + (x i).val))) ∧
        ((∀ (i : Fin r) (t : ℕ), n ≠ fibonacciSequence (a i) (b i) t) →
          (lowerPosition g n : ℤ) = Int.floor (φ * n) - C ∧
          (upperPosition g n : ℤ) = Int.floor (φ ^ 2 * n) - C) := by
  sorry

end Gu2015Sprague
