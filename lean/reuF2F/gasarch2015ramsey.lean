import Mathlib

/-!
# Ramsey Game Numbers

Authors: William Gasarch, Clyde Kruskal, Dao Lu, Eric Weaver, and Natalie Wilkinson.
Origin: [University of Maryland REU-CAAR
2014](https://www.cs.umd.edu/projects/reucaar/highlights-2014.html).
Reference: W. Gasarch, C. Kruskal, D. Lu, E. Weaver, and N. Wilkinson, *Ramsey Game Numbers*,
undated research report (PDF version November 23, 2015).
-/

noncomputable section

namespace Gasarch2015Ramsey

open scoped Classical in
/-- Blue can force the first star on `n` vertices in the achievement game on `m` vertices
(Definitions 1.1-1.3). Here `true` means Blue moves next, and exhausted tied boards are not wins. -/
inductive BlueWins (n m : ℕ) :
    SimpleGraph (Fin m) → SimpleGraph (Fin m) → Bool → Prop
  | won {B R : SimpleGraph (Fin m)} {turn : Bool}
      (blue : ∃ v, n - 1 ≤ B.degree v) (red : ∀ v, R.degree v < n - 1) :
      BlueWins n m B R turn
  | blueMove {B R : SimpleGraph (Fin m)} {u v : Fin m}
      (blue : ∀ w, B.degree w < n - 1) (red : ∀ w, R.degree w < n - 1)
      (distinct : u ≠ v) (uncoloredBlue : ¬B.Adj u v) (uncoloredRed : ¬R.Adj u v)
      (next : BlueWins n m (B ⊔ SimpleGraph.edge u v) R false) :
      BlueWins n m B R true
  | redMove {B R : SimpleGraph (Fin m)}
      (blue : ∀ w, B.degree w < n - 1) (red : ∀ w, R.degree w < n - 1)
      (available : ∃ u v, u ≠ v ∧ ¬B.Adj u v ∧ ¬R.Adj u v)
      (next : ∀ u v, u ≠ v → ¬B.Adj u v → ¬R.Adj u v →
        BlueWins n m B (R ⊔ SimpleGraph.edge u v) true) :
      BlueWins n m B R false

/-- **Unnumbered conjecture** (Section 4(2)). For every star on at least six vertices, its Ramsey
game number is `2 * n - 4`.

Both first-player victory on that board and failure on every smaller complete board are
retained, with no Maker-Breaker or induced-star substitution. -/
theorem star_ramsey_game_number (n : ℕ) (hn : 6 ≤ n) :
    BlueWins n (2 * n - 4) ⊥ ⊥ true ∧
      ∀ m : ℕ, m < 2 * n - 4 → ¬BlueWins n m ⊥ ⊥ true := by
  sorry

end Gasarch2015Ramsey
