import Mathlib

/-!
# On the Asymmetric Generalizations of Two Extremal Questions on Friends-and-Strangers Graphs

Author: Kiril Bangachev.
Origin: [University of Minnesota Duluth REU 2021](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: K. Bangachev, *On the asymmetric generalizations of two extremal questions on
friends-and-strangers graphs*, European J. Combin. **104** (2022), 103529; arXiv:2107.06789.
-/

namespace Bangachev2022Asymmetric

/-- The friends-and-strangers graph: configurations are bijections, and swaps are allowed along
an edge of `X` exactly when the two occupants are adjacent in `Y` (Definition 1.1). -/
def friendsStrangers {n : ℕ} (X Y : SimpleGraph (Fin n)) :
    SimpleGraph (Equiv.Perm (Fin n)) :=
  SimpleGraph.fromRel fun σ τ ↦
    ∃ a b, X.Adj a b ∧ Y.Adj (σ a) (σ b) ∧ τ = (Equiv.swap a b).trans σ

open scoped Classical in
/-- **Conjecture 8.1** (arXiv v1, p. 26). The asymmetric minimum-degree bound ensures
connectivity without requiring both minimum degrees to exceed `n / 2`.

Zhao et al. (2025) prove a restricted case. -/
theorem conjecture_8_1 {n : ℕ} (X Y : SimpleGraph (Fin n))
    (hX : X.Connected) (hY : Y.Connected)
    (hdegree : 3 * n ≤ 2 * min X.minDegree Y.minDegree +
      3 * max X.minDegree Y.minDegree) :
    (friendsStrangers X Y).Connected := by
  sorry

end Bangachev2022Asymmetric
