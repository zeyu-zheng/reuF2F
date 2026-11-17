import Mathlib

/-!
# Wilf Equivalence in Weyl Groups and Signed Permutations

Author: Kaarel Haenni.
Origin: [MIT SPUR 2019](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: K. Haenni, *Wilf equivalence in Weyl groups and signed permutations*, MIT SPUR final
paper, August 1, 2019, 31 pp.; see also Y. Gao and K. Hanni, *Counting signed vexillary
permutations*, Adv. Appl. Math. **121** (2020), 102106.
-/

namespace Haenni2019Wilf

/-- The set `B_n^j(pattern)` of signed permutations with `j` positive images of positive indices
whose increasing `2n`-letter embedding avoids the pattern (Section 3). `Fin.rev` represents sign
reversal. -/
def avoidingSignedPermutations {k : ℕ} (pattern : Fin k → ℕ) (n j : ℕ) :
    Set (Equiv.Perm (Fin (2 * n))) :=
  {w | (∀ i, w i.rev = (w i).rev) ∧
    {i : Fin (2 * n) | n ≤ i.val ∧ n ≤ (w i).val}.ncard = j ∧
    ¬∃ f : Fin k → Fin (2 * n), StrictMono f ∧
      ∀ a b, w (f a) < w (f b) ↔ pattern a < pattern b}

/-- **Conjecture 3.26** (p. 30; also Gao–Hanni Conjecture 4.1). The patterns `12345` and `21354`
have equal signed-permutation avoidance counts at every positive-image count.

Containment is classical containment in the full `2n`-letter embedding, not root-system
containment. -/
theorem conjecture_3_26 (n j : ℕ) (hj : j ≤ n) :
    (avoidingSignedPermutations ![0, 1, 2, 3, 4] n j).ncard =
      (avoidingSignedPermutations ![1, 0, 2, 4, 3] n j).ncard := by
  sorry

end Haenni2019Wilf
