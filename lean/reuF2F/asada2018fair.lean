import Mathlib

/-!
# Fair Division and Generalizations of Sperner- and KKM-Type Results

Authors: Megumi Asada, Florian Frick, Vivek Pisharody, Maxwell Polevy,
David Stoner, Ling Hei Tsang, and Zoe Wellner.
Origin: [Cornell SPUR 2016](https://www.math.cmu.edu/~ffrick/REU.html).
Reference: M. Asada, F. Frick, V. Pisharody, M. Polevy, D. Stoner, L. H. Tsang, and Z. Wellner,
*Fair division and generalizations of Sperner- and KKM-type results*, SIAM J. Discrete Math.
**32** (2018), no. 1, 591-610; arXiv:1701.04955v1.
-/

namespace Asada2018Fair

/-- **Conjecture 2.11** (p. 9). Every divisible necklace admits an optimal-size binary splitting
among any `k ≥ 4` thieves in the smallest possible hypercube (Definition 2.6).

Empty pieces from repeated cuts are allowed. The power-of-two case is proved by
Jojic--Panina--Zivaljevic. -/
theorem conjecture_2_11 {q : ℕ} (k : ℕ) (hq : 0 < q) (hk : 4 ≤ k)
    (necklace : List (Fin q)) (hdiv : ∀ c : Fin q, k ∣ necklace.count c) :
    ∃ (pieces : Fin ((k - 1) * q + 1) → List (Fin q))
        (recipient : Fin ((k - 1) * q + 1) → Fin k)
        (vertex : Fin k ↪ (Fin (Nat.clog 2 k) → Bool)),
      (List.ofFn pieces).flatten = necklace ∧
      (∀ (thief : Fin k) (c : Fin q),
        k * (∑ i,
          if recipient i = thief then (pieces i).count c else 0) = necklace.count c) ∧
      (∀ i : Fin ((k - 1) * q),
        hammingDist (vertex (recipient i.castSucc)) (vertex (recipient i.succ)) = 1) := by
  sorry

end Asada2018Fair
