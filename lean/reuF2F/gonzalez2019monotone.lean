import Mathlib

/-!
# Monotone Catenary Degree in Numerical Monoids

Authors: Daniel Gonzalez Cedre, Cameron Wright, and Jenna Zomback.
Origin: [PURE Math 2015](https://www.nsf.gov/awardsearch/showAward?AWD_ID=1045147).
Reference: D. Gonzalez Cedre, C. Wright, and J. Zomback, *Monotone Catenary Degree in Numerical
Monoids*, preprint; arXiv:1912.08114v3.
-/

noncomputable section

namespace Gonzalez2019Monotone

open scoped ENNReal

/-- The factorizations of `m` into the indexed generators (Section 3). -/
def Factorizations {k : ℕ} (generators : Fin k → ℕ) (m : ℕ) :=
  {z : Fin k → ℕ // ∑ i, z i * generators i = m}

/-- The distance: the larger length minus the length of the componentwise gcd (Definition 2). -/
def factorizationDistance {k : ℕ} (z w : Fin k → ℕ) : ℕ :=
  max (∑ i, z i) (∑ i, w i) - ∑ i, min (z i) (w i)

/-- The least uniform chain bound over all factorizations of all monoid elements (Definitions 3-4,
Section 3). The value is in `ℕ∞`, allowing infinity for a general tuple. -/
def catenaryDegree {k : ℕ} (generators : Fin k → ℕ) : ℕ∞ :=
  sInf {N : ℕ∞ | ∀ m : ℕ, ∀ z w : Factorizations generators m,
    Relation.ReflTransGen
      (fun x y : Factorizations generators m ↦
        (factorizationDistance x.val y.val : ℕ∞) ≤ N) z w}

/-- The uniform bound using nondecreasing-length chains (Definition 8, Section 3). Only one
length order is encoded, since reversing a chain covers the other. -/
def monotoneCatenaryDegree {k : ℕ} (generators : Fin k → ℕ) : ℕ∞ :=
  sInf {N : ℕ∞ | ∀ m : ℕ, ∀ z w : Factorizations generators m,
    (∑ i, z.val i) ≤ ∑ i, w.val i →
      Relation.ReflTransGen
        (fun x y : Factorizations generators m ↦
          (factorizationDistance x.val y.val : ℕ∞) ≤ N ∧
            (∑ i, x.val i) ≤ ∑ i, y.val i) z w}

/-- **Conjecture 1** (Section 5). The generalized arithmetic numerical monoid has equal ordinary
and monotone catenary degrees when `gcd(h - 1, d) > 1`.

The parameters express the source's minimal three-generator family. -/
theorem conjecture_1 (a h d : ℕ) (ha : 3 ≤ a) (hh : 2 ≤ h)
    (hd : 0 < d) (had : Nat.Coprime a d) (hgcd : 1 < Nat.gcd (h - 1) d) :
    monotoneCatenaryDegree (![a, a * h + d, a * h + 2 * d] : Fin 3 → ℕ) =
      catenaryDegree (![a, a * h + d, a * h + 2 * d] : Fin 3 → ℕ) := by
  sorry

end Gonzalez2019Monotone
