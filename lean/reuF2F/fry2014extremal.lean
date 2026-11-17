import Mathlib

/-!
# Extremal Arithmetic in Numerical Semigroups

Authors: Andy Fry, Sarah McConnell, Claire Spychalla, Zofia Stanley, and Brandon Van Over.
Origin: [San Diego State University REU 2014](https://cdoneill.sdsu.edu/reu/research.html).
Reference: A. Fry, S. McConnell, C. Spychalla, Z. Stanley, and B. Van Over, *Extremal
Arithmetic in Numerical Semigroups*, SDSU Mathematics REU, August 8, 2014, 79 pp.
-/

namespace Fry2014Extremal

open Finset

/-- All nonnegative coefficient factorizations over the listed generators (Section 1). -/
def factorizations (A : Finset ℕ) (m : ℕ) : Set (A → ℕ) :=
  {c | ∑ g : A, c g * g.val = m}

/-- The lengths of all factorizations of an element (Section 1). -/
def lengthSet (A : Finset ℕ) (m : ℕ) : Set ℕ :=
  (fun c : A → ℕ ↦ ∑ g, c g) '' factorizations A m

/-- All successive length gaps over the entire generated monoid (Section 1). -/
def deltaSet (A : Finset ℕ) : Set ℕ :=
  {d | ∃ m : ℕ,
    m ∈ (AddSubmonoid.closure (A : Set ℕ) : Set ℕ) ∧
      ∃ l r : lengthSet A m, CovBy l r ∧ d = r.val - l.val}

/-- A nonempty positive set with odd maximum meeting each complementary pair about that maximum
(Definitions 4.3-4.4). -/
def IsGolden (G : Finset ℕ) : Prop :=
  G.Nonempty ∧ (∀ g : G, 0 < g.val) ∧ Odd (G.sup id) ∧
    ∀ j > 0, j < G.sup id →
      j ∈ (G : Set ℕ) ∨ G.sup id - j ∈ (G : Set ℕ)

/-- **Conjecture 4.22** (Goldmember; p. 46). A changed delta set requires a missing golden or
reflected golden set of index `⌊t / 2⌋`.

Golden sets are read in generator-offset coordinates, as in the source's examples and tables,
not in affine generator values; this is the full necessary condition, not Conjecture 4.23. -/
theorem goldmember_conjecture (a x t : ℕ) (I : Finset ℕ)
    (ha : 0 < a) (hx : 0 < x) (ht : 0 < t) (hat : t < a)
    (hcoprime : Nat.Coprime a x)
    (hI : I ≤ Finset.range (t + 1))
    (hzero : 0 ∈ (I : Set ℕ)) (hlast : t ∈ (I : Set ℕ))
    (hcard : 2 ≤ #I) (hindex : (I.erase 0).gcd id = 1) :
    (∀ g : (Finset.range (t + 1)).image (fun i ↦ a + i * x),
      g.val ∉ (AddSubmonoid.closure
        (((Finset.range (t + 1)).image (fun i ↦ a + i * x)).erase g.val : Set ℕ) : Set ℕ)) →
    (∀ g : I.image (fun i ↦ a + i * x),
      g.val ∉ (AddSubmonoid.closure
        ((I.image (fun i ↦ a + i * x)).erase g.val : Set ℕ) : Set ℕ)) →
    deltaSet (I.image (fun i ↦ a + i * x)) ≠ ({x} : Set ℕ) →
    ∃ N : ℕ, ∃ G : Finset ℕ,
      0 < N ∧ N = t / 2 ∧ IsGolden G ∧ G.sup id = 2 * N - 1 ∧
        (G ≤ Finset.Ioo 0 t \ I ∨ G.image (fun g ↦ t - g) ≤ Finset.Ioo 0 t \ I) := by
  sorry

end Fry2014Extremal
