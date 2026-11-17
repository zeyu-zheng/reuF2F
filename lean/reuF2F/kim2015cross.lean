import Mathlib

/-!
# The Cross Number of Minimal Zero-sum Sequences in Finite Abelian Groups

Author: Bumsoo Kim.
Origin: [University of Minnesota Duluth REU](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: B. Kim, *The Cross Number of Minimal Zero-sum Sequences in Finite Abelian Groups*,
arXiv:1410.6867.
-/

noncomputable section

universe u

namespace Kim2015Cross

/-- A sequence is zero-sum free if no nonempty subsequence has sum zero. -/
def IsZeroSumFree {G : Type*} [AddCommMonoid G] (S : Multiset G) : Prop :=
  ∀ T : Multiset G, T ≤ S → T ≠ 0 → T.sum ≠ 0

/-- A sequence is minimal zero-sum when it is nonempty, zero-sum, and its only zero-sum
subsequences are the empty sequence and itself. -/
def IsMinimalZeroSum {G : Type*} [AddCommMonoid G] (S : Multiset G) : Prop :=
  S ≠ 0 ∧ S.sum = 0 ∧
    ∀ T : Multiset G, T ≤ S → T.sum = 0 → T = 0 ∨ T = S

/-- The cross number `k(S) = sum_g v_g(S) / ord(g)` of a sequence. -/
def crossNumber {G : Type*} [AddMonoid G] (S : Multiset G) : ℚ :=
  (S.map fun g : G ↦ (1 : ℚ) / (addOrderOf g : ℚ)).sum

/-- `q` is the cross number `K(G)`, the maximum cross number among minimal zero-sum
sequences over `G`. -/
def HasCrossNumber (G : Type*) [AddCommMonoid G] (q : ℚ) : Prop :=
  IsGreatest {r : ℚ | ∃ S : Multiset G, IsMinimalZeroSum S ∧ crossNumber S = r} q

/-- A cyclic prime-power decomposition `G ≃ ⨁ᵢ C_{pᵢ^{aᵢ}}`, as a product of cyclic groups. -/
structure CyclicPrimePowerDecomposition (G : Type u) [AddCommGroup G] where
  /-- The index type of the cyclic factors. -/
  ι : Type u
  fintype : Fintype ι
  /-- The prime `pᵢ` of each cyclic factor. -/
  prime : ι → ℕ
  /-- The exponent `aᵢ` of each cyclic factor. -/
  exponent : ι → ℕ
  prime_isPrime : ∀ i : ι, Nat.Prime (prime i)
  exponent_pos : ∀ i : ι, 0 < exponent i
  /-- The isomorphism of `G` with the product of the cyclic factors. -/
  equiv : G ≃+ (∀ i : ι, ZMod (prime i ^ exponent i))

namespace CyclicPrimePowerDecomposition

attribute [instance] fintype

/-- The little cross number `k⋆(G) = ∑ i, (1 - 1 / pᵢ ^ aᵢ)` of a cyclic prime-power
decomposition. -/
def kStar {G : Type u} [AddCommGroup G] (D : CyclicPrimePowerDecomposition G) : ℚ :=
  letI := D.fintype
  ∑ i : D.ι, ((1 : ℚ) - (1 : ℚ) / ((D.prime i ^ D.exponent i : ℕ) : ℚ))

end CyclicPrimePowerDecomposition

/-- **Conjecture 23**. Maximal minimal zero-sum sequences consist of one element and primary
zero-sum-free factors, with cross number `K*`; zero-sum-free sequences attaining `k*` likewise
split into primary factors. -/
theorem conjecture_23_primary_splitting_and_krause_zahlten_value
    {G : Type*} [AddCommGroup G] [Finite G]
    (D : CyclicPrimePowerDecomposition G) :
    (∀ U : Multiset G,
      IsMinimalZeroSum U → HasCrossNumber G (crossNumber U) →
        ∃ (g : G) (parts : {p : ℕ // p ∈ (AddMonoid.exponent G).primeFactors} → Multiset G),
          U = {g} + ∑ p, parts p ∧
            ∀ p, IsZeroSumFree (parts p) ∧
              ∀ x ∈ parts p, x ∈ AddCommGroup.primaryComponent G p.1) ∧
      HasCrossNumber G (D.kStar + (1 : ℚ) / (AddMonoid.exponent G : ℚ)) ∧
        ∀ S : Multiset G, IsZeroSumFree S → crossNumber S = D.kStar →
          ∃ parts : {p : ℕ // p ∈ (AddMonoid.exponent G).primeFactors} → Multiset G,
            S = ∑ p, parts p ∧
              ∀ p, IsZeroSumFree (parts p) ∧
                ∀ x ∈ parts p, x ∈ AddCommGroup.primaryComponent G p.1 := by
  sorry

end Kim2015Cross
