import Mathlib

/-!
# Accepted Elasticity in Local Arithmetic Congruence Monoids

Authors: Lorin Crawford, Vadim Ponomarenko, Jason Steinberg, and Marla Williams.
Origin: [San Diego State University REU 2012](https://cdoneill.sdsu.edu/reu/research.html).
Reference: L. Crawford, V. Ponomarenko, J. Steinberg, and M. Williams, *Accepted elasticity in
local arithmetic congruence monoids*, Results Math. **66** (2014), 227--245.
-/

namespace Crawford2014Accepted

/-- A sequence over a finite abelian group, a partition, and a subpartition satisfying the
prescribed product, avoidance, and ratio conditions (Definition 1). -/
structure Configuration {G : Type*} [CommGroup G] [Finite G]
    (g : G) (δ γ : ℕ) where
  order_le : orderOf g ≤ δ
  gamma_lt : γ < orderOf g
  /-- The number of blocks in the subpartition. -/
  c : ℕ
  /-- The number of blocks in the partition. -/
  d : ℕ
  c_pos : 0 < c
  d_pos : 0 < d
  /-- The underlying sequence over `G`, as a multiset. -/
  sequence : Multiset G
  /-- The blocks of the partition of the sequence. -/
  partition : Fin d → Multiset G
  /-- The blocks of the subpartition of the sequence. -/
  subpartition : Fin c → Multiset G
  partition_sum : ∑ i, partition i = sequence
  subpartition_le : ∑ i, subpartition i ≤ sequence
  partition_prod : ∀ i, (partition i).prod = g ^ (γ + 1)
  partition_avoids : ∀ i, ∀ T : Multiset G,
    T ≤ partition i → T ≠ 0 →
      ∀ k ≥ 1, k ≤ γ → T.prod ≠ g ^ k
  subpartition_prod : ∀ i, (subpartition i).prod = g ^ γ
  ratio : 1 + ((δ : ℚ) - 1) / ((δ : ℚ) - γ) ≤ (c : ℚ) / d

/-- **Conjecture 1** (author manuscript, Section 6). Configuration existence is downward closed in
positive `γ`. -/
theorem conjecture_1 {G : Type*} [CommGroup G] [Finite G]
    (g : G) (δ γ : ℕ) (hγ : 0 < γ)
    (h : Nonempty (Configuration g δ γ)) :
    Nonempty (Configuration g δ (γ - 1)) := by
  sorry

end Crawford2014Accepted
