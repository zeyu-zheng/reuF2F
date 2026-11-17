import Mathlib

/-!
# Sandpile Groups of Cayley Graphs of F_2^r

Authors: Jiyang Gao, Jared Marx-Kuo, Vaughan McDonald, and Chi Ho Yuen.
Origin: [University of Minnesota Twin Cities REU
2018](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: J. Gao, J. Marx-Kuo, V. McDonald, and C. H. Yuen, *Sandpile Groups of Cayley Graphs
of F_2^r*, preprint; arXiv:1912.06919v3.
-/

noncomputable section

namespace Gao2019Sandpile

/-- The hypercube: binary vectors adjacent when exactly one coordinate differs (Section 1). -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → ZMod 2) :=
  SimpleGraph.fromRel fun u v ↦ hammingDist u v = 1

open scoped Classical in
/-- The sandpile group: the torsion subgroup of the integral Laplacian cokernel (Section 1). -/
abbrev sandpile {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :=
  AddCommGroup.torsion ((V → ℤ) ⧸ LinearMap.range (Matrix.toLin' (G.lapMatrix ℤ)))

/-- **Conjecture 4.14**. The `n`-th descending invariant factor of the hypercube sandpile group
has the stated 2-adic valuation. -/
theorem conjecture_4_14 (n : ℕ) (hn : 3 ≤ n) :
    ∃ (d : ℕ) (c : Fin d → ℕ) (hnd : n ≤ d),
      (∀ i, 1 < c i) ∧
      (∀ i j, i ≤ j → c j ∣ c i) ∧
      Nonempty (sandpile (hypercube n) ≃+ (∀ i, ZMod (c i))) ∧
      padicValNat 2 (c ⟨n - 1, by omega⟩) =
        max ((Finset.Icc 1 (n - 2)).sup fun x ↦ padicValNat 2 x + x)
          (padicValNat 2 (n - 1) + n - 3) := by
  sorry

end Gao2019Sandpile
