import Mathlib

/-!
# Counting numerical semigroups by Frobenius number, multiplicity, and depth

Author: Sean Li.
Origin: [University of Minnesota Duluth REU
2022](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: S. Li, *Counting numerical semigroups by Frobenius number, multiplicity, and depth*,
Combin. Theory **3** (2023), no. 3, Paper No. 6, 29 pp.; doi:10.5070/C63362789;
arXiv:2208.14587v2.
-/

noncomputable section

namespace Li2023Counting

open scoped Topology

open scoped Classical in
/-- The number `Fr(f)` of numerical semigroups with Frobenius number `f`. -/
def frobeniusCount (f : ℕ) : ℕ :=
  let semigroups : Set (AddSubmonoid ℕ) :=
    {S | (S : Set ℕ)ᶜ.Finite ∧ FrobeniusNumber f (S : Set ℕ)}
  have hfinite : semigroups.Finite := by
    apply Set.Finite.of_injOn (f := fun S : AddSubmonoid ℕ ↦ (S : Set ℕ)ᶜ)
      (t := (Set.Iic f).powerset)
    · intro S hS
      change (S : Set ℕ)ᶜ ⊆ Set.Iic f
      have hF : f ∉ S ∧ ∀ k > f, k ∈ S := by
        simpa only [frobeniusNumber_iff, AddSubmonoid.closure_eq] using hS.2
      intro n hn
      exact le_of_not_gt (fun h ↦ hn (hF.2 n h))
    · intro S _ T _ hST
      exact SetLike.coe_injective (compl_injective hST)
    · exact (Set.finite_Iic f).powerset
  hfinite.toFinset.card

/-- **Open question** (Section 6.1; arXiv v2, p. 20). The ratio of the
even Frobenius count to the preceding odd one converges to a value strictly less than one. -/
theorem ratio_surmise :
    ∃ L : ℝ, L < 1 ∧
      Filter.Tendsto
        (fun k : ℕ ↦ (frobeniusCount (2 * k) : ℝ) /
          (frobeniusCount (2 * k - 1) : ℝ))
        Filter.atTop (𝓝 L) := by
  sorry

end Li2023Counting
