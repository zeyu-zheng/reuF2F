import Mathlib

/-!
# Crescent configurations in normed spaces

Authors: Sara Fish, Dylan King, Steven J. Miller, Eyvindur A. Palsson,
and Catherine Wahlenmayer.
Origin: [Williams College SMALL REU 2019](https://math.williams.edu/small/research-publications/).
Reference: S. Fish, D. King, S. J. Miller, E. A. Palsson, and C. Wahlenmayer, *Crescent
configurations in normed spaces*, Integers **20** (2020), Paper A96, 38 pp.; arXiv:1909.08769v2.
-/

namespace Fish2019Crescent

open Finset

/-- The distance-equality pattern agrees, after relabeling, with that of equally spaced points on
a line (Definition 2.10). -/
def IsLineLike (p : Seminorm ℝ (Fin 2 → ℝ)) (P : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ e : Fin #P ≃ P, ∀ i j k l,
    p ((e i : Fin 2 → ℝ) - e j) = p ((e k : Fin 2 → ℝ) - e l) ↔
      Nat.dist i.val j.val = Nat.dist k.val l.val

/-- No three points are collinear, no four lie on one norm-circle, and no four form a line-like
configuration (Definition 2.13). -/
def InStrongGeneralPosition (p : Seminorm ℝ (Fin 2 → ℝ))
    (P : Finset (Fin 2 → ℝ)) : Prop :=
  (∀ Q ∈ P.powersetCard 3, ¬Collinear ℝ (Q : Set (Fin 2 → ℝ))) ∧
    ∀ Q ∈ P.powersetCard 4,
      (¬∃ c : Fin 2 → ℝ, ∃ r > (0 : ℝ), ∀ x ∈ Q, p (x - c) = r) ∧
      ¬IsLineLike p Q

/-- Strong general position with exactly `n - 1` distances, one of each multiplicity from 1 to
`n - 1` (Definition 2.15). -/
def IsStrongCrescent (p : Seminorm ℝ (Fin 2 → ℝ))
    (P : Finset (Fin 2 → ℝ)) : Prop := by
  classical
  let pairs := {z ∈ P.sym2 | ¬z.IsDiag}
  let length : Sym2 (Fin 2 → ℝ) → ℝ := Sym2.lift
    ⟨fun x y ↦ p (x - y), fun x y ↦ by
      simpa only [neg_sub] using (map_neg_eq_map p (x - y)).symm⟩
  exact InStrongGeneralPosition p P ∧
    #(pairs.image length) = #P - 1 ∧
    ∀ i ≥ 1, i ≤ #P - 1 →
      ∃ r ∈ pairs.image length, #{z ∈ pairs | length z = r} = i

/-- **Conjecture 6.2** (p. 36). For each norm on the plane there is a threshold beyond which no
strong crescent configurations exist.

The threshold depends on the norm; positive definiteness turns the seminorm `p` into a norm. -/
theorem eventually_no_strong_crescents (p : Seminorm ℝ (Fin 2 → ℝ))
    (hp : ∀ x, p x = 0 → x = 0) :
    ∃ N : ℕ, ∀ P : Finset (Fin 2 → ℝ),
      N ≤ #P → ¬IsStrongCrescent p P := by
  sorry

end Fish2019Crescent
