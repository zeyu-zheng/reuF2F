import Mathlib

/-!
# On extending type B parking spaces

Authors: Anthony Adams, Joshua Dorsam, Lily Levitsky, and Megan Mann.
Origin: [MathILy-EST 2025](https://mathily.org/mathilyest/past.html).
Reference: A. Adams, J. Dorsam, L. Levitsky, and M. Mann, *On extending type B parking spaces*,
preprint (2026), 14 pp.; arXiv:2601.18090v1.
-/

noncomputable section

namespace Adams2026Extending

/-- The signed symmetric group in row-sign coordinates, with the permutation acting on signs by
`s i ↦ s (w.symm i)` (Definition 2.12). -/
abbrev B (n : ℕ) :=
  SemidirectProduct (Fin n → Units ℤ) (Equiv.Perm (Fin n)) mulAutArrow

/-- The inclusion fixing the last signed letter: append sign `+1` and extend the permutation by
fixing `Fin.last n` (Introduction). -/
def inclusion (n : ℕ) : MonoidHom (B n) (B (n + 1)) :=
  let signs : MonoidHom (Fin n → Units ℤ) (Fin (n + 1) → Units ℤ) :=
    { toFun := fun s ↦ Fin.lastCases 1 s
      map_one' := by
        funext i
        cases i using Fin.lastCases <;> simp
      map_mul' := by
        intro s t
        funext i
        cases i using Fin.lastCases <;> simp }
  let perms := Equiv.Perm.extendDomainHom (finSuccAboveEquiv (Fin.last n))
  SemidirectProduct.map signs perms fun w ↦ by
    apply MonoidHom.ext
    intro s
    funext i
    change Fin.lastCases (motive := fun _ ↦ Units ℤ) 1 (fun j ↦ s (w.symm j)) i =
      Fin.lastCases (motive := fun _ ↦ Units ℤ) 1 s ((perms w).symm i)
    have hcast (v : Equiv.Perm (Fin n)) (j : Fin n) :
        perms v j.castSucc = (v j).castSucc := by
      simpa only [perms, Equiv.Perm.extendDomainHom_apply,
        finSuccAboveEquiv_apply, Fin.succAbove_last] using
        v.extendDomain_apply_image (finSuccAboveEquiv (Fin.last n)) j
    have hlast (v : Equiv.Perm (Fin n)) : perms v (Fin.last n) = Fin.last n := by
      exact v.extendDomain_apply_not_subtype (finSuccAboveEquiv (Fin.last n))
        (by simp)
    change Fin.lastCases (motive := fun _ ↦ Units ℤ) 1 (fun j ↦ s (w.symm j)) i =
      Fin.lastCases (motive := fun _ ↦ Units ℤ) 1 s (perms w.symm i)
    cases i using Fin.lastCases with
    | last => simp only [hlast, Fin.lastCases_last]
    | cast j => simp only [hcast, Fin.lastCases_castSucc]

/-- The signed action on `ZMod m` coordinates, where row sign `s i` multiplies coordinate
`x (w.symm i)` (Definitions 3.1 and 3.3). -/
@[instance_reducible]
def signedAction (m n : ℕ) : MulAction (B n) (Fin n → ZMod m) where
  smul g x i := ((g.left i : ℤ) : ZMod m) * x (g.right.symm i)
  one_smul x := by
    funext i
    change ((1 : ℤ) : ZMod m) * x i = x i
    simp
  mul_smul g h x := by
    funext i
    change (((g.left i * h.left (g.right.symm i) : Units ℤ) : ℤ) : ZMod m) *
        x (h.right.symm (g.right.symm i)) =
      ((g.left i : ℤ) : ZMod m) *
        (((h.left (g.right.symm i) : ℤ) : ZMod m) *
          x (h.right.symm (g.right.symm i)))
    simp only [Units.val_mul, Int.cast_mul, mul_assoc]

/-- **Conjecture 1.1**. For every positive modulus and rank, the complex linearization of the
signed action extends along the last-letter inclusion.

Equality on this canonical space is equivalent, by linear transport, to the source's
isomorphic restriction; the extension need not permute this basis. -/
theorem conjecture_1_1 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    letI := signedAction m n
    ∃ ρ : Representation ℂ (B (n + 1)) (MonoidAlgebra ℂ (Fin n → ZMod m)),
      ρ.comp (inclusion n) =
        Representation.ofMulAction ℂ (B n) (Fin n → ZMod m) := by
  sorry

end Adams2026Extending
