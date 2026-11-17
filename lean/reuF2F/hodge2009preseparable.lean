import Mathlib

/-!
# Preseparable Extensions of Multidimensional Preferences

Authors: Jonathan K. Hodge, Mark Krines, and Jennifer Lahr.
Origin: [Grand Valley State University REU
2007](https://www.gvsu.edu/mathreu/research-and-publications-at-previous-reu-programs-5.htm).
Reference: J. K. Hodge, M. Krines, and J. Lahr, *Preseparable extensions of multidimensional
preferences*, Order **26** (2009), 125–147; doi:10.1007/s11083-009-9112-1.
-/

namespace Hodge2009Preseparable

/-- Separability: the strict preference between outcomes on `S` is independent of the fixed
outcome outside `S` (Definition 3). -/
def Separable {n : ℕ} (order : LinearOrder (Fin n → Bool))
    (S : Finset (Fin n)) : Prop :=
  ∀ a b u v : Fin n → Bool,
    order.lt (fun i ↦ if i ∈ S then a i else u i)
      (fun i ↦ if i ∈ S then b i else u i) →
    order.lt (fun i ↦ if i ∈ S then a i else v i)
      (fun i ↦ if i ∈ S then b i else v i)

/-- A character is admissible if some total order has exactly its listed separable sets
(p. 128). -/
def Admissible {n : ℕ} (C : Finset (Finset (Fin n))) : Prop :=
  ∃ order : LinearOrder (Fin n → Bool),
    ∀ S : Finset (Fin n), S ∈ C ↔ Separable order S

/-- The explicit finite-family input: a binary field for `n` followed by one `n`-bit incidence row
per listed subset, each field terminated by `none`. Malformed input is rejected, and the family
must contain the empty and full sets. -/
def readCharacter (word : List (Option Bool)) :
    Option ((n : ℕ) × Finset (Finset (Fin n))) := do
  let [] :: reversedFields ← pure (word.splitOn none).reverse | none
  let header :: rows ← pure reversedFields.reverse | none
  let headerBits := header.filterMap id
  let n := Computability.decodeNat headerBits
  if headerBits.map some = header ∧ Computability.encodeNat n = headerBits then
    let subsets ← rows.mapM fun row ↦ do
      let bits := row.filterMap id
      if bits.map some = row ∧ bits.length = n then
        some ({i | bits.getD i.val false} : Finset (Fin n))
      else none
    let C := subsets.toFinset
    if (∅ : Finset (Fin n)) ∈ C ∧ Finset.univ ∈ C then some ⟨n, C⟩ else none
  else none

/-- **Open question** (Section 7, pp. 146–147). Deciding character admissibility is
NP-hard.

The open-question paragraph gives the expected NP-hard direction. The binary domain is a reading
of the binary defaults in Sections 5–6, inputs are explicitly listed families rather than
full-power-set tables, and the conclusion is many-one NP-hardness only. -/
theorem character_admissibility_np_hard :
    let targetLanguage : Set (List (Option Bool)) := {word |
      ∃ (n : ℕ) (C : Finset (Finset (Fin n))),
        readCharacter word = some ⟨n, C⟩ ∧ Admissible C}
    let pairCode := (Computability.encodingProd
      (Computability.encodingList (Option Bool))
      (Computability.encodingList Bool)).encode
    let np : Set (List (Option Bool)) → Prop := fun language ↦
      ∃ verifier : (List (Option Bool) × List Bool) → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime pairCode
          Computability.encodeBool verifier,
        (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
        ∃ bound : Polynomial ℕ, ∀ input : List (Option Bool),
          input ∈ language ↔ ∃ certificate : List Bool,
            certificate.length ≤ bound.eval input.length ∧
            verifier (input, certificate) = true
    ∀ language : Set (List (Option Bool)), np language →
      ∃ reduction : List (Option Bool) → List (Option Bool),
      ∃ machine : Turing.TM2ComputableInPolyTime id id reduction,
        (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
        ∀ word, word ∈ language ↔ reduction word ∈ targetLanguage := by
  sorry

end Hodge2009Preseparable
