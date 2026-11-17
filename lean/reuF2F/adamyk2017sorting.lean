import Mathlib

/-!
# Sorting permutations: Games, genomes, and cycles

Authors: K. L. M. Adamyk, E. Holmes, G. R. Mayfield, D. J. Moritz,
M. Scheepers, B. E. Tenner, and H. C. Wauck.
Origin: [Boise State University REU 2012-2013](https://arxiv.org/pdf/1410.2353v4#page=24).
Reference: K. L. M. Adamyk, E. Holmes, G. R. Mayfield, D. J. Moritz, M. Scheepers, B. E. Tenner,
and H. C. Wauck, *Sorting permutations: games, genomes, and cycles*, Discrete Math. Algorithms
Appl. (2017); doi:10.1142/S179383091750063X; arXiv:1410.2353v4.
-/

namespace Adamyk2017Sorting

/-- A signed permutation in inverse-image notation: each magnitude from `1` to `n` occurs once,
with an independent sign (Section 1). -/
abbrev SignedPermutation (n : ℕ) :=
  {row : List ℤ // (row.map Int.natAbs).Perm (List.range' 1 n)}

/-- A cdr move: reverse and negate the block between opposite pointers (Definition 5.1).
Endpoints use the orientation-aware pointer formulas, not the printed sign-insensitive sentence. -/
def CDR {n : ℕ} (a b : SignedPermutation n) : Prop :=
  ∃ (k : ℤ) (left middle right : List ℤ), 0 < k ∧ k < (n : ℤ) ∧
    ((a.val = left ++ [k] ++ middle ++ [-(k + 1)] ++ right ∧
      b.val = left ++ [k, k + 1] ++ middle.reverse.map (fun x ↦ -x) ++ right) ∨
     (a.val = left ++ [-(k + 1)] ++ middle ++ [k] ++ right ∧
      b.val = left ++ [-(k + 1), -k] ++ middle.reverse.map (fun x ↦ -x) ++ right) ∨
     (a.val = left ++ [k + 1] ++ middle ++ [-k] ++ right ∧
      b.val = left ++ middle.reverse.map (fun x ↦ -x) ++ [-(k + 1), -k] ++ right) ∨
     (a.val = left ++ [-k] ++ middle ++ [k + 1] ++ right ∧
      b.val = left ++ middle.reverse.map (fun x ↦ -x) ++ [k, k + 1] ++ right))

/-- The input decoder for Problem D.5: `n > 1`, then `n` signed initial and `n` signed terminal
entries. Fields are `encodeNat` words ending in `none`, magnitude `m` is coded `2m` (positive) or
`2m + 1` (negative), and malformed inputs decode to `none`. -/
def readInstance (word : List (Option Bool)) :
    Option ((n : ℕ) × SignedPermutation n × SignedPermutation n) := do
  let [] :: reversedFields ← pure (word.splitOn none).reverse | none
  let fields ← reversedFields.reverse.mapM fun field ↦ do
    let bits := field.filterMap id
    let value := Computability.decodeNat bits
    if bits.map some = field ∧ Computability.encodeNat value = bits then
      some value
    else none
  let n :: entries ← pure fields | none
  if 1 < n ∧ entries.length = 2 * n then
    let signed := fun code : ℕ ↦
      if code % 2 = 0 then ((code / 2 : ℕ) : ℤ) else -((code / 2 : ℕ) : ℤ)
    let initial := (entries.take n).map signed
    let terminal := (entries.drop n).map signed
    if hi : (initial.map Int.natAbs).Perm (List.range' 1 n) then
      if ht : (terminal.map Int.natAbs).Perm (List.range' 1 n) then
        some ⟨n, ⟨initial, hi⟩, ⟨terminal, ht⟩⟩
      else none
    else none
  else none

/-- **Open question** (Section 8, p. 23). Deciding whether a specified cdr fixed point
is reachable (Decision Problem D.5) is not NP-complete.

NP-completeness uses Turing machines and polynomial many-one reductions; no membership in P is
claimed. The binary input encoding is a choice, as the source leaves it unspecified, and
zero-step reachability counts. -/
theorem fixed_point_not_np_complete :
    let reachabilityLanguage : Set (List (Option Bool)) := {word |
      ∃ n : ℕ, ∃ initial terminal : SignedPermutation n,
        readInstance word = some ⟨n, initial, terminal⟩ ∧
        (¬∃ next : SignedPermutation n, CDR terminal next) ∧
        Relation.ReflTransGen CDR initial terminal}
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
    ¬(np reachabilityLanguage ∧
      ∀ language : Set (List (Option Bool)), np language →
        ∃ reduction : List (Option Bool) → List (Option Bool),
        ∃ machine : Turing.TM2ComputableInPolyTime id id reduction,
          (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
          ∀ word, word ∈ language ↔ reduction word ∈ reachabilityLanguage) := by
  sorry

end Adamyk2017Sorting
