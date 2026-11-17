import Mathlib

/-!
# Optimally Solving Colored Generalized Sliding-Tile Puzzles: Complexity and Bounds

Authors: Marcus Gozon and Jingjin Yu.
Origin: [DIMACS REU 2023](https://archive.reu.dimacs.rutgers.edu/2023/mg2010/public_html/).
Reference: M. Gozon and J. Yu, *Optimally solving colored generalized sliding-tile puzzles:
complexity and bounds*, preprint (2024); arXiv:2410.14947v1.
-/

namespace Gozon2026Optimally

/-- A complete injective placement of the labeled tiles on the full rectangle. Labels and
row/column coordinates are zero-based. -/
abbrev Configuration (rows columns tiles : ℕ) :=
  Fin tiles ↪ Fin rows × Fin columns

/-- The single-escort GSTP instance with both complete placements as input (Section 2.1). The
missing cell is the escort, not an additional labeled tile. -/
structure Puzzle where
  /-- The number of rows of the board. -/
  rows : ℕ
  /-- The number of columns of the board. -/
  columns : ℕ
  /-- The number of labeled tiles. -/
  tiles : ℕ
  rows_pos : 0 < rows
  columns_pos : 0 < columns
  one_escort : rows * columns = tiles + 1
  /-- The initial placement of the tiles. -/
  initial : Configuration rows columns tiles
  /-- The goal placement of the tiles. -/
  goal : Configuration rows columns tiles

/-- One synchronous unit step or wait for every tile, with no head-on exchange and
nonperpendicular corner-following. Injectivity enforces the no-meet constraint. -/
def Move {rows columns tiles : ℕ}
    (a b : Configuration rows columns tiles) : Prop :=
  let d := fun i : Fin tiles ↦
    (((b i).1.val : ℤ) - ((a i).1.val : ℤ),
      ((b i).2.val : ℤ) - ((a i).2.val : ℤ))
  (∀ i, d i = (0, 0) ∨ d i = (1, 0) ∨ d i = (-1, 0) ∨
    d i = (0, 1) ∨ d i = (0, -1)) ∧
  ∀ i j, i ≠ j →
    ¬(a i = b j ∧ b i = a j) ∧
    (b i = a j → (d i).1 * (d j).1 + (d i).2 * (d j).2 ≠ 0)

/-- The binary input: rows, columns, tile count, blank count (exactly one), positive `K`, then
every initial and goal row-major cell index in label order. Each natural field writes each
`encodeNat` bit `b` as `[true, b]` and ends in `false`, and malformed inputs reject. -/
def readPuzzle (word : List Bool) : Option (Puzzle × ℕ) := do
  let rec /-- Reads one natural-number field: the payload bits before the terminating `false`. -/
    readBits : List Bool → Option (List Bool × List Bool)
    | false :: rest => some ([], rest)
    | true :: b :: rest => do
        let (bits, rest) ← readBits rest
        some (b :: bits, rest)
    | _ => none
  let readNat := fun word : List Bool ↦ do
    let (bits, rest) ← readBits word
    let n := Computability.decodeNat bits
    if Computability.encodeNat n = bits then some (n, rest) else none
  let (rows, rest) ← readNat word
  let (columns, rest) ← readNat rest
  let (tiles, rest) ← readNat rest
  let (escorts, rest) ← readNat rest
  let (K, rest) ← readNat rest
  if hr : 0 < rows then
    if hc : 0 < columns then
      if he : rows * columns = tiles + 1 then
        if escorts = 1 ∧ 0 < K then
          let rec /-- Reads `count` cell indices, rejecting any outside the board. -/
            readPositions : (count : ℕ) → List Bool →
              Option ((Fin count → Fin rows × Fin columns) × List Bool)
            | 0, w => some ((fun i ↦ Fin.elim0 i), w)
            | count + 1, w => do
              let (index, w) ← readNat w
              if h : index < rows * columns then
                let q : Fin rows × Fin columns :=
                  (⟨index / columns, (Nat.div_lt_iff_lt_mul hc).mpr h⟩,
                    ⟨index % columns, Nat.mod_lt _ hc⟩)
                let (tail, w) ← readPositions count w
                some (Fin.cases q tail, w)
              else none
          let (initial, rest) ← readPositions tiles rest
          let (goal, rest) ← readPositions tiles rest
          if rest = [] then
            if hi : Function.Injective initial then
              if hg : Function.Injective goal then
                some ({ rows, columns, tiles, rows_pos := hr, columns_pos := hc,
                        one_escort := he, initial := ⟨initial, hi⟩, goal := ⟨goal, hg⟩ }, K)
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- The one-escort makespan deadline language: all tiles reach the supplied goal at a common
`T ≤ K`. Malformed inputs reject, and `T = 0` is allowed although `K` is positive. -/
def MOGSTP : Set (List Bool) :=
  {word | ∃ (g : Puzzle) (K : ℕ),
    readPuzzle word = some (g, K) ∧
    ∃ T ≤ K, ∃ path : Fin (T + 1) → Configuration g.rows g.columns g.tiles,
      path 0 = g.initial ∧ path (Fin.last T) = g.goal ∧
      ∀ t : Fin T, Move (path t.castSucc) (path t.succ)}

/-- **Open question** (Section 5, p. 16). The full rectangular single-escort MOGSTP deadline
language is NP-hard.

MOGSTP is as in M. Gozon and J. Yu, arXiv:2312.10887v1, Section 3.1. Rectangles include
one-row and one-column boards and the zero-tile 1x1 board; no NP membership, other escort count
or feasibility promise is asserted. Goals are arbitrary complete input placements; the
successor's ordered-goal wording is read in its algorithmic scope, not as a deadline-preserving
normalization. -/
theorem single_escort_np_hard :
    let pairCode := (Computability.encodingProd
      (Computability.encodingList Bool)
      (Computability.encodingList Bool)).encode
    let np : Set (List Bool) → Prop := fun language ↦
      ∃ verifier : (List Bool × List Bool) → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime pairCode
          Computability.encodeBool verifier,
        (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
        ∃ bound : Polynomial ℕ, ∀ input : List Bool,
          input ∈ language ↔ ∃ certificate : List Bool,
            certificate.length ≤ bound.eval input.length ∧
            verifier (input, certificate) = true
    ∀ language : Set (List Bool), np language →
      ∃ reduction : List Bool → List Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime id id reduction,
        (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
        ∀ word, word ∈ language ↔ reduction word ∈ MOGSTP := by
  sorry

end Gozon2026Optimally
