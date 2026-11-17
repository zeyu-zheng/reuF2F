import Mathlib

/-!
# Equivalence between Restricted Non-interactive Statistical Zero-knowledge Classes

Authors: Jacob Gray, Saachi Mutreja, and Pengxiang Wang, with Eric Allender and
Harsha Tirumala.
Origin: [DIMACS REU 2022](https://archive.reu.dimacs.rutgers.edu/2022/jg1884/public_html/).
Reference: J. Gray, S. Mutreja, and P. Wang, *Equivalence between restricted non-interactive
statistical zero-knowledge classes*, DIMACS final research report (July 29, 2022).
-/

namespace Gray2022Equivalence

open Finset

/-- One output depending on at most four input coordinates, with a 16-bit table. An absent
coordinate is supplied as `false`. -/
structure FourLocalGate (m : ℕ) where
  /-- The input coordinates read by the gate, with `none` for an absent coordinate. -/
  input : Fin 4 → Option (Fin m)
  /-- The truth table of the gate on its four input bits. -/
  table : Fin 16 → Bool

/-- A finite distribution circuit, retaining the declared number of random inputs. -/
structure FourLocalCircuit where
  /-- The number of random input bits. -/
  inputs : ℕ
  /-- The number of output bits. -/
  outputs : ℕ
  /-- The gate computing each output bit. -/
  gate : Fin outputs → FourLocalGate inputs

/-- Evaluate a table in little-endian order of its four argument bits. -/
def FourLocalGate.eval {m : ℕ} (g : FourLocalGate m) (x : Fin m → Bool) : Bool :=
  let b := fun j ↦ (g.input j).elim false x
  g.table ⟨(b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat + 8 * (b 3).toNat, by
    have h₀ := Bool.toNat_le (b 0)
    have h₁ := Bool.toNat_le (b 1)
    have h₂ := Bool.toNat_le (b 2)
    have h₃ := Bool.toNat_le (b 3)
    omega⟩

/-- Evaluate every output on the same input bit vector, preserving correlations. -/
def FourLocalCircuit.eval (c : FourLocalCircuit)
    (x : Fin c.inputs → Bool) : Fin c.outputs → Bool :=
  fun j ↦ (c.gate j).eval x

/-- The base-two Shannon entropy of the circuit's output on independent uniform bits (before
Definition 5 of the full paper). Zero masses contribute zero. -/
noncomputable def FourLocalCircuit.entropy (c : FourLocalCircuit) : ℝ :=
  (∑ y : Fin c.outputs → Bool,
    Real.negMulLog
      (#{x : Fin c.inputs → Bool | c.eval x = y} /
        (2 : ℝ) ^ c.inputs)) / Real.log 2

/-- The unary encoding of a circuit: input ports, output count, and each output's four
option-coded wire indices and sixteen table bits. -/
def FourLocalCircuit.encode (c : FourLocalCircuit) : List Bool :=
  ([c.inputs, c.outputs] ++
    (List.ofFn fun j ↦
      List.ofFn (fun a ↦ ((c.gate j).input a).elim 0 (fun i ↦ i.val + 1)) ++
      List.ofFn (fun a ↦ ((c.gate j).table a).toNat)).flatten).flatMap
    (fun n ↦ List.replicate n true ++ [false])

/-- The encoding of a query list: each circuit bit is preceded by `true`, and each circuit ends
in `false`. -/
def encodeCircuitList (cs : List FourLocalCircuit) : List Bool :=
  cs.flatMap fun c ↦ c.encode.flatMap (fun b ↦ [true, b]) ++ [false]

/-- Finite-control instructions of a deterministic transducer, with two-way
read-only input, one work tape, and unreadable append-only output. -/
inductive Instruction (s : ℕ)
  | move (next : Fin (s + 1)) (inputMove workMove : Option Turing.Dir)
      (write : Option (Option Bool)) (emit : Option Bool)
  | halt

/-- A finite transition table. The input alphabet has distinct end markers, and `none` is the
blank work-tape symbol. -/
structure Machine (s : ℕ) where
  /-- The instruction for each state, input-tape symbol and work-tape symbol. -/
  transition : Fin (s + 1) → Option (Option Bool) → Option Bool → Instruction s

/-- A configuration of the transducer. Neither the input position nor the accumulated output is
visible to the control. -/
structure Configuration (s : ℕ) where
  /-- The current control state. -/
  state : Fin (s + 1) := 0
  /-- The input-head position, with `0` the left end marker. -/
  inputPosition : ℕ := 0
  /-- The work-tape head position relative to its starting cell. -/
  position : ℤ := 0
  /-- The contents of the work tape around its head. -/
  work : Turing.Tape (Option Bool) := default
  /-- The output emitted so far. -/
  output : List Bool := []
  /-- Whether the machine has halted. -/
  halted : Bool := false

/-- One transition step. -/
def Machine.step {s : ℕ} (M : Machine s) (input : List Bool)
    (c : Configuration s) : Configuration s :=
  if c.halted then c else
  let symbol := if c.inputPosition = 0 then none
    else some (input[c.inputPosition - 1]?)
  match M.transition c.state symbol c.work.head with
  | .halt => { c with halted := true }
  | .move q di dw w e =>
      let inputPosition := match di with
        | none => c.inputPosition
        | some .left => c.inputPosition - 1
        | some .right => min (c.inputPosition + 1) (input.length + 1)
      let work := match w with
        | none => c.work
        | some b => c.work.write b
      let work := match dw with
        | none => work
        | some d => work.move d
      let position := match dw with
        | none => c.position
        | some .left => c.position - 1
        | some .right => c.position + 1
      { c with
        state := q
        inputPosition := inputPosition
        position := position
        work := work
        output := c.output ++ e.toList }

/-- Execution from the left input marker and blank work/output tapes. -/
def Machine.run {s : ℕ} (M : Machine s) (input : List Bool) :
    ℕ → Configuration s
  | 0 => {}
  | t + 1 => M.step input (M.run input t)

/-- **Conjecture 4.3** (p. 4). `NISZK_L` is closed under logspace disjunctive truth-table
reductions.

Closure is expressed through the complete fixed-threshold `EA_NC0` problem (full paper,
Definition 5 and Theorem 7), with arbitrary query lists and gap queries retained; adding
independent uniform outputs justifies the signed thresholds at small output counts. -/
theorem disjunctive_logspace_closure :
    ∃ s : ℕ, ∃ M : Machine s, ∃ K d : ℕ, 0 < K ∧
      (∀ input : List Bool,
        (M.run input (K * (input.length + 1) ^ d)).halted = true ∧
          ∀ u : ℕ, u ≤ K * (input.length + 1) ^ d →
            (M.run input u).position.natAbs ≤
              K * (Nat.log 2 (input.length + 2) + 1)) ∧
      (∀ cs : List FourLocalCircuit,
        ∃ result : FourLocalCircuit,
          (M.run (encodeCircuitList cs)
              (K * ((encodeCircuitList cs).length + 1) ^ d)).output = result.encode ∧
          ((∃ c ∈ cs, (c.outputs : ℝ) - 2 < c.entropy) →
            (result.outputs : ℝ) - 2 < result.entropy) ∧
          ((∀ c ∈ cs, c.entropy < (c.outputs : ℝ) - 4) →
            result.entropy < (result.outputs : ℝ) - 4)) := by
  sorry

end Gray2022Equivalence
