import Mathlib

/-!
# Simple reductions to circuit minimization: DIMACS REU Report

Authors: Vishal Ramesh, Sasha Sami, and Noah Singer.
Origin: [DIMACS REU 2021](https://archive.reu.dimacs.rutgers.edu/2021/vr342/public_html/).
Reference: V. Ramesh, S. Sami, and N. Singer, *Simple reductions to circuit minimization: DIMACS
REU Report* (July 2021), 10 pp.
-/

noncomputable section

namespace Ramesh2021Simple

/-- An internal De Morgan gate, whose predecessors are variables, free constants or earlier
internal gates. -/
inductive Gate (m previous : ℕ)
  | neg : ((Fin m ⊕ Bool) ⊕ Fin previous) → Gate m previous
  | conj : ((Fin m ⊕ Bool) ⊕ Fin previous) →
      ((Fin m ⊕ Bool) ⊕ Fin previous) → Gate m previous
  | disj : ((Fin m ⊕ Bool) ⊕ Fin previous) →
      ((Fin m ⊕ Bool) ⊕ Fin previous) → Gate m previous

/-- A finite acyclic single-output circuit, counting only its internal gates. -/
structure Circuit (m : ℕ) where
  /-- The number of internal gates. -/
  gates : ℕ
  /-- Each gate, whose inputs are variables, constants or earlier gates. -/
  gate : (i : Fin gates) → Gate m i.val
  /-- The output: a variable, a Boolean constant or a gate. -/
  output : (Fin m ⊕ Bool) ⊕ Fin gates

/-- The value of an internal gate, recursively evaluating its earlier predecessors. -/
def Circuit.gateValue {m : ℕ} (C : Circuit m) (x : Fin m → Bool)
    (i : Fin C.gates) : Bool :=
  let value : ((Fin m ⊕ Bool) ⊕ Fin i.val) → Bool := fun w ↦
    match w with
    | .inl (.inl j) => x j
    | .inl (.inr b) => b
    | .inr j => C.gateValue x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  match C.gate i with
  | .neg a => !(value a)
  | .conj a b => value a && value b
  | .disj a b => value a || value b
termination_by i.val

/-- The Boolean function computed by the circuit, with zero-cost output selection. -/
def Circuit.eval {m : ℕ} (C : Circuit m) (x : Fin m → Bool) : Bool :=
  match C.output with
  | .inl (.inl j) => x j
  | .inl (.inr b) => b
  | .inr j => C.gateValue x j

/-- The minimum internal-gate count `size(f)` among circuits computing `f` (Section 1). -/
def circuitSize {m : ℕ} (f : (Fin m → Bool) → Bool) : ℕ :=
  sInf {s : ℕ | ∃ C : Circuit m, C.gates = s ∧ C.eval = f}

/-- **Conjecture 3.6**. For all sufficiently large truth tables, the expected minimum circuit
size is nondecreasing throughout the stated bias interval.

Size is the De Morgan gate count with free constant inputs, the contextual GII/MW/Wegener
reading; the report does not specify constant costs. -/
theorem conjecture_3_6 :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ p q : ℝ, 1 / 50 ≤ p → p < q → q ≤ 1 / 2 →
        (∑ f : ((Fin m → Bool) → Bool),
          (circuitSize f : ℝ) *
            ∏ x : (Fin m → Bool), if f x then p else 1 - p) ≤
        (∑ f : ((Fin m → Bool) → Bool),
          (circuitSize f : ℝ) *
            ∏ x : (Fin m → Bool), if f x then q else 1 - q) := by
  sorry

end Ramesh2021Simple
