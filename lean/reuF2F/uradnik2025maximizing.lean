import Mathlib

/-!
# Maximizing Truth Learning in a Social Network is NP-hard

Authors: Filip Uradnik, Amanda Wang, and Jie Gao.
Origin: [DIMACS REU 2024](https://dimacs.rutgers.edu/reu-participant-details/uradnik-filip-2024).
Reference: F. Uradnik, A. Wang, and J. Gao, *Maximizing Truth Learning in a Social Network is
NP-hard*, Proc. AAMAS 2025 (2025), 2078-2086; arXiv:2502.12704v1.
-/

noncomputable section

namespace Uradnik2025Maximizing

/-- A directed network with a common truth prior and private-signal accuracy (Definition 2.1).
The source's parameter domain is enforced by the decoder `readProblem`. -/
structure SocialNetwork where
  /-- The number of agents. -/
  size : ℕ
  /-- The directed network on the agents. -/
  graph : Digraph (Fin size)
  /-- The common prior probability of the truth state. -/
  prior : ℚ
  /-- The probability that each private signal matches the truth. -/
  accuracy : ℚ

open scoped Classical in
/-- The expected fraction of correct announcements in a fixed time-to-vertex ordering, with
fresh fair ties (Definition 2.2; Bayesian rule, p. 2080). The recursion stores unannounced
coordinates as `false` padding. -/
def learningRate (N : SocialNetwork) (order : Equiv.Perm (Fin N.size)) : ℚ :=
  let rec
    /-- The joint probability of the truth, the signals and the padded announcements
    after the first `t` turns. -/
    joint : ℕ → Bool → (Fin N.size → Bool) → (Fin N.size → Bool) → ℚ
    | 0 => fun b s a ↦
      if a = (fun _ ↦ false) then
        (if b then N.prior else 1 - N.prior) *
          ∏ u, if s u = b then N.accuracy else 1 - N.accuracy
      else 0
    | t + 1 =>
      let previous := joint t
      if h : t < N.size then
        let v := order ⟨t, h⟩
        fun b s a ↦
          let weight := fun truth : Bool ↦
            ∑ signals : Fin N.size → Bool, ∑ actions : Fin N.size → Bool,
              if signals v = s v ∧
                  (∀ u : Fin N.size, N.graph.Adj u v →
                    (order.symm u).val < t → actions u = a u) then
                previous truth signals actions
              else 0
          previous b s (Function.update a v false) *
            (if weight false < weight true then (if a v then 1 else 0)
             else if weight true < weight false then (if a v then 0 else 1)
             else (1 / 2 : ℚ))
      else previous
  (∑ b : Bool, ∑ s : Fin N.size → Bool, ∑ a : Fin N.size → Bool,
    joint N.size b s a * ∑ v : Fin N.size, (if a v = b then 1 else 0 : ℚ)) /
      (N.size : ℚ)

/-- The canonical binary input: seven escaped binary-natural fields (size, then
numerator/denominator for prior, accuracy and error tolerance), followed by the row-major
adjacency bits. A digit is `true` then the digit and `false` ends a field; noncanonical,
malformed and out-of-domain inputs are rejected. -/
def readProblem (word : List Bool) : Option (SocialNetwork × ℚ) := do
  let rec
    /-- Read one escaped binary word, returning its digits and the remaining input. -/
    field : List Bool → Option (List Bool × List Bool)
    | false :: rest => some ([], rest)
    | true :: bit :: rest => do
      let (bits, tail) ← field rest
      pure (bit :: bits, tail)
    | _ => none
  let readNat := fun input ↦ do
    let (bits, rest) ← field input
    let value := Computability.decodeNat bits
    if Computability.encodeNat value = bits then some (value, rest) else none
  let (n, rest) ← readNat word
  let (qn, rest) ← readNat rest
  let (qd, rest) ← readNat rest
  let (pn, rest) ← readNat rest
  let (pd, rest) ← readNat rest
  let (en, rest) ← readNat rest
  let (ed, edges) ← readNat rest
  let q : ℚ := (qn : ℚ) / (qd : ℚ)
  let p : ℚ := (pn : ℚ) / (pd : ℚ)
  let ε : ℚ := (en : ℚ) / (ed : ℚ)
  if 0 < n ∧ edges.length = n * n ∧
      0 < qd ∧ 0 < pd ∧ 0 < ed ∧
      Nat.Coprime qn qd ∧ Nat.Coprime pn pd ∧ Nat.Coprime en ed ∧
      0 < q ∧ q < 1 ∧ (1 / 2 : ℚ) < p ∧ p < 1 ∧
      0 < ε ∧ ε < 1 then
    some (⟨n, Digraph.mk' (fun u v ↦ edges.getD (u.val * n + v.val) false),
      q, p⟩, ε)
  else none

/-- Network learning for the fixed Bayesian rule: some ordering chosen before any random draws
attains the inclusive average-learning threshold (Definition 2.5). -/
def networkLearning : Set (List Bool) :=
  {word | ∃ (N : SocialNetwork) (ε : ℚ),
    readProblem word = some (N, ε) ∧
      ∃ order : Equiv.Perm (Fin N.size), 1 - ε ≤ learningRate N order}

/-- **Unnumbered conjecture** (Section 6, Future Work, p. 2085). Bayesian Network Learning is
not in NP.

The rule, implicit in the paragraph, is taken as the Bayesian variant of Definition 2.5 with
rational binary inputs; Definition 2.5 controls the threshold despite the reduction's
epsilon-complement mismatch. -/
theorem bayesian_network_learning_not_in_np :
    let pairCode := (Computability.encodingProd
      (Computability.encodingList Bool) (Computability.encodingList Bool)).encode
    ¬(∃ verifier : (List Bool × List Bool) → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime pairCode
          Computability.encodeBool verifier,
        (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
        ∃ bound : Polynomial ℕ, ∀ input : List Bool,
          input ∈ networkLearning ↔ ∃ certificate : List Bool,
            certificate.length ≤ bound.eval input.length ∧
            verifier (input, certificate) = true) := by
  sorry

end Uradnik2025Maximizing
