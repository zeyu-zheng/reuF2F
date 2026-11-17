import Mathlib

/-!
# Investigations on Automorphism Groups of Quantum Stabilizer Codes

Author: Hanson Hao.
Origin: [Stanford SURIM
2021](https://surim.stanford.edu/publications/abstract-algebra/investigations-automorphism-groups-quantum-stabilizer-codes).
Reference: H. Hao, *Investigations on Automorphism Groups of Quantum Stabilizer Codes*,
arXiv:2109.12735.
-/

noncomputable section

namespace Hao2021Investigations

/-- Single-qubit Pauli labels. -/
inductive PauliLabel : Type
  | I | X | Y | Z

namespace PauliLabel

/-- The binary `X` support of a Pauli label. -/
def xBit : PauliLabel → ZMod 2
  | I => 0
  | X => 1
  | Y => 1
  | Z => 0

/-- The binary `Z` support of a Pauli label. -/
def zBit : PauliLabel → ZMod 2
  | I => 0
  | X => 0
  | Y => 1
  | Z => 1

/-- The phase of a label in the normal form `i^phase X^x Z^z`, so that `Y = i X Z`. -/
def phase : PauliLabel → ZMod 4
  | I => 0
  | X => 0
  | Y => 1
  | Z => 0

end PauliLabel

/-- A finite Pauli word in the normal form `i^phase * ∏_j X_j^{x_j} Z_j^{z_j}`. Stabilizer
membership uses the exact phase, weak automorphism membership only the binary supports. -/
structure PauliWord (n : ℕ) where
  /-- The exponent of the phase factor `i`. -/
  phase : ZMod 4
  /-- The exponent `x_j` of `X_j` at each qubit. -/
  x : Fin n → ZMod 2
  /-- The exponent `z_j` of `Z_j` at each qubit. -/
  z : Fin n → ZMod 2

namespace PauliWord

/-- The identity Pauli word. -/
def one (n : ℕ) : PauliWord n where
  phase := 0
  x := fun _ ↦ 0
  z := fun _ ↦ 0

/-- Multiplication of Pauli words in the normal form `i^a X^u Z^v`. -/
def mul {n : ℕ} (p q : PauliWord n) : PauliWord n where
  phase := p.phase + q.phase +
    ∑ i : Fin n, if p.z i = 1 ∧ q.x i = 1 then (2 : ZMod 4) else 0
  x := fun i ↦ p.x i + q.x i
  z := fun i ↦ p.z i + q.z i

/-- The positive tensor word attached to a function of Pauli labels. -/
def ofLabels {n : ℕ} (f : Fin n → PauliLabel) : PauliWord n where
  phase := ∑ i : Fin n, (f i).phase
  x := fun i ↦ (f i).xBit
  z := fun i ↦ (f i).zBit

/-- The `S_n` action on `G_n` permuting tensor factors. The phase is unchanged and supports are
pulled back by `σ⁻¹`. -/
def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : PauliWord n) : PauliWord n where
  phase := p.phase
  x := fun i ↦ p.x (σ.symm i)
  z := fun i ↦ p.z (σ.symm i)

end PauliWord

open PauliLabel

/-- The ten positive Pauli-word generators of the `[[11,1,5]]` code (Section 2.2.7,
Question 2.16). -/
def q216Generator : Fin 10 → PauliWord 11
  | ⟨0, _⟩ => PauliWord.ofLabels ![Z, Z, Z, Z, Z, Z, I, I, I, I, I]
  | ⟨1, _⟩ => PauliWord.ofLabels ![X, X, X, X, X, X, I, I, I, I, I]
  | ⟨2, _⟩ => PauliWord.ofLabels ![I, I, I, Z, X, Y, Y, Y, Y, X, Z]
  | ⟨3, _⟩ => PauliWord.ofLabels ![I, I, I, X, Y, Z, Z, Z, Z, Y, X]
  | ⟨4, _⟩ => PauliWord.ofLabels ![Z, Y, X, I, I, I, Z, Y, X, I, I]
  | ⟨5, _⟩ => PauliWord.ofLabels ![X, Z, Y, I, I, I, X, Z, Y, I, I]
  | ⟨6, _⟩ => PauliWord.ofLabels ![I, I, I, Z, Y, X, X, Y, Z, I, I]
  | ⟨7, _⟩ => PauliWord.ofLabels ![I, I, I, X, Z, Y, Z, X, Y, I, I]
  | ⟨8, _⟩ => PauliWord.ofLabels ![Z, X, Y, I, I, I, Z, Z, Z, X, Y]
  | _ => PauliWord.ofLabels ![Y, Z, X, I, I, I, Y, Y, Y, Z, X]

/-- The ordered product of a finite family of Pauli words selected by binary coefficients. -/
def pauliProduct {m n : ℕ} (g : Fin m → PauliWord n) (coeff : Fin m → ZMod 2) :
    PauliWord n :=
  (List.finRange m).foldl
    (fun acc j ↦ if coeff j = 0 then acc else PauliWord.mul acc (g j))
    (PauliWord.one n)

/-- **Question 2.16** (with its preceding explicit suspicion). The listed `[[11,1,5]]` code has
trivial strong and weak automorphism groups.

The generator tests are Corollaries 2.3 and 2.8; for these Hermitian stabilizer elements,
equality of binary supports is equality up to sign. -/
theorem question_2_16_strong_and_weak_automorphism_groups_trivial :
    (∀ σ : Equiv.Perm (Fin 11),
      (∀ j : Fin 10, ∃ coeff : Fin 10 → ZMod 2,
        PauliWord.permute σ (q216Generator j) = pauliProduct q216Generator coeff) ↔ σ = 1) ∧
    (∀ σ : Equiv.Perm (Fin 11),
      (∀ j : Fin 10, ∃ coeff : Fin 10 → ZMod 2,
        (PauliWord.permute σ (q216Generator j)).x = (pauliProduct q216Generator coeff).x ∧
          (PauliWord.permute σ (q216Generator j)).z = (pauliProduct q216Generator coeff).z) ↔
        σ = 1) := by
  sorry

end Hao2021Investigations
