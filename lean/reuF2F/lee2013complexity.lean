import Mathlib

/-!
# The complexity class PDQP

Author: Mitchell Lee.
Origin: [MIT SPUR 2013](https://math.mit.edu/research/undergraduate/spur/documents/2013Lee.pdf).
Reference: M. Lee, *The complexity class PDQP*, MIT SPUR final paper (2013); see also
S. Aaronson, A. Bouland, J. Fitzsimons, and M. Lee, *The space "just above" BQP*,
arXiv:1412.6507v1 (2014).
-/

noncomputable section

namespace Lee2013Complexity

open scoped ENNReal Polynomial

/-- The two single-qubit gates of the fixed finite gate basis (Section 8.2, p. 14). -/
inductive OneQubitGate
  /-- The real rotation `exp(i cos⁻¹(3/5) Y)`, with entries `4/5` and `±3/5`. -/
  | rotation
  /-- The phase gate `diag(1, i)`. -/
  | phase
  deriving DecidableEq

/-- The unitary matrix of a single-qubit gate: the rotation with entries `4/5`, `±3/5`, or the
phase gate `diag(1, i)` (Section 8.2, p. 14). -/
def OneQubitGate.matrix : OneQubitGate → Matrix.unitaryGroup Bool ℂ
  | .rotation =>
      ⟨Matrix.of fun x y ↦ if x = y then 4 / 5 else if x then 3 / 5 else -3 / 5, by
        rw [Matrix.mem_unitaryGroup_iff']
        ext x y
        cases x <;> cases y <;>
          norm_num [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
            map_ofNat]⟩
  | .phase =>
      ⟨Matrix.diagonal fun b ↦ if b then Complex.I else 1, by
        rw [Matrix.mem_unitaryGroup_iff']
        ext x y
        cases x <;> cases y <;>
          simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose]⟩

/-- A gate of a circuit on `n` wires: a single-qubit gate or a controlled-NOT (Sections 2.1
and 8.2). -/
inductive Gate (n : ℕ)
  /-- A single-qubit gate of the basis applied to one wire. -/
  | single (kind : OneQubitGate) (wire : Fin n)
  /-- A controlled-NOT gate with distinct control and target wires. -/
  | controlledNot (control target : Fin n) (different : control ≠ target)

/-- The unitary matrix of a gate acting on its wires (Section 2.1). -/
def Gate.matrix {n : ℕ} : Gate n → Matrix.unitaryGroup (Fin n → Bool) ℂ
  | .single kind wire =>
      let e := Equiv.funSplitAt wire Bool
      let u := Matrix.kronecker kind.matrix.val
        (1 : Matrix ({j : Fin n // j ≠ wire} → Bool) ({j : Fin n // j ≠ wire} → Bool) ℂ)
      have hu : u ∈ Matrix.unitaryGroup _ ℂ :=
        Matrix.kronecker_mem_unitary kind.matrix.property (one_mem _)
      ⟨u.submatrix e e, by
        rw [Matrix.mem_unitaryGroup_iff'] at hu ⊢
        change u.conjTranspose * u = 1 at hu
        change (u.submatrix e e).conjTranspose * u.submatrix e e = 1
        rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ e e e, hu,
          Matrix.submatrix_one_equiv]⟩
  | .controlledNot c t h =>
      let f : (Fin n → Bool) → (Fin n → Bool) := fun x ↦ Function.update x t (xor (x c) (x t))
      have hf : Function.Involutive f := by
        intro x
        funext i
        by_cases hi : i = t
        · subst i
          simp [f, h]
        · simp [f, hi]
      let e := hf.toPerm
      ⟨e.permMatrix ℂ, by
        rw [Matrix.mem_unitaryGroup_iff']
        change (e.permMatrix ℂ).conjTranspose * e.permMatrix ℂ = 1
        rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
        simp⟩

/-- A query to `Q_P`: a circuit given by its width and its unitary blocks, each followed by a
measurement of a set of wires (Section 4). -/
structure Query where
  /-- The number of qubits. -/
  width : ℕ
  /-- The gate lists, each followed by the set of measured wires. -/
  blocks : List (List (Gate width) × Finset (Fin width))

/-- Parse a counted list of gate instructions. -/
private def Query.decodeGates (width : ℕ) :
    ℕ → List ℕ → Option (List (Gate width) × List ℕ)
  | 0, fields => some ([], fields)
  | n + 1, 0 :: wire :: 0 :: tail => do
      if h : wire < width then
        let (gs, rest) ← Query.decodeGates width n tail
        return (.single .rotation ⟨wire, h⟩ :: gs, rest)
      else none
  | n + 1, 1 :: wire :: 0 :: tail => do
      if h : wire < width then
        let (gs, rest) ← Query.decodeGates width n tail
        return (.single .phase ⟨wire, h⟩ :: gs, rest)
      else none
  | n + 1, 2 :: c :: t :: tail => do
      if hc : c < width then
        if ht : t < width then
          if hct : c ≠ t then
            let (gs, rest) ← Query.decodeGates width n tail
            return (.controlledNot ⟨c, hc⟩ ⟨t, ht⟩
              (fun h ↦ hct (congrArg Fin.val h)) :: gs, rest)
          else none
        else none
      else none
  | _, _ => none

/-- Parse a counted list of blocks, each a gate list with a set of measured wires. -/
private def Query.decodeBlocks (width : ℕ) :
    ℕ → List ℕ → Option (List (List (Gate width) × Finset (Fin width)) × List ℕ)
  | 0, fields => some ([], fields)
  | n + 1, gateCount :: fields => do
      let (gates, afterGates) ← Query.decodeGates width gateCount fields
      let count :: afterCount := afterGates | none
      if (afterCount.take count).length = count then
        let measured ← (afterCount.take count).mapM
          (fun k ↦ if h : k < width then some (⟨k, h⟩ : Fin width) else none)
        let (blocks, rest) ← Query.decodeBlocks width n (afterCount.drop count)
        return ((gates, measured.toFinset) :: blocks, rest)
      else none
  | _, _ => none

/-- The explicit finite-alphabet encoding of a query by unary fields for the width, the block
count, the gate tags and wires, and the measured wires.

Gates come from the fixed basis, so no amplitudes or succinct register descriptions occur. -/
def Query.encoding : Computability.Encoding Query (Option Bool) :=
  -- Self-delimited unary fields.
  let fieldEncoding : Computability.Encoding (List ℕ) (Option Bool) :=
    let encode : List ℕ → List (Option Bool) :=
      List.flatMap (fun n ↦ List.replicate n (some true) ++ [none])
    let step : Option Bool → Option (List ℕ) → Option (List ℕ)
      | none, rest => (List.cons 0) <$> rest
      | some true, rest => rest.bind (fun ns ↦ match ns with
          | n :: tail => some ((n + 1) :: tail)
          | _ => none)
      | some false, _ => none
    let decode : List (Option Bool) → Option (List ℕ) :=
      fun word ↦ word.foldr step (some [])
    have readPrefix (n : ℕ) (w : List (Option Bool)) :
        decode (List.replicate n (some true) ++ none :: w) =
          (List.cons n) <$> decode w := by
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [List.replicate_succ, List.cons_append]
        change step (some true)
          (decode (List.replicate n (some true) ++ none :: w)) = _
        rw [ih]
        cases decode w <;> rfl
    ⟨encode, decode, by
      intro ns
      induction ns with
      | nil => rfl
      | cons n ns ih =>
        change decode ((List.replicate n (some true) ++ [none]) ++ encode ns) = _
        rw [List.append_assoc]
        change decode (List.replicate n (some true) ++ none :: encode ns) = _
        rw [readPrefix, ih]
        rfl⟩
  let gateFields {n : ℕ} (g : Gate n) : List ℕ := match g with
    | .single .rotation wire => [0, wire.val, 0]
    | .single .phase wire => [1, wire.val, 0]
    | .controlledNot c t _ => [2, c.val, t.val]
  let blockFields {n : ℕ} (b : List (Gate n) × Finset (Fin n)) : List ℕ :=
    b.1.length :: b.1.flatMap gateFields ++
      b.2.card :: ((b.2.sort (· ≤ ·)).map Fin.val)
  let encode (q : Query) : List (Option Bool) :=
    fieldEncoding.encode (q.width :: q.blocks.length :: q.blocks.flatMap blockFields)
  let decode (word : List (Option Bool)) : Option Query := do
    let width :: count :: fields ← fieldEncoding.decode word | none
    let (blocks, rest) ← Query.decodeBlocks width count fields
    if rest = [] then return ⟨width, blocks⟩ else none
  have gates_roundtrip {n : ℕ} (gs : List (Gate n)) (rest : List ℕ) :
      Query.decodeGates n gs.length (gs.flatMap gateFields ++ rest) = some (gs, rest) := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases g with
      | single kind wire =>
        cases kind <;> simp [gateFields, Query.decodeGates, wire.isLt, ih]
      | controlledNot c t different =>
        have hct : c.val ≠ t.val := fun h ↦ different (Fin.ext h)
        simp [gateFields, Query.decodeGates, c.isLt, t.isLt, hct, ih]
  have indices_roundtrip {n : ℕ} (xs : List (Fin n)) :
      (xs.map Fin.val).mapM
        (fun k ↦ if h : k < n then some (⟨k, h⟩ : Fin n) else none) = some xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [x.isLt, ih]
  have blocks_roundtrip {n : ℕ} (bs : List (List (Gate n) × Finset (Fin n)))
      (rest : List ℕ) :
      Query.decodeBlocks n bs.length (bs.flatMap blockFields ++ rest) = some (bs, rest) := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      rcases b with ⟨gs, measured⟩
      simp only [List.length_cons, List.flatMap_cons, blockFields, List.cons_append,
        List.append_assoc, Query.decodeBlocks]
      rw [gates_roundtrip]
      have hlen : ((measured.sort (· ≤ ·)).map Fin.val).length = measured.card := by simp
      simp only [← hlen, List.length_map]
      simp only [Finset.length_sort, List.length_take, inf_eq_left, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some, List.length_append, hlen, List.length_flatMap,
        List.length_cons, List.length_map, List.sum_map_add, List.map_const', List.sum_replicate,
        smul_eq_mul, mul_one, le_add_iff_nonneg_right, zero_le, ↓reduceIte, List.take_left',
        indices_roundtrip, List.drop_left', Finset.sort_toFinset]
      change (Query.decodeBlocks n bs.length (bs.flatMap blockFields ++ rest)).bind _ = _
      rw [ih]
      rfl
  ⟨encode, decode, by
    rintro ⟨width, blocks⟩
    have hb := blocks_roundtrip blocks []
    simp only [List.append_nil] at hb
    simp [encode, decode, hb]⟩

/-- A pure state of a register of `width` qubits: a unit vector (Section 2.1). -/
def State (width : ℕ) : Type :=
  {ψ : EuclideanSpace ℂ (Fin width → Bool) // ‖ψ‖ = 1}

open scoped Classical in
/-- The computational-basis measurement of a set `S` of wires, returning the normalized
post-measurement state (Section 2.1).

Only outcomes of positive Born weight occur, so no state is chosen for zero-weight outcomes. -/
def collapse {width : ℕ} (S : Finset (Fin width)) (ψ : State width) : PMF (State width) :=
  let project : (S → Bool) → EuclideanSpace ℂ (Fin width → Bool) :=
    fun r ↦ WithLp.toLp 2 (fun x ↦ if (fun i : S ↦ x i) = r then ψ.val x else 0)
  have hsum : ∑ r : S → Bool, ‖project r‖ ^ 2 = 1 := by
    calc
      ∑ r : S → Bool, ‖project r‖ ^ 2 =
          ∑ r : S → Bool, ∑ x : Fin width → Bool,
            if (fun i : S ↦ x i) = r then ‖ψ.val x‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        simp [project, EuclideanSpace.norm_sq_eq, apply_ite]
      _ = ∑ x : Fin width → Bool, ‖ψ.val x‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp
      _ = 1 := by
        rw [← EuclideanSpace.norm_sq_eq, ψ.property]
        simp
  let outcomes : PMF (S → Bool) :=
    PMF.ofFintype (fun r ↦ ENNReal.ofReal (‖project r‖ ^ 2)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ ↦ sq_nonneg ‖project r‖), hsum]
      simp)
  outcomes.bindOnSupport fun r hr ↦ PMF.pure
    ⟨(‖project r‖⁻¹ : ℝ) • project r, by
      have hp : 0 < ‖project r‖ ^ 2 := by
        have h := (outcomes.apply_pos_iff r).mpr hr
        change 0 < ENNReal.ofReal (‖project r‖ ^ 2) at h
        exact ENNReal.ofReal_pos.mp h
      have hn : ‖project r‖ ≠ 0 := by
        intro hz
        simp [hz] at hp
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (project r))),
        inv_mul_cancel₀ hn]⟩

open scoped Classical in
/-- The non-collapsing history of a pure state under a list of unitary blocks, each followed by
a computational-basis measurement (Section 4).

Each step prepends a full-register sample without disturbing the state, and the next block acts
on the post-measurement state. -/
def qpFrom {width : ℕ}
    (blocks : List (Matrix.unitaryGroup (Fin width → Bool) ℂ × Finset (Fin width)))
    (ψ : State width) : PMF (Fin (blocks.length + 1) → Fin width → Bool) :=
  let samples : PMF (Fin width → Bool) :=
    PMF.ofFintype (fun x ↦ ENNReal.ofReal (‖ψ.val x‖ ^ 2)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ sq_nonneg ‖ψ.val x‖),
        ← EuclideanSpace.norm_sq_eq, ψ.property]
      simp)
  samples.bind fun sample ↦
    match blocks with
    | [] => PMF.pure (fun _ ↦ sample)
    | (U, S) :: rest =>
      let φ : State width :=
        ⟨(@Matrix.toEuclideanCLM ℂ (Fin width → Bool) _ _ _) U.val ψ.val,
          (Unitary.norm_map
            (Unitary.map (StarMonoidHom.ofClass
              (@Matrix.toEuclideanCLM ℂ (Fin width → Bool) _ _ _)) U)
            ψ.val).trans ψ.property⟩
      (collapse S φ).bind fun next ↦ (qpFrom rest next).map (Fin.cons sample)
termination_by blocks.length

/-- The oracle `Q_P` on a query: run the circuit from `|0…0⟩` and output all `T + 1`
whole-register samples, in time order and wire order (Section 4).

Within a block the first gate acts first. -/
def Query.qp (query : Query) : PMF (List Bool) :=
  let blocks := query.blocks.map fun block ↦
    (block.1.foldl (fun unitary gate ↦ gate.matrix * unitary) 1, block.2)
  (qpFrom blocks ⟨EuclideanSpace.single (fun _ ↦ false) 1, by simp⟩).map
    (fun samples ↦ (List.ofFn samples).flatMap List.ofFn)

/-- **Question 1** (Section 9, p. 15; ABFL Section 7, question 4). Every language in PDQP belongs
to PP: `PDQP ⊆ PP`.

PDQP is encoded by a polynomial-time query generator and postprocessor around one `Q_P` call
with success probability at least `2/3`, over the fixed gate basis and the explicit encoding
`Query.encoding`; PP by a polynomial-time machine with fair coins and success probability
greater than `1/2`. -/
theorem question_1 (language : Set (List Bool)) :
    let wordPair := (Computability.encodingProd
      (Computability.encodingList Bool) (Computability.encodingList Bool)).encode
    (∃ (generate : List Bool → Query)
        (answer : List Bool × List Bool → Bool)
        (generator : Turing.TM2ComputableInPolyTime
          (Computability.encodingList Bool).encode Query.encoding.encode generate)
        (postprocessor : Turing.TM2ComputableInPolyTime
          wordPair Computability.encodeBool answer),
      (∀ k, Finite (generator.tm.Γ k)) ∧
      (∀ k, Finite (postprocessor.tm.Γ k)) ∧
      ∃ resource : ℕ[X], ∀ input : List Bool,
        let query := generate input
        query.width + query.blocks.length +
            (query.blocks.map (fun block ↦ block.1.length)).sum +
            (Query.encoding.encode query).length +
            query.width * (query.blocks.length + 1) ≤ resource.eval input.length ∧
        (2 / 3 : ℝ≥0∞) ≤ query.qp.toOuterMeasure
          {transcript | answer (input, transcript) = true ↔ input ∈ language}) →
    ∃ (answer : List Bool × List Bool → Bool) (coins : ℕ[X])
        (machine : Turing.TM2ComputableInPolyTime
          wordPair Computability.encodeBool answer),
      (∀ k, Finite (machine.tm.Γ k)) ∧
      ∀ input : List Bool,
        (1 / 2 : ℝ≥0∞) <
          (PMF.uniformOfFintype (Fin (coins.eval input.length) → Bool)).toOuterMeasure
            {bits | answer (input, List.ofFn bits) = true ↔ input ∈ language} := by
  sorry

end Lee2013Complexity
