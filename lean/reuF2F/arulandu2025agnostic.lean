import Mathlib

/-!
# Agnostic Product Mixed State Tomography via Robust Statistics

Authors: Alvan Arulandu, Ilias Diakonikolas, Daniel Kane, and Jerry Li.
Origin: [Quantum@UW REU 2025](https://quantumreu.cs.washington.edu/past-reus/2025).
Reference: A. Arulandu, I. Diakonikolas, D. Kane, and J. Li, *Agnostic product mixed state
tomography via robust statistics*, preprint; arXiv:2510.08472v2 (2026; first version 2025).
-/

noncomputable section
namespace Arulandu2025Agnostic

open scoped ComplexOrder

/-- Self-delimited unary natural-number fields over the alphabet `Option Bool`. Unary headers
keep resource fields from encoding exponential workspace for free. -/
def fieldEncoding : Computability.Encoding (List ℕ) (Option Bool) :=
  let encode : List ℕ → List (Option Bool) :=
    List.flatMap (fun n ↦ List.replicate n (some true) ++ [none])
  let step : Option Bool → Option (List ℕ) → Option (List ℕ)
    | none, rest => (List.cons 0) <$> rest
    | some true, rest => rest.bind (fun ns ↦ match ns with
        | n :: tail => some ((n+1) :: tail)
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

/-- A computational-basis label for an n-qubit register. -/
abbrev BasisLabel (n : ℕ) := Fin n → Bool

/-- The fixed one-qubit gates used by this concrete interpreter. -/
inductive OneQubitGate
  | hadamard
  | phaseT

/-- The exact `H` and `T` matrices. -/
def OneQubitGate.matrix : OneQubitGate → Matrix.unitaryGroup Bool ℂ
  | .hadamard => by
      let s : ℂ := (√2 : ℝ)
      refine ⟨Matrix.of (fun x y ↦ (if x && y then -1 else 1) / s), ?_⟩
      rw [Matrix.mem_unitaryGroup_iff']
      ext x y
      cases x <;> cases y <;>
        simp only [Bool.and_eq_true, Bool.false_eq_true, Bool.true_eq_false,
          Complex.conj_ofReal, Finset.card_insert_of_notMem, Finset.card_singleton,
          Finset.mem_singleton, Finset.sum_const, Finset.sum_insert, Finset.sum_singleton,
          Fintype.univ_bool, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply,
          Matrix.one_apply_eq, Matrix.one_apply_ne, Matrix.star_eq_conjTranspose, Nat.cast_ofNat,
          Nat.reduceAdd, RCLike.star_def, and_false, and_true, map_neg, map_one, ne_eq,
          not_false_eq_true, nsmul_eq_mul, one_div, s, star_div₀, star_inv₀, ↓reduceIte]
      all_goals
        apply Complex.ext <;>
          norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
        all_goals field_simp
        all_goals norm_num
  | .phaseT => by
      let z : ℂ := (1 + Complex.I) / (√2 : ℝ)
      have hz : (starRingEnd ℂ) z * z = 1 := by
        apply Complex.ext
        · simp [z, Complex.div_re, Complex.div_im, Complex.normSq_apply]
          field_simp
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        · simp [z, Complex.div_re, Complex.div_im, Complex.normSq_apply]
          ring
      refine ⟨Matrix.diagonal (fun b ↦ if b then z else 1), ?_⟩
      rw [Matrix.mem_unitaryGroup_iff']
      ext x y
      cases x <;> cases y <;>
        simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
          hz]

/-- One primitive operation, with wire indices already checked against register width. -/
inductive Gate (n : ℕ)
  | single (kind : OneQubitGate) (wire : Fin n)
  | controlledNot (control target : Fin n) (different : control ≠ target)

/-- The unitary of a primitive gate acting on its named wires. -/
def Gate.matrix {n : ℕ} : Gate n → Matrix.unitaryGroup (BasisLabel n) ℂ
  | .single kind wire => by
      let e := Equiv.funSplitAt wire Bool
      let u := Matrix.kronecker kind.matrix.val
        (1 : Matrix ({j : Fin n // j ≠ wire} → Bool)
          ({j : Fin n // j ≠ wire} → Bool) ℂ)
      have hu : u ∈ Matrix.unitaryGroup _ ℂ :=
        Matrix.kronecker_mem_unitary kind.matrix.property (one_mem _)
      refine ⟨u.submatrix e e, ?_⟩
      rw [Matrix.mem_unitaryGroup_iff'] at hu ⊢
      change u.conjTranspose * u = 1 at hu
      change (u.submatrix e e).conjTranspose * u.submatrix e e = 1
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ e e e, hu,
        Matrix.submatrix_one_equiv]
  | .controlledNot c t h => by
      let f : BasisLabel n → BasisLabel n := fun x ↦ Function.update x t (xor (x c) (x t))
      have hf : Function.Involutive f := by
        intro x
        funext i
        by_cases hi : i = t
        · subst i
          simp [f, h]
        · simp [f, hi]
      let e := hf.toPerm
      refine ⟨e.permMatrix ℂ, ?_⟩
      rw [Matrix.mem_unitaryGroup_iff']
      change (e.permMatrix ℂ).conjTranspose * e.permMatrix ℂ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp

/-- A finite circuit with a fixed register width and checked H/T/CNOT instructions. -/
structure Circuit where
  /-- The number of qubits in the register. -/
  width : ℕ
  /-- The list of gate instructions, applied in order. -/
  operations : List (Gate width)

/-- The circuit unitary in physical execution order. -/
def Circuit.matrix (c : Circuit) : Matrix.unitaryGroup (BasisLabel c.width) ℂ :=
  c.operations.foldl (fun u g ↦ g.matrix * u) 1

/-- Parse finite circuit instructions with validated gate tags and wire indices. -/
private def Circuit.decodeGates (width : ℕ) : List ℕ → Option (List (Gate width))
    | 0 :: wire :: tail => do
        if h : wire < width then
          return .single .hadamard ⟨wire,h⟩ :: (← Circuit.decodeGates width tail)
        else none
    | 1 :: wire :: tail => do
        if h : wire < width then
          return .single .phaseT ⟨wire,h⟩ :: (← Circuit.decodeGates width tail)
        else none
    | 2 :: control :: target :: tail => do
        if hc : control < width then
          if ht : target < width then
            if hct : control ≠ target then
              return .controlledNot ⟨control,hc⟩ ⟨target,ht⟩
                (fun h ↦ hct (congrArg Fin.val h)) :: (← Circuit.decodeGates width tail)
            else none
          else none
        else none
    | [] => some []
    | _ => none

/-- Finite circuit description with unary width and validated gate and wire fields. -/
def Circuit.encoding : Computability.Encoding Circuit (Option Bool) :=
  let fields {n : ℕ} (g : Gate n) : List ℕ := match g with
    | .single .hadamard wire => [0, wire.val]
    | .single .phaseT wire => [1, wire.val]
    | .controlledNot control target _ => [2, control.val, target.val]
  let encode (c : Circuit) := fieldEncoding.encode
    (c.width :: c.operations.flatMap fields)
  let decode (word : List (Option Bool)) : Option Circuit := do
    let width :: rest ← fieldEncoding.decode word | none
    return ⟨width, ← Circuit.decodeGates width rest⟩
  ⟨encode, decode, by
    rintro ⟨width, ops⟩
    have h : ∀ ops : List (Gate width),
        Circuit.decodeGates width (ops.flatMap fields) = some ops := by
      intro ops
      induction ops with
      | nil => rfl
      | cons g ops ih =>
        cases g with
        | single kind wire =>
          cases kind <;> simp [List.flatMap_cons, fields, Circuit.decodeGates, wire.isLt, ih]
        | controlledNot c t different =>
          have hct : c.val ≠ t.val := fun h ↦ different (Fin.ext h)
          simp [List.flatMap_cons, fields, Circuit.decodeGates, c.isLt, t.isLt, hct, ih]
    simp [encode, decode, h]⟩

/-- A mixed quantum state on a finite computational basis. -/
abbrev Density (ι : Type) [Fintype ι] :=
  {ρ : Matrix ι ι ℂ // ρ.PosSemidef ∧ ρ.trace = 1}

/-- Trace distance is half the sum of singular values for the Euclidean operator. -/
def traceDistance {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ σ : Density ι) : ℝ :=
  ((Matrix.toEuclideanLin (ρ.val - σ.val)).singularValues.sum (fun _ x ↦ x)) / 2

/-- Tensor product of the arbitrary one-qubit mixed factors, in qubit order. -/
def productState : (n : ℕ) → (Fin n → Density Bool) → Density (BasisLabel n)
  | 0, _ => ⟨1, Matrix.PosSemidef.one, by simp [Matrix.trace_one, BasisLabel]⟩
  | n + 1, π => by
    let prev := productState n (fun i ↦ π i.castSucc)
    let last := π (Fin.last n)
    let M := Matrix.kronecker prev.val last.val
    let e := Fin.succFunEquiv Bool n
    refine ⟨M.submatrix e e, (prev.property.1.kronecker last.property.1).submatrix e, ?_⟩
    change (∑ x : BasisLabel (n + 1), M (e x) (e x)) = 1
    rw [e.sum_comp (fun x ↦ M x x)]
    change M.trace = 1
    dsimp [M]
    rw [Matrix.trace_kronecker, prev.property.2, last.property.2, mul_one]

/-- The product-mixed ansatz (Definition 1.1). -/
def productMixedStates (n : ℕ) : Set (Density (BasisLabel n)) :=
  Set.range (productState n)

/-- The best product-mixed approximation error `opt(ρ)`. -/
def opt {n : ℕ} (ρ : Density (BasisLabel n)) : ℝ :=
  sInf {e : ℝ | ∃ π ∈ productMixedStates n, e = traceDistance ρ π}

/-- Append fresh zero ancillas while retaining the original computational-basis order. -/
def zeroEmbedding (n a : ℕ) : Matrix (BasisLabel (n + a)) (BasisLabel n) ℂ :=
  fun y x ↦ if y = Fin.append x (fun _ : Fin a ↦ false) then 1 else 0

/-- The ancilla embedding is an isometry. -/
theorem zeroEmbedding_isometry (n a : ℕ) :
    (zeroEmbedding n a).conjTranspose * zeroEmbedding n a = 1 := by
  classical
  ext x z
  have h : Fin.append z (fun _ : Fin a ↦ false) =
      Fin.append x (fun _ : Fin a ↦ false) ↔ z = x := by
    constructor
    · intro heq
      funext i
      have hi := congrFun heq (Fin.castAdd a i)
      simpa using hi
    · rintro rfl
      rfl
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    zeroEmbedding, apply_ite, h, eq_comm]

/-- Apply a unitary to a mixed state after appending fresh zero ancillas. -/
def evolve {n a : ℕ} (U : Matrix.unitaryGroup (BasisLabel (n + a)) ℂ)
    (ρ : Density (BasisLabel n)) : Density (BasisLabel (n + a)) :=
  let J := zeroEmbedding n a
  let E := U.val * J
  have hU : U.val.conjTranspose * U.val = 1 := U.property.1
  have hE : E.conjTranspose * E = 1 := by
    dsimp [E]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U.val.conjTranspose, hU, Matrix.one_mul,
      zeroEmbedding_isometry]
  ⟨E * ρ.val * E.conjTranspose, ρ.property.1.mul_mul_conjTranspose_same E, by
    calc
      (E * ρ.val * E.conjTranspose).trace =
          (E.conjTranspose * E * ρ.val).trace := Matrix.trace_mul_cycle E ρ.val E.conjTranspose
      _ = 1 := by rw [hE, Matrix.one_mul, ρ.property.2]⟩

/-- Proper one-qubit state encoded by a complex Gram matrix, with a fixed zero fallback. -/
def gramState (B : Matrix Bool Bool ℂ) : Density Bool :=
  let H := B * B.conjTranspose
  have hH : H.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose B
  let t := H.trace.re
  have him : H.trace.im = 0 := (RCLike.nonneg_iff.mp hH.trace_nonneg).2
  have hreal : (t : ℂ) = H.trace := by
    apply Complex.ext <;> simp [t, him]
  if ht : t = 0 then
    ⟨(1 / 2 : ℝ) • (1 : Matrix Bool Bool ℂ),
      Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2), by
        simp [Matrix.trace_smul, Matrix.trace_one]⟩
  else
    have hnonneg : 0 ≤ t := (RCLike.nonneg_iff.mp hH.trace_nonneg).1
    ⟨t⁻¹ • H, hH.smul (inv_nonneg.mpr hnonneg), by
      rw [Matrix.trace_smul, ← hreal]
      simp [ht]⟩

/-- A fixed finite dyadic Gram description: sign and magnitude bits for eight real entries. -/
structure DyadicGram (p : ℕ) where
  /-- The sign bit of each entry's real or imaginary part, indexed by row, column and part. -/
  sign : Bool → Bool → Bool → Bool
  /-- The binary digits of each entry's real or imaginary part magnitude. -/
  magnitude : Bool → Bool → Bool → Fin (p + 1) → Bool

/-- Decode signed dyadic entries exactly as rational numbers before embedding into C. -/
def DyadicGram.matrix {p : ℕ} (c : DyadicGram p) : Matrix Bool Bool ℂ :=
  fun i j ↦
    let component := fun part ↦
      ((if c.sign i j part then -1 else 1 : ℚ) *
        (∑ k : Fin (p + 1), if c.magnitude i j part k then (2 : ℚ) ^ k.val else 0)) /
        (2 : ℚ) ^ p
    (component false : ℂ) + (component true : ℂ) * Complex.I

/-- Decode a finite dyadic output block to a product of one-qubit mixed states. -/
def decodeProduct (n p : ℕ) (bits : Fin ((n * 8) * (p + 2)) → Bool) :
    Density (BasisLabel n) :=
  let read := fun (q : Fin n) (i j part : Bool) (offset : Fin (p + 2)) ↦
    let component : Fin 8 := ⟨(if i then 4 else 0) + (if j then 2 else 0) +
      (if part then 1 else 0), by cases i <;> cases j <;> cases part <;> decide⟩
    bits (finProdFinEquiv (finProdFinEquiv (q, component), offset))
  productState n (fun q ↦
    let c : DyadicGram p :=
      { sign := fun i j part ↦ read q i j part 0
        magnitude := fun i j part k ↦ read q i j part k.succ }
    gramState c.matrix)

/-- Public widths and finite precision for the seed, copies, and final private workspace. -/
structure Layout where
  /-- The number of measured qubits in the seed register. -/
  seed : ℕ
  /-- The number of seed-circuit qubits retained privately for postprocessing. -/
  retained : ℕ
  /-- The number of copies of the input state that are measured. -/
  copies : ℕ
  /-- The number of ancilla qubits used in each copy measurement. -/
  copyAncillas : ℕ
  /-- The number of ancilla qubits used in the postprocessing circuit. -/
  postAncillas : ℕ
  /-- The dyadic precision of the output description. -/
  precision : ℕ

/-- Every resource field has an explicit unary description; malformed layouts are rejected. -/
def Layout.encoding : Computability.Encoding Layout (Option Bool) :=
  let encode (L : Layout) := fieldEncoding.encode
    [L.seed, L.retained, L.copies, L.copyAncillas, L.postAncillas, L.precision]
  let decode (word : List (Option Bool)) : Option Layout := do
    let [s, k, N, c, q, p] ← fieldEncoding.decode word | none
    return ⟨s, k, N, c, q, p⟩
  ⟨encode, decode, by
    rintro ⟨s, k, N, c, q, p⟩
    simp [encode, decode]⟩

/-- The finite controller interface separates outcome-independent copy design from final
processing. -/
inductive Request
  | layout (n accuracy confidence : ℕ)
  | seed (n accuracy confidence : ℕ)
  | measurement (n accuracy confidence index : ℕ) (seed : List Bool)
  | postprocess (n accuracy confidence : ℕ) (seed transcript : List Bool)

/-- Tagged requests use unary numeric fields and literal seed/transcript bits in finite
alphabets. -/
def Request.encoding :
    Computability.Encoding Request ((Option Bool ⊕ Bool) ⊕ Bool) :=
  let blocks := Computability.encodingProd
    (Computability.encodingProd fieldEncoding (Computability.encodingList Bool))
    (Computability.encodingList Bool)
  let encode : Request → List ((Option Bool ⊕ Bool) ⊕ Bool)
    | .layout n a b => blocks.encode (([0, n, a, b], []), [])
    | .seed n a b => blocks.encode (([1, n, a, b], []), [])
    | .measurement n a b i r => blocks.encode (([2, n, a, b, i], r), [])
    | .postprocess n a b r y => blocks.encode (([3, n, a, b], r), y)
  let decode (word : List ((Option Bool ⊕ Bool) ⊕ Bool)) : Option Request := do
    let ((fields, r), y) ← blocks.decode word
    match fields, r, y with
    | [0, n, a, b], [], [] => return .layout n a b
    | [1, n, a, b], [], [] => return .seed n a b
    | [2, n, a, b, i], r, [] => return .measurement n a b i r
    | [3, n, a, b], r, y => return .postprocess n a b r y
    | _, _, _ => none
  ⟨encode, decode, by
    intro request
    cases request <;> simp [encode, decode]⟩

/-- **Unnumbered conjecture** (Section 1.1.1). No uniformly efficient nonadaptive single-copy
learner achieves a dimension-independent vanishing semi-agnostic rate for the product-mixed
ansatz.

Learners are finite-gate circuits with a private quantum seed workspace retained only for final
processing. Problem 1's ket notation is read by the mixed-state Definition 1.1, and register
widths include zero. -/
theorem adaptive_measurements_necessary :
    ¬∃ generate : Request → List (Option Bool),
      ∃ machine : Turing.TM2ComputableInPolyTime Request.encoding.encode
        (Computability.encodingList (Option Bool)).encode generate,
        (∀ stack : machine.tm.K, Finite (machine.tm.Γ stack)) ∧
        ∃ bound : Polynomial ℕ, ∃ f : ℝ → ℝ,
          (∀ t ≥ (0 : ℝ), 0 ≤ f t) ∧
          MonotoneOn f (Set.Ici 0) ∧ f 0 = 0 ∧
          (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
            ∀ t ≥ (0 : ℝ), t < δ → f t < ε) ∧
          ∀ n a b : ℕ, 0 < a → 0 < b →
            ∃ L : Layout,
              Layout.encoding.decode (generate (.layout n a b)) = some L ∧
              ∃ seedGates : List (Gate (L.seed + L.retained)),
              ∃ copyGates : BasisLabel L.seed → Fin L.copies →
                  List (Gate (n + L.copyAncillas)),
              let copyWidth := n + L.copyAncillas
              let postWidth := (L.retained + (L.seed + L.copies * copyWidth)) + L.postAncillas
              ∃ postGates : BasisLabel L.seed → (Fin L.copies → BasisLabel copyWidth) →
                  List (Gate postWidth),
                Circuit.encoding.decode (generate (.seed n a b)) =
                    some ⟨L.seed + L.retained, seedGates⟩ ∧
                (∀ r : BasisLabel L.seed, ∀ i : Fin L.copies,
                  Circuit.encoding.decode
                    (generate (.measurement n a b i.val (List.ofFn r))) =
                    some ⟨copyWidth, copyGates r i⟩) ∧
                (let flatten := fun y : Fin L.copies → BasisLabel copyWidth ↦
                    fun j : Fin (L.copies * copyWidth) ↦
                      y (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
                 let charged := fun request : Request ↦
                    (Request.encoding.encode request).length + (generate request).length +
                    machine.time.eval (Request.encoding.encode request).length
                 ∃ houtput : ((n * 8) * (L.precision + 2)) ≤ postWidth,
                   (∀ r : BasisLabel L.seed, ∀ y : Fin L.copies → BasisLabel copyWidth,
                     Circuit.encoding.decode (generate (.postprocess n a b
                       (List.ofFn r) (List.ofFn (flatten y)))) =
                         some ⟨postWidth, postGates r y⟩ ∧
                     n + a + b + L.seed + L.retained + L.copies +
                       L.copies * copyWidth + postWidth + L.precision +
                       ((n * 8) * (L.precision + 2)) + seedGates.length +
                       (∑ i : Fin L.copies, (copyGates r i).length) +
                       (postGates r y).length + charged (.layout n a b) +
                       charged (.seed n a b) +
                       (∑ i : Fin L.copies,
                         charged (.measurement n a b i.val (List.ofFn r))) +
                       charged (.postprocess n a b (List.ofFn r)
                         (List.ofFn (flatten y))) ≤ bound.eval (n + a + b + 1)) ∧
                   ∀ ρ : Density (BasisLabel n),
                     1 - 1 / (2 : ℝ) ^ b ≤ (∑ r : BasisLabel L.seed,
                       ∑ y : Fin L.copies → BasisLabel copyWidth,
                       ∑ z : BasisLabel postWidth,
                         if traceDistance ρ
                             (decodeProduct n L.precision (fun j ↦ z (Fin.castLE houtput j))) ≤
                               f (opt ρ) + 1 / (a : ℝ) then
                           (∏ i : Fin L.copies,
                             (evolve (n := n) (a := L.copyAncillas)
                               (Circuit.mk copyWidth (copyGates r i)).matrix ρ).val
                               (y i) (y i) |>.re) *
                           Complex.normSq
                             (∑ u : BasisLabel L.retained,
                               (Circuit.mk postWidth (postGates r y)).matrix.val z
                                 (Fin.append (Fin.append u (Fin.append r (flatten y)))
                                   (fun _ : Fin L.postAncillas ↦ false)) *
                               (Circuit.mk (L.seed + L.retained) seedGates).matrix.val
                                 (Fin.append r u) (fun _ ↦ false))
                         else 0)) := by
  sorry

end Arulandu2025Agnostic
