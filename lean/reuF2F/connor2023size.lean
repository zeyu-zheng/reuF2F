import Mathlib

/-!
# On the size and complexity of scrambles

Authors: Seamus Connor, Steven DiSilvio, Sasha Kononova, Ralph Morrison,
and Krish Singal.
Origin: [Williams College SMALL REU](https://math.williams.edu/small/).
Reference: S. Connor, S. DiSilvio, S. Kononova, R. Morrison, and K. Singal, *On the size and
complexity of scrambles*, arXiv:2311.17342v3 (2026).
-/

namespace Connor2023Size

open Finset

/-- The multigraph presented by an explicit edge-instance list. Repeated endpoint pairs remain
distinct edges, indexed by their list positions. -/
def graphFromEdges {n m : ℕ} (ends : Fin m → Fin n × Fin n) :
    Graph (Fin n) (Fin m) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := ends e = (u, v) ∨ ends e = (v, u)
  isLink_symm _ _ := ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hx hv
    rcases hx with hx | hx <;> rcases hv with hv | hv
    · exact Or.inl (Prod.mk.inj (hx.symm.trans hv)).1
    · exact Or.inr (Prod.mk.inj (hx.symm.trans hv)).1
    · exact Or.inr (Prod.mk.inj (hx.symm.trans hv)).2
    · exact Or.inl (Prod.mk.inj (hx.symm.trans hv)).2
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro _; exact ⟨(ends e).1, (ends e).2, Or.inl (Prod.eta _)⟩
    · intro _; exact Set.mem_univ _
  left_mem_of_isLink := by intro _ _ _ _; trivial

/-- A nonempty family of pairwise vertex-disjoint, nonempty connected eggs (Section 2.2). Eggs
are encoded as vertex sets with their induced subgraphs. -/
def IsDisjointScramble {n m : ℕ} (G : Graph (Fin n) (Fin m))
    (S : Finset (Finset (Fin n))) : Prop :=
  S.Nonempty ∧
    (∀ A ∈ S, A.Nonempty ∧ (G.induce (A : Set (Fin n))).toSimpleGraph.Connected) ∧
    (S : Set (Finset (Fin n))).Pairwise fun A B ↦ Disjoint A B

/-- One side of an egg-cut: two connected complementary vertex sets, each containing an entire
egg (Section 2.2). The cut size is `edgeCut.ncard` in the target. -/
def IsEggCutSide {n m : ℕ} (G : Graph (Fin n) (Fin m))
    (S : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧
    (G.induce (A : Set (Fin n))).toSimpleGraph.Connected ∧
    (G.induce ((Aᶜ : Finset (Fin n)) : Set (Fin n))).toSimpleGraph.Connected ∧
    (∃ egg ∈ S, egg ⊆ A) ∧ (∃ egg ∈ S, egg ⊆ Aᶜ)

/-- A canonical finite explicit multigraph input. Endpoint pairs are increasing, the pair list
is sorted with repetitions, and connectivity includes the one-vertex graph. -/
structure Instance where
  /-- The number of vertices. -/
  vertices : ℕ
  /-- The number of edges. -/
  edges : ℕ
  /-- The target lower bound for the order of a disjoint scramble. -/
  threshold : ℕ
  vertices_pos : 0 < vertices
  /-- The ordered endpoint pair of each edge. -/
  ends : Fin edges → Fin vertices × Fin vertices
  endpoints_ordered : ∀ e, (ends e).1 < (ends e).2
  pairs_sorted : (List.ofFn ends).Pairwise fun a b ↦
    a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
  connected : (graphFromEdges ends).toSimpleGraph.Connected

open scoped Classical in
/-- The decoder of escaped canonical binary naturals: vertex count, edge count, threshold, then
endpoint pairs. Malformed, trailing and out-of-domain inputs fail. -/
noncomputable def readInstance (input : List Bool) : Option Instance := do
  let rec
    /-- Read one escaped binary word, returning its digits and the remaining input. -/
    readBits : List Bool → Option (List Bool × List Bool)
    | false :: rest => some ([], rest)
    | true :: b :: rest => do
      let (bits, tail) ← readBits rest
      some (b :: bits, tail)
    | _ => none
  let readNat := fun word ↦ do
    let (bits, rest) ← readBits word
    let value := Computability.decodeNat bits
    if Computability.encodeNat value = bits then some (value, rest) else none
  let (v, rest) ← readNat input
  let (e, rest) ← readNat rest
  let (k, rest) ← readNat rest
  if hv : 0 < v then
    let rec
      /-- Read `m` endpoint pairs of vertex indices below `v`, with the remaining input. -/
      readEdges : (m : ℕ) → List Bool →
        Option ((Fin m → Fin v × Fin v) × List Bool)
      | 0, word => some (Fin.elim0, word)
      | m + 1, word => do
        let (a, word) ← readNat word
        let (b, word) ← readNat word
        if ha : a < v then
          if hb : b < v then
            let (tail, word) ← readEdges m word
            some (Fin.cases (⟨a, ha⟩, ⟨b, hb⟩) tail, word)
          else none
        else none
    let (ends, rest) ← readEdges e rest
    if rest = [] then
      if ho : ∀ i, (ends i).1 < (ends i).2 then
        if hs : (List.ofFn ends).Pairwise fun a b ↦
            a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) then
          if hc : (graphFromEdges ends).toSimpleGraph.Connected then
            some { vertices := v, edges := e, threshold := k,
                   vertices_pos := hv, ends, endpoints_ordered := ho,
                   pairs_sorted := hs, connected := hc }
          else none
        else none
      else none
    else none
  else none

/-- **Following Question 6.5** (Section 6.1, p. 16). Deciding the disjoint scramble threshold is
NP-hard.

Graphs are finite connected loopless multigraphs, not only simple ones; inputs are explicit
edge lists with binary thresholds under many-one reductions, with no succinct multiplicities. -/
theorem disjoint_scramble_np_hard :
    let pairCode := (Computability.encodingProd
      (Computability.encodingList Bool) (Computability.encodingList Bool)).encode
    ∀ language : Set (List Bool),
      (∃ verifier : (List Bool × List Bool) → Bool,
        ∃ machine : Turing.TM2ComputableInPolyTime pairCode
            Computability.encodeBool verifier,
          (∀ stack : machine.tm.K, Finite (machine.tm.Γ stack)) ∧
          ∃ bound : Polynomial ℕ, ∀ input : List Bool,
            input ∈ language ↔ ∃ certificate : List Bool,
              certificate.length ≤ bound.eval input.length ∧
                verifier (input, certificate) = true) →
      ∃ reduction : List Bool → List Bool,
        ∃ machine : Turing.TM2ComputableInPolyTime id id reduction,
          (∀ stack : machine.tm.K, Finite (machine.tm.Γ stack)) ∧
          ∀ input, input ∈ language ↔
            ∃ g : Instance, readInstance (reduction input) = some g ∧
              ∃ S : Finset (Finset (Fin g.vertices)),
                IsDisjointScramble (graphFromEdges g.ends) S ∧ g.threshold ≤ #S ∧
                ∀ A : Finset (Fin g.vertices), IsEggCutSide (graphFromEdges g.ends) S A →
                  g.threshold ≤
                    ((graphFromEdges g.ends).edgeCut (A : Set (Fin g.vertices))).ncard := by
  sorry

end Connor2023Size
