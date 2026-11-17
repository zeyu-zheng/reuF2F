import Mathlib

/-!
# On the scramble number of graphs

Authors: Marino Echavarria, Max Everett, Robin Huang, Liza Jacoby, Ralph Morrison, and Ben Weber.
Origin: [Williams College SMALL REU](https://math.williams.edu/small/research-publications/).
Reference: M. Echavarria, M. Everett, R. Huang, L. Jacoby, R. Morrison, and B. Weber, *On the
scramble number of graphs*, Discrete Appl. Math. **310** (2022), 43-59; arXiv:2103.15253v3.
-/

noncomputable section

namespace Echavarria2022Scramble

open Finset

/-- An explicitly labelled loopless multigraph, given by its vertex count and edge list.

Parallel edges are separate list entries, and isolated vertices are retained. -/
structure GraphInput where
  /-- The number of vertices. -/
  vertices : ℕ
  /-- The endpoints of each edge, in list order. -/
  ends : List (Fin vertices × Fin vertices)
  /-- Each edge lists its smaller endpoint first. -/
  ordered : ∀ e ∈ ends, e.1 < e.2

/-- The multigraph of an explicit edge list, with edges indexed by their list positions. -/
def GraphInput.toGraph (g : GraphInput) : Graph (Fin g.vertices) (Fin g.ends.length) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := g.ends[e] = (u, v) ∨ g.ends[e] = (v, u)
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
    · intro _
      exact ⟨g.ends[e].1, g.ends[e].2, Or.inl (Prod.eta _)⟩
    · intro _
      exact Set.mem_univ _
  left_mem_of_isLink := by
    intro _ _ _ _
    trivial

open scoped Classical in
/-- Decode a binary word as a graph: a unary vertex count followed by unary endpoint pairs, each
field terminated by `false`.

Malformed words, including out-of-range, looped or reversed pairs, decode to `none`. -/
def decodeGraph (input : List Bool) : Option GraphInput :=
  if input.getLast? ≠ some false then none else do
    let fields := (input.splitOn false).dropLast.map List.length
    match fields with
    | [] => none
    | n :: rest =>
      let rec /-- Reads the remaining fields in pairs as edges, rejecting out-of-range endpoints. -/
        readEdges : List ℕ → Option (List (Fin n × Fin n))
        | [] => some []
        | a :: b :: tail => do
          if ha : a < n then
            if hb : b < n then
              let edges ← readEdges tail
              some ((⟨a, ha⟩, ⟨b, hb⟩) :: edges)
            else none
          else none
        | _ => none
      let edges ← readEdges rest
      if ho : ∀ e ∈ edges, e.1 < e.2 then
        some { vertices := n, ends := edges, ordered := ho }
      else none

/-- A scramble: a family of eggs, each a nonempty vertex set inducing a connected subgraph
(Section 2.2).

Eggs need not be disjoint, and the empty family is allowed. -/
def IsScramble (g : GraphInput) (S : Finset (Finset (Fin g.vertices))) : Prop :=
  ∀ egg ∈ S, egg.Nonempty ∧
    (g.toGraph.induce (egg : Set (Fin g.vertices))).toSimpleGraph.Connected

open scoped Classical in
/-- The order of a scramble: the largest `q` bounded by every hitting set and by every egg-cut
(Section 2.2).

The order is capped by the vertex count, and a family with no egg-cut imposes no cut bound. -/
def scrambleOrder (g : GraphInput) (S : Finset (Finset (Fin g.vertices))) : ℕ :=
  {q ∈ range (g.vertices + 1) |
    (∀ C : Finset (Fin g.vertices), (∀ egg ∈ S, (C ∩ egg).Nonempty) → q ≤ #C) ∧
    (∀ A : Finset (Fin g.vertices),
      (∃ egg ∈ S, egg ⊆ A) → (∃ egg ∈ S, egg ⊆ Aᶜ) →
        q ≤ (g.toGraph.edgeCut (A : Set (Fin g.vertices))).ncard)}.sup id

open scoped Classical in
/-- The scramble number: the maximum order of a scramble (Section 2.2).

The null graph has scramble number zero. -/
def scrambleNumber (g : GraphInput) : ℕ :=
  {S ∈ (univ : Finset (Fin g.vertices)).powerset.powerset | IsScramble g S}.sup (scrambleOrder g)

/-- **Question 3.6** (Section 3, arXiv v3 p. 11). For each fixed `k`, whether the scramble number
of a graph is at most `k` can be decided in polynomial time.

Inputs are binary words in the unary encoding of `decodeGraph`, malformed words are rejected, and
each `k` has its own polynomial-time machine with finite stack alphabets. -/
theorem question_3_6 (k : ℕ) :
    ∃ decider : List Bool → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime id Computability.encodeBool decider,
        (∀ stack : machine.tm.K, Finite (machine.tm.Γ stack)) ∧
        ∀ input : List Bool, decider input = true ↔
          ∃ g : GraphInput, decodeGraph input = some g ∧ scrambleNumber g ≤ k := by
  sorry

end Echavarria2022Scramble
