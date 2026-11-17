import Mathlib

/-!
# Time Complexity of Computation and Construction in the Chemical Reaction Network-Controlled Tile Assembly Model

Authors: Nicholas Schiefer and Erik Winfree.
Origin: [Caltech SURF 2015-2016](https://www.dna.caltech.edu/DNApeople-past-members.html).
Reference: N. Schiefer and E. Winfree, *Time Complexity of Computation and Construction in the
Chemical Reaction Network-Controlled Tile Assembly Model*, DNA 2016, LNCS **9818** (2016),
165-182; doi:10.1007/978-3-319-43994-5_11.
-/

noncomputable section

namespace Schiefer2016Time

open Finset

/-- A physical tile: its four oriented label-strength bonds (Definition 1). -/
structure Tile (Label : Type) where
  /-- The label and strength of the north bond. -/
  north : Label × ℕ
  /-- The label and strength of the east bond. -/
  east : Label × ℕ
  /-- The label and strength of the south bond. -/
  south : Label × ℕ
  /-- The label and strength of the west bond. -/
  west : Label × ℕ
  deriving DecidableEq

/-- A tile system: finite species and tile sets, removal map and temperature (Definition 3).
Tiles are a set of four-tuples, so identical tiles are not distinguished by IDs. -/
structure TileSystem (Label Signal : Type) where
  /-- The finite set of signal species. -/
  signals : Finset Signal
  /-- The finite set of physical tiles. -/
  tiles : Finset (Tile Label)
  /-- The optional signal associated with removing each tile. -/
  removal : tiles → Option signals
  /-- The binding temperature. -/
  temperature : ℕ

variable {Label Signal : Type}

/-- A finite, oriented lattice map of tiles (Definition 2). -/
abbrev Placement (K : TileSystem Label Signal) :=
  Finmap (fun _ : ℤ × ℤ ↦ K.tiles)

open scoped Classical in
/-- The total local binding strength at an occupied site (Definition 2). -/
def bindingStrength (K : TileSystem Label Signal) (A : Placement K)
    (p : ℤ × ℤ) : ℕ :=
  A.keys.sum (fun q ↦
    match A.lookup p, A.lookup q with
    | some a, some b =>
        let matching (x y : Label × ℕ) := if x = y then x.2 else 0
        if q = (p.1 + 1, p.2) then matching a.val.east b.val.west
        else if q = (p.1 - 1, p.2) then matching a.val.west b.val.east
        else if q = (p.1, p.2 + 1) then matching a.val.north b.val.south
        else if q = (p.1, p.2 - 1) then matching a.val.south b.val.north
        else 0
    | _, _ => 0)

/-- An assembly: grid connectivity, origin seed and local binding (Definition 2). The activated
singleton is the only binding exception, and assemblies are determined by their placement. -/
@[ext] structure Assembly (K : TileSystem Label Signal) where
  /-- The tiles placed at the occupied grid positions. -/
  placement : Placement K
  origin : (0, 0) ∈ placement.keys
  connected : (SimpleGraph.fromRel (fun p q : placement.keys ↦
    q.val = (p.val.1 + 1, p.val.2) ∨
    q.val = (p.val.1 - 1, p.val.2) ∨
    q.val = (p.val.1, p.val.2 + 1) ∨
    q.val = (p.val.1, p.val.2 - 1))).Connected
  binding : placement.keys = {(0, 0)} ∨
    ∀ p ∈ placement.keys, K.temperature ≤ bindingStrength K placement p

/-- The activated singleton seed of the last two reaction types (Definition 3). -/
def seedAssembly (K : TileSystem Label Signal) (t : K.tiles) : Assembly K where
  placement := Finmap.singleton (0, 0) t
  origin := by simp
  connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨(0, 0), by simp⟩, ?_⟩
    intro w
    have hw : w.val = (0, 0) := by simpa using w.property
    have heq : w = ⟨(0, 0), by simp⟩ := Subtype.ext hw
    subst w
    exact SimpleGraph.Reachable.rfl
  binding := Or.inl (Finmap.keys_singleton _ _)

/-- Species: free signals, free tiles and activated assemblies (Definition 6). -/
inductive Species (K : TileSystem Label Signal)
  | signal : K.signals → Species K
  | tile : K.tiles → Species K
  | assembly : Assembly K → Species K

/-- A state: a finite multiset of species, as natural multiplicities (Definition 6). -/
abbrev State (K : TileSystem Label Signal) := Species K →₀ ℕ

/-- The epsilon notation for an optional signal (Definition 3). Absence contributes no signal
molecule. -/
def signalTerm (K : TileSystem Label Signal) (s : Option K.signals) :
    Multiset (Species K) :=
  (s.toList.map Species.signal : List (Species K))

/-- A reaction: reactant and product multisets and a nonnegative rational rate. Equality
identifies permutations, not separate syntactic reaction IDs. -/
structure Reaction (K : TileSystem Label Signal) where
  /-- The multiset of reactant species. -/
  reactants : Multiset (Species K)
  /-- The multiset of product species. -/
  products : Multiset (Species K)
  /-- The nonnegative rational rate constant. -/
  rate : NNRat

/-- The six explicit reaction types, with both permitted product forms for creation
(Definition 3). Null signals are omitted rather than treated as an inexhaustible species. -/
def ExplicitReaction {K : TileSystem Label Signal} (r : Reaction K) : Prop :=
  (∃ a b c d : Option K.signals,
    r.reactants = signalTerm K a + signalTerm K b ∧
    r.products = signalTerm K c + signalTerm K d) ∨
  (∃ (a c d : Option K.signals) (t : K.tiles),
    r.reactants = signalTerm K a + {Species.tile t} ∧
    r.products = signalTerm K c + signalTerm K d) ∨
  (∃ a b : Option K.signals,
    r.reactants = signalTerm K a + signalTerm K b ∧
    ((∃ (t : K.tiles) (c : Option K.signals),
      r.products = {Species.tile t} + signalTerm K c) ∨
     (∃ t u : K.tiles, r.products = {Species.tile t} + {Species.tile u}))) ∨
  (∃ (a b : Option K.signals) (t u : K.tiles),
    r.reactants = signalTerm K a + {Species.tile t} ∧
    r.products = signalTerm K b + {Species.tile u}) ∨
  (∃ (a : Option K.signals) (t : K.tiles),
    r.reactants = signalTerm K a + {Species.tile t} ∧
    r.products = {Species.assembly (seedAssembly K t)} + signalTerm K (K.removal t)) ∨
  (∃ (a : Option K.signals) (t : K.tiles),
    r.reactants = {Species.assembly (seedAssembly K t)} + signalTerm K (K.removal t) ∧
    r.products = signalTerm K a + {Species.tile t})

/-- The implicit unit-rate additions and removals between valid assemblies (Definition 5).
Only a nonorigin site changes, and removal requires exactly temperature and a signal. -/
def ImplicitReaction {K : TileSystem Label Signal} (r : Reaction K) : Prop :=
  ∃ (A B : Assembly K) (p : ℤ × ℤ) (t : K.tiles),
    p ≠ (0, 0) ∧ A.placement.lookup p = none ∧
    B.placement = A.placement.insert p t ∧ r.rate = 1 ∧
    ((r.reactants = {Species.assembly A} + {Species.tile t} ∧
      r.products = {Species.assembly B} + signalTerm K (K.removal t)) ∨
     (K.removal t ≠ none ∧ bindingStrength K B.placement p = K.temperature ∧
      r.reactants = {Species.assembly B} + signalTerm K (K.removal t) ∧
      r.products = {Species.assembly A} + {Species.tile t}))

/-- A finite program, with only free signals and tiles initially present (Definition 3). -/
structure Program (Label Signal : Type) where
  /-- The underlying tile system. -/
  system : TileSystem Label Signal
  /-- The finite set of explicit reactions. -/
  reactions : Finset (Reaction system)
  explicit : ∀ r ∈ reactions, ExplicitReaction r
  /-- The initial counts of free signals and tiles. -/
  initial : system.signals ⊕ system.tiles →₀ ℕ

/-- The initial state embeds free supplies without any prebuilt assembly. -/
def Program.initialState (P : Program Label Signal) : State P.system :=
  P.initial.mapDomain (fun x ↦ match x with
    | Sum.inl s => Species.signal s
    | Sum.inr t => Species.tile t)

/-- Possible reactions, with full multiset feasibility including repeated reactants
(Definition 7). Positive null-reactant templates remain possible, with unspecified kinetics. -/
def Program.Possible (P : Program Label Signal) (L : State P.system)
    (r : Reaction P.system) : Prop := by
  classical
  exact (r ∈ P.reactions ∨ ImplicitReaction r) ∧
    r.rate ≠ 0 ∧ r.reactants.toFinsupp ≤ L

/-- A directed edge: stoichiometric consumption and production (Definition 8). Identity events
are retained. -/
def Program.Step (P : Program Label Signal) (L M : State P.system) : Prop := by
  classical
  exact ∃ r : Reaction P.system, P.Possible L r ∧
    M = L - r.reactants.toFinsupp + r.products.toFinsupp

/-- Finite-path reachability (Definition 8). Finiteness of the reachable set is a separate
source condition. -/
def Program.Reachable (P : Program Label Signal) (L : State P.system) : Prop :=
  Relation.ReflTransGen P.Step P.initialState L

/-- The mass: signals and free tiles weigh one; assemblies weigh all their tiles
(Definition 10). -/
def State.mass {K : TileSystem Label Signal} (L : State K) : ℕ :=
  L.sum (fun species count ↦ count * match species with
    | Species.signal _ => 1
    | Species.tile _ => 1
    | Species.assembly A => #A.placement.keys)

open scoped Classical in
/-- The partial propensity for one or two reactants, with no factor `1 / 2` (Definition 11).
Inactive events give `0`, null-reactant, higher-arity and zero-volume binary events give `none`,
and the volume is an input. -/
def Reaction.propensity {K : TileSystem Label Signal} (r : Reaction K)
    (L : State K) (volume : NNRat) : Option NNRat :=
  if r.rate = 0 ∨ ¬r.reactants.toFinsupp ≤ L then some 0
    else if 1 ≤ r.reactants.card ∧ r.reactants.card ≤ 2 ∧
        (r.reactants.card = 1 ∨ volume ≠ 0) then
      some (r.rate * r.reactants.toFinsupp.prod
        (fun s n ↦ ((L s).descFactorial n : NNRat)) /
        volume ^ (r.reactants.card - 1))
    else none

/-- The assembly encodes a binary word: a start tile followed by its decoded symbols
(Definition 16). The word runs along the positive horizontal axis from a start tile that need
not be the origin seed. -/
def Assembly.Encodes {K : TileSystem Label Signal} (A : Assembly K)
    (start : K.tiles) (decode : K.tiles → Option Bool) {n : ℕ}
    (word : Fin n → Bool) : Prop :=
  ∃ offset : ℤ, A.placement.lookup (offset, 0) = some start ∧
    (∀ p : ℤ × ℤ, p ∈ A.placement.keys ↔
      p.2 = 0 ∧ offset ≤ p.1 ∧ p.1 ≤ offset + (n : ℤ)) ∧
    ∀ i : Fin n, ∃ tile : K.tiles,
      A.placement.lookup (offset + (i.val : ℤ) + 1, 0) = some tile ∧
      decode tile = some (word i)

open scoped Classical in
/-- **Conjecture 1**. No zero-error CRN-TAM family constructs every length-`n` binary word in
polynomial expected time.

Determinism means terminal coverage and time means expected global event absorption, given by
finite mean-time equations; the singleton-seed and event-stopping conventions are contextual
readings. -/
theorem conjecture_1 :
    ¬∃ (program : ℕ → Program ℕ ℕ) (C : ℝ) (d n₀ : ℕ),
      0 < C ∧ ∀ n : ℕ,
      let P := program n
      ∃ (start : P.system.tiles) (decode : P.system.tiles → Option Bool)
        (states : Finset (State P.system))
        (events : Finset (Reaction P.system))
        (rate : State P.system → Reaction P.system → NNRat)
        (time : State P.system → ℝ),
        (∀ L, L ∈ states ↔ P.Reachable L) ∧
        (∀ r, r ∈ events ↔ ∃ L ∈ states, P.Possible L r) ∧
        (∀ L ∈ states, ∃ M,
          Relation.ReflTransGen P.Step L M ∧ ¬∃ r, P.Possible M r) ∧
        (∀ L ∈ states, ∀ r ∈ events,
          P.Possible L r →
            r.propensity L ((states.sup State.mass : ℕ) : NNRat) = some (rate L r) ∧
            0 < rate L r) ∧
        (∀ L ∈ states, 0 ≤ time L) ∧
        (∀ L ∈ states, (¬∃ r, P.Possible L r) →
          time L = 0 ∧ ∀ word : Fin n → Bool,
            ∃ A : Assembly P.system,
              0 < L (Species.assembly A) ∧ A.Encodes start decode word) ∧
        (∀ L ∈ states, (∃ r, P.Possible L r) →
          (∑ r ∈ events, if P.Possible L r then
            (rate L r : ℝ) *
              (time L - time (L - r.reactants.toFinsupp + r.products.toFinsupp))
            else 0) = 1) ∧
        (n₀ ≤ n → time P.initialState ≤ C * (n : ℝ) ^ d) := by sorry

end Schiefer2016Time
