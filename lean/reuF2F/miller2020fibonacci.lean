import Mathlib

/-!
# The Fibonacci Quilt Game

Authors: Steven J. Miller and Alexandra Newlon.
Origin: [Williams College SMALL REU
2019](https://web.williams.edu/Mathematics/sjmiller/public_html/math/talks/small2019/Fibonacci_Quilt_Game_Umass_Slides.pdf).
Reference: S. J. Miller and A. Newlon, *The Fibonacci Quilt Game*, arXiv:1909.01938, 2019.
-/

noncomputable section

namespace Miller2020Fibonacci

open scoped Topology Real

section Setup

attribute [local instance] Classical.propDecidable

/-- A game state: the finite multiset of Fibonacci Quilt terms, as the count function
`i ↦` number of copies of `q_i`. Source indices start at `1`; valid states exclude `0`. -/
abbrev GameState : Type := ℕ →₀ ℕ

/-- The elementary moves (Definition 1.7). -/
inductive MoveKind where
  | consecutive (i : ℕ) : MoveKind
  | distanceFour (i : ℕ) : MoveKind
  | duplicateToSingle (i : ℕ) : MoveKind
  | duplicateThree : MoveKind
  | duplicateFourToOneSix : MoveKind
  | duplicateFourToThreeFive : MoveKind
  | duplicateFive : MoveKind
  | duplicateSixToTwoEight : MoveKind
  | duplicateSixToThreeSeven : MoveKind
  | duplicateLarge (i : ℕ) : MoveKind
  | distanceThree (i : ℕ) : MoveKind
  | oneAndThree : MoveKind

/-- Number of copies of `q_j` consumed by a move. -/
def moveConsumes : MoveKind → ℕ → ℕ
  | MoveKind.consecutive i, j => (if j = i then 1 else 0) + if j = i + 1 then 1 else 0
  | MoveKind.distanceFour i, j => (if j = i then 1 else 0) + if j = i + 4 then 1 else 0
  | MoveKind.duplicateToSingle i, j => if j = i then 2 else 0
  | MoveKind.duplicateThree, j => if j = 3 then 2 else 0
  | MoveKind.duplicateFourToOneSix, j => if j = 4 then 2 else 0
  | MoveKind.duplicateFourToThreeFive, j => if j = 4 then 2 else 0
  | MoveKind.duplicateFive, j => if j = 5 then 2 else 0
  | MoveKind.duplicateSixToTwoEight, j => if j = 6 then 2 else 0
  | MoveKind.duplicateSixToThreeSeven, j => if j = 6 then 2 else 0
  | MoveKind.duplicateLarge i, j => if j = i then 2 else 0
  | MoveKind.distanceThree i, j => (if j = i then 1 else 0) + if j = i + 3 then 1 else 0
  | MoveKind.oneAndThree, j => (if j = 1 then 1 else 0) + if j = 3 then 1 else 0

/-- Number of copies of `q_j` produced by a move. -/
def moveProduces : MoveKind → ℕ → ℕ
  | MoveKind.consecutive i, j =>
      if i = 1 then if j = 3 then 1 else 0
      else if 2 ≤ i then if j = i + 3 then 1 else 0
      else 0
  | MoveKind.distanceFour i, j =>
      if i = 1 then (if j = 2 then 1 else 0) + if j = 4 then 1 else 0
      else if 2 ≤ i then if j = i + 5 then 1 else 0
      else 0
  | MoveKind.duplicateToSingle i, j =>
      if i = 1 then if j = 2 then 1 else 0
      else if i = 2 then if j = 4 then 1 else 0
      else 0
  | MoveKind.duplicateThree, j => (if j = 2 then 1 else 0) + if j = 4 then 1 else 0
  | MoveKind.duplicateFourToOneSix, j => (if j = 1 then 1 else 0) + if j = 6 then 1 else 0
  | MoveKind.duplicateFourToThreeFive, j => (if j = 3 then 1 else 0) + if j = 5 then 1 else 0
  | MoveKind.duplicateFive, j => (if j = 1 then 1 else 0) + if j = 7 then 1 else 0
  | MoveKind.duplicateSixToTwoEight, j => (if j = 2 then 1 else 0) + if j = 8 then 1 else 0
  | MoveKind.duplicateSixToThreeSeven, j => (if j = 3 then 1 else 0) + if j = 7 then 1 else 0
  | MoveKind.duplicateLarge i, j =>
      if 7 ≤ i then (if j = i - 5 then 1 else 0) + if j = i + 2 then 1 else 0 else 0
  | MoveKind.distanceThree i, j =>
      if i = 1 ∨ i = 2 then if j = i + 4 then 1 else 0
      else if i = 3 then (if j = 1 then 1 else 0) + if j = 7 then 1 else 0
      else if i = 4 ∨ i = 5 then (if j = 1 then 1 else 0) + if j = i + 4 then 1 else 0
      else if i = 6 then (if j = 2 then 1 else 0) + if j = 10 then 1 else 0
      else if 7 ≤ i then (if j = i - 5 then 1 else 0) + if j = i + 4 then 1 else 0
      else 0
  | MoveKind.oneAndThree, j => if j = 4 then 1 else 0

/-- Applicability side conditions for all move kinds except the special side condition on
Rule (2a), `q_1 ∧ q_5 → q_2 ∧ q_4`. -/
def MoveKind.ApplicableExceptRuleTwoA (mv : MoveKind) : Prop :=
  match mv with
  | MoveKind.consecutive i => i = 1 ∨ 2 ≤ i
  | MoveKind.distanceFour i => 2 ≤ i
  | MoveKind.duplicateToSingle i => i = 1 ∨ i = 2
  | MoveKind.duplicateThree => True
  | MoveKind.duplicateFourToOneSix => True
  | MoveKind.duplicateFourToThreeFive => True
  | MoveKind.duplicateFive => True
  | MoveKind.duplicateSixToTwoEight => True
  | MoveKind.duplicateSixToThreeSeven => True
  | MoveKind.duplicateLarge i => 7 ≤ i
  | MoveKind.distanceThree i => 1 ≤ i
  | MoveKind.oneAndThree => True

/-- A move other than Rule (2a) is legally available from `st`. -/
def HasLegalMoveExceptRuleTwoA (st : GameState) : Prop :=
  ∃ (mv : MoveKind) (next : GameState),
    st 0 = 0 ∧ MoveKind.ApplicableExceptRuleTwoA mv ∧
      (∀ j : ℕ, moveConsumes mv j ≤ st j) ∧
        (∀ j : ℕ, next j = st j - moveConsumes mv j + moveProduces mv j) ∧
          next 0 = 0

/-- Applicability side conditions for the moves, where Rule (2a), `q_1 ∧ q_5 → q_2 ∧ q_4`, may
be used only when no other move is possible (Definition 1.7). -/
def MoveKind.Applicable (mv : MoveKind) (st : GameState) : Prop :=
  match mv with
  | MoveKind.consecutive i => i = 1 ∨ 2 ≤ i
  | MoveKind.distanceFour i =>
      (i = 1 ∧ 0 < st 1 ∧ 0 < st 5 ∧ ¬HasLegalMoveExceptRuleTwoA st) ∨ 2 ≤ i
  | MoveKind.duplicateToSingle i => i = 1 ∨ i = 2
  | MoveKind.duplicateThree => True
  | MoveKind.duplicateFourToOneSix => True
  | MoveKind.duplicateFourToThreeFive => True
  | MoveKind.duplicateFive => True
  | MoveKind.duplicateSixToTwoEight => True
  | MoveKind.duplicateSixToThreeSeven => True
  | MoveKind.duplicateLarge i => 7 ≤ i
  | MoveKind.distanceThree i => 1 ≤ i
  | MoveKind.oneAndThree => True

/-- Legal Fibonacci Quilt Game moves (Definition 1.7). -/
def LegalMove (st : GameState) (mv : MoveKind) (next : GameState) : Prop :=
  st 0 = 0 ∧ MoveKind.Applicable mv st ∧
    (∀ j : ℕ, moveConsumes mv j ≤ st j) ∧
      (∀ j : ℕ, next j = st j - moveConsumes mv j + moveProduces mv j) ∧
        next 0 = 0

/-- One recorded move in a finite Fibonacci Quilt game. -/
structure PlayedMove where
  /-- The kind of move played. -/
  kind : MoveKind
  /-- The game state after the move. -/
  stateAfter : GameState

/-- A finite play whose consecutive states are related by legal Fibonacci Quilt moves. -/
def IsLegalPlayFrom : GameState → List PlayedMove → Prop
  | _, [] => True
  | st, step :: rest =>
      LegalMove st step.kind step.stateAfter ∧ IsLegalPlayFrom step.stateAfter rest

end Setup

/-- **Conjecture 1.10**. Standardized lengths of the Quilt game of Definition 1.7 converge to a
standard Gaussian under uniform legal-move choices.

The game stops when no listed move remains, without terminal-value conditioning, and Section 2.2
supplies the moment normalization. The literal rules are kept although Rule (3f),
`2q6 → q3 + q7`, changes value 14 to 12, contrary to the source's conservation description. -/
theorem conjecture_1_10_random_game_lengths_converge_to_gaussian
    (μ : ℕ → List PlayedMove → ℝ)
    (hlaw : ∀ N : ℕ,
      (∀ play, 0 ≤ μ N play) ∧
      (∀ play, μ N play ≠ 0 →
        IsLegalPlayFrom (Finsupp.single 1 N) play ∧
          ¬∃ mv next,
            LegalMove ((play.map PlayedMove.stateAfter).getLastD (Finsupp.single 1 N)) mv next) ∧
      (Function.support (μ N)).Finite ∧
      (∑' play, μ N play) = 1 ∧
      (∀ pref : List PlayedMove,
        IsLegalPlayFrom (Finsupp.single 1 N) pref →
        let st := (pref.map PlayedMove.stateAfter).getLastD (Finsupp.single 1 N)
        (∃ mv next, LegalMove st mv next) →
        ∃ choices : Finset (MoveKind × GameState),
          (∀ choice, choice ∈ choices ↔ LegalMove st choice.1 choice.2) ∧
          choices.Nonempty ∧
          ∀ choice₁ ∈ choices, ∀ choice₂ ∈ choices,
            (∑' tail : List PlayedMove,
              μ N (pref ++
                ({ kind := choice₁.1, stateAfter := choice₁.2 } : PlayedMove) :: tail)) =
            (∑' tail : List PlayedMove,
              μ N (pref ++
                ({ kind := choice₂.1, stateAfter := choice₂.2 } : PlayedMove) :: tail)))) :
    let mean : ℕ → ℝ := fun N ↦ ∑' play, μ N play * (play.length : ℝ)
    let variance : ℕ → ℝ := fun N ↦
      ∑' play, μ N play * ((play.length : ℝ) - mean N) ^ 2
    ∀ a b : ℝ, a < b →
      Filter.Tendsto
        (fun N : ℕ ↦ ∑' play : List PlayedMove,
          if a ≤ ((play.length : ℝ) - mean N) / √(variance N) ∧
              ((play.length : ℝ) - mean N) / √(variance N) ≤ b then
            μ N play
          else 0)
        Filter.atTop
        (𝓝 (∫ x in a..b, (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2))) := by
  sorry

end Miller2020Fibonacci
