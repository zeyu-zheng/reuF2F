import Mathlib

/-!
# Finiteness classes arising from Ramsey-theoretic statements in set theory without choice

Authors: Joshua Brot, Mengyang Cao, and David Fernandez-Breton.
Origin: [University of Michigan REU
2018](https://prod.lsa.umich.edu/content/dam/math-assets/math-document/reu-documents/2018FinalPapers/Brot%20and%20Cao.pdf).
Reference: J. Brot, M. Cao, and D. Fernandez-Breton, *Finiteness classes arising from
Ramsey-theoretic statements in set theory without choice*, Ann. Pure Appl. Logic **172** (2021),
no. 6, 102961; arXiv:1910.11025v6. Earlier version: J. Brot and M. Cao, *Some Ramsey-theoretic
statements without the Axiom of Choice*, University of Michigan REU report (2018).
-/

namespace Brot2021Finiteness

/-- The two constants of the ZFA language (pp. 11-12). -/
inductive FunctionSymbol : ℕ → Type
  | empty : FunctionSymbol 0
  | atoms : FunctionSymbol 0

/-- Membership is the only nonlogical relation of ZFA. -/
inductive RelationSymbol : ℕ → Type
  | mem : RelationSymbol 2

/-- The first-order language of ZFA; equality is logical. -/
def language : FirstOrder.Language :=
  { Functions := FunctionSymbol, Relations := RelationSymbol }

local notation:50 x:50 " ∈ₘ " y:51 =>
  FirstOrder.Language.Structure.RelMap (L := language) RelationSymbol.mem ![x, y]
local notation "∅ₘ" =>
  FirstOrder.Language.Structure.funMap (L := language) FunctionSymbol.empty Fin.elim0
local notation "Aₘ" =>
  FirstOrder.Language.Structure.funMap (L := language) FunctionSymbol.atoms Fin.elim0

variable {M : Type*} [language.Structure M]

/-- Sets are the objects that are not atoms (p. 12). -/
def IsSet (x : M) : Prop := ¬x ∈ₘ Aₘ

/-- Internal set inclusion; atoms are not admitted as vacuous subsets. -/
def Subset (x y : M) : Prop :=
  IsSet x ∧ IsSet y ∧ ∀ z : M, z ∈ₘ x → z ∈ₘ y

/-- The internal unordered pair, allowing equal entries and arbitrary objects. -/
def PairSet (x y p : M) : Prop :=
  IsSet p ∧ ∀ z : M, z ∈ₘ p ↔ z = x ∨ z = y

/-- The internal power set: all internal subsets that are sets (p. 12). -/
def Powerset (x p : M) : Prop :=
  IsSet x ∧ IsSet p ∧ ∀ y : M, y ∈ₘ p ↔ Subset y x

/-- Satisfaction of the ZFA axioms without choice (pp. 11-12). The schemes range over
first-order formulas with every finite tuple of parameters, not external predicates. -/
structure ZFA (M : Type*) [language.Structure M] : Prop where
  empty_set : IsSet (∅ₘ : M) ∧ ∀ x : M, ¬x ∈ₘ ∅ₘ
  atoms_set : IsSet (Aₘ : M)
  atoms_spec : ∀ z : M, z ∈ₘ Aₘ ↔ z ≠ ∅ₘ ∧ ∀ x : M, ¬x ∈ₘ z
  extensionality : ∀ x y : M, IsSet x → IsSet y →
    (∀ z : M, z ∈ₘ x ↔ z ∈ₘ y) → x = y
  pairing : ∀ x y : M, ∃ p : M, PairSet x y p
  union_set : ∀ x : M, IsSet x → ∃ u : M, IsSet u ∧
    ∀ z : M, z ∈ₘ u ↔ ∃ y : M, y ∈ₘ x ∧ z ∈ₘ y
  power_set : ∀ x : M, IsSet x → ∃ p : M, Powerset x p
  infinity : ∃ i : M, IsSet i ∧ (∅ₘ : M) ∈ₘ i ∧
    ∀ x : M, x ∈ₘ i → ∃ s : M, s ∈ₘ i ∧ IsSet s ∧
      ∀ z : M, z ∈ₘ s ↔ z ∈ₘ x ∨ z = x
  separation : ∀ (n : ℕ) (φ : language.Formula (Fin (n + 1)))
    (parameters : Fin n → M) (x : M), IsSet x →
    ∃ y : M, IsSet y ∧ ∀ z : M,
      z ∈ₘ y ↔ z ∈ₘ x ∧ φ.Realize (Fin.cons z parameters)
  replacement : ∀ (n : ℕ) (φ : language.Formula (Fin (n + 2)))
    (parameters : Fin n → M) (x : M), IsSet x →
    (∀ a : M, a ∈ₘ x → ∃! b : M, φ.Realize (Fin.cons a (Fin.cons b parameters))) →
    ∃ y : M, IsSet y ∧ ∀ b : M,
      b ∈ₘ y ↔ ∃ a : M, a ∈ₘ x ∧ φ.Realize (Fin.cons a (Fin.cons b parameters))
  foundation : ∀ x : M, IsSet x → (∃ a : M, a ∈ₘ x) →
    ∃ a : M, a ∈ₘ x ∧ ¬∃ b : M, b ∈ₘ a ∧ b ∈ₘ x

/-- Tarski finiteness: every internal nonempty family of internal subsets has an
inclusion-minimal member (p. 12). In ZFA this is equivalent to Definition 1.1(1). -/
def InternallyFinite (x : M) : Prop :=
  IsSet x ∧ ∀ family : M, IsSet family →
    (∀ y : M, y ∈ₘ family → Subset y x) →
    (∃ y : M, y ∈ₘ family) →
    ∃ y : M, y ∈ₘ family ∧
      ∀ z : M, z ∈ₘ family → Subset z y → z = y

/-- The underlying set `[X]^{<ω}` of the Boolean group, including the empty set (pp. 7-8). -/
def FinitePowerset (x p : M) : Prop :=
  IsSet x ∧ IsSet p ∧
    ∀ y : M, y ∈ₘ p ↔ Subset y x ∧ InternallyFinite y

/-- The Kuratowski ordered pair, used for function graphs (p. 12). -/
def OrderedPair (p x y : M) : Prop :=
  ∃ s t : M, PairSet x x s ∧ PairSet x y t ∧ PairSet s t p

/-- Evaluation of an internal function graph. -/
def GraphValue (f x y : M) : Prop :=
  ∃ p : M, p ∈ₘ f ∧ OrderedPair p x y

/-- An internal set of ordered pairs, with exactly the specified domain,
unique values in the specified codomain, and no extraneous graph members. -/
def FunctionGraph (f domain codomain : M) : Prop :=
  IsSet f ∧ IsSet domain ∧ IsSet codomain ∧
    (∀ p : M, p ∈ₘ f → ∃ x y : M,
      x ∈ₘ domain ∧ y ∈ₘ codomain ∧ OrderedPair p x y) ∧
    ∀ x : M, x ∈ₘ domain → ∃! y : M, y ∈ₘ codomain ∧ GraphValue f x y

/-- The Boolean-group operation is symmetric difference, not union (p. 8). -/
def SymmetricDifference (x y s : M) : Prop :=
  IsSet x ∧ IsSet y ∧ IsSet s ∧ ∀ z : M,
    z ∈ₘ s ↔ (z ∈ₘ x ∧ ¬z ∈ₘ y) ∨ (z ∈ₘ y ∧ ¬z ∈ₘ x)

/-- The Boolean sum of the distinct members of a finite `family` (pp. 7-8). It is encoded by an
internal graph on the internal power set with the empty-sum and one-member extension rules, which
gives iterated symmetric difference by internal induction. -/
def BooleanSum (x family sum : M) : Prop :=
  IsSet sum ∧ InternallyFinite family ∧
    (∀ a : M, a ∈ₘ family → Subset a x ∧ InternallyFinite a) ∧
    ∃ subfamilies values graph : M,
      Powerset family subfamilies ∧ FinitePowerset x values ∧
      FunctionGraph graph subfamilies values ∧
      GraphValue graph ∅ₘ ∅ₘ ∧ GraphValue graph family sum ∧
      ∀ g a : M, Subset g family → a ∈ₘ family → ¬a ∈ₘ g →
        ∃ extended u v : M,
          (IsSet extended ∧ ∀ z : M, z ∈ₘ extended ↔ z ∈ₘ g ∨ z = a) ∧
          GraphValue graph g u ∧ GraphValue graph extended v ∧
          SymmetricDifference u a v

/-- **Questions 5.1(1)** (p. 21). Some ZFA model has a set that is H-finite but H3-infinite, with
the Boolean definitions 3.1(2)-(3) and 3.6(2)-(3).

The question is read as model existence, in the separation direction of p. 17. The final clause
asks for one, two or three distinct set members, allowing repeated witnesses but not repeated
summands; empty sums by cancellation are included. -/
theorem question_5_1_1 :
    ∃ (M : Type) (interpretation : language.Structure M),
      letI := interpretation
      Nonempty M ∧ ZFA M ∧
      ∃ x finiteSubsets one two : M,
        IsSet x ∧ FinitePowerset x finiteSubsets ∧
        PairSet ∅ₘ ∅ₘ one ∧ PairSet ∅ₘ one two ∧
        (∃ c : M, FunctionGraph c finiteSubsets two ∧
          ∀ y : M, Subset y finiteSubsets → ¬InternallyFinite y →
            ∃ f g s t i j : M,
              Subset f y ∧ InternallyFinite f ∧ f ≠ ∅ₘ ∧
              Subset g y ∧ InternallyFinite g ∧ g ≠ ∅ₘ ∧
              BooleanSum x f s ∧ BooleanSum x g t ∧
              GraphValue c s i ∧ GraphValue c t j ∧ i ≠ j) ∧
        (∀ d : M, FunctionGraph d finiteSubsets two →
          ∃ y i : M, Subset y finiteSubsets ∧ ¬InternallyFinite y ∧ i ∈ₘ two ∧
            ∀ f : M, Subset f y → InternallyFinite f →
              (∃ a b c : M, ∀ z : M, z ∈ₘ f ↔ z = a ∨ z = b ∨ z = c) →
              ∃ s : M, BooleanSum x f s ∧ GraphValue d s i) := by sorry

end Brot2021Finiteness
