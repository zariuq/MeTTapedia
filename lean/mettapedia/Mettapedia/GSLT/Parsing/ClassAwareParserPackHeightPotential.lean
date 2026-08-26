import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration

/-!
# Static height potentials for class-aware ParserPack plans

The height-bounded reference enumerator is complete once every root
derivation has a common finite height bound.  This module supplies a generic,
presentation-sensitive way to earn such a bound.  A finite table assigns an
integer potential to each result sort; a positive per-codepoint budget pays
for recursive structure that makes input progress.

Validation inspects every lexical and structural row of the supplied plan.
It is therefore not a grammar-name or digest gate.  Nullable recursive cycles
cannot pass unless some consuming item on the cycle pays their height debt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Exact cursor width forced by a terminal matcher. -/
def terminalWidth : TerminalMatcher → Nat
  | .eof => 0
  | .any | .char _ | .class _ => 1

/-- Every terminal witness has exactly the width declared by its matcher. -/
theorem terminal_stop_eq_start_add_width
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile input matcher start stop) :
    stop = start + terminalWidth matcher := by
  cases matched <;> rfl

/-- A finite, inspectable affine height certificate.  Missing sort rows have
potential zero; validation still has to discharge every production using
that value. -/
structure HeightPotential where
  perCodepoint : Nat
  sortPotentials : List (String × Int)
  deriving Repr

def HeightPotential.sortPotential
    (certificate : HeightPotential) (resultSort : String) : Int :=
  (certificate.sortPotentials.find? fun row => row.1 == resultSort).map
      (fun row => row.2) |>.getD 0

/-- Affine debt of an item suffix.  The initial one pays for `nil`; each
terminal pays one constructor and receives its exact input-width credit;
each nonterminal pays one constructor and carries its sort potential. -/
def HeightPotential.itemsDebt
    (certificate : HeightPotential) : List PackItem → Int
  | [] => 1
  | .terminal matcher :: rest =>
      certificate.itemsDebt rest + 1 -
        (certificate.perCodepoint : Int) * terminalWidth matcher
  | .nonterminal resultSort :: rest =>
      certificate.sortPotential resultSort +
        certificate.itemsDebt rest + 1

def HeightPotential.lexicalAdmissible
    (certificate : HeightPotential)
    (production : CompiledLexicalProduction) : Prop :=
  (1 : Int) ≤
    (certificate.perCodepoint : Int) * terminalWidth production.matcher +
      certificate.sortPotential production.resultSort

def HeightPotential.structuralAdmissible
    (certificate : HeightPotential)
    (production : CompiledStructuralProduction) : Prop :=
  certificate.itemsDebt production.items + 1 ≤
    certificate.sortPotential production.resultSort

def HeightPotential.lexicalAdmissible?
    (certificate : HeightPotential)
    (production : CompiledLexicalProduction) : Bool :=
  decide ((1 : Int) ≤
    (certificate.perCodepoint : Int) * terminalWidth production.matcher +
      certificate.sortPotential production.resultSort)

def HeightPotential.structuralAdmissible?
    (certificate : HeightPotential)
    (production : CompiledStructuralProduction) : Bool :=
  decide (certificate.itemsDebt production.items + 1 ≤
    certificate.sortPotential production.resultSort)

@[simp] theorem HeightPotential.lexicalAdmissible?_eq_true_iff
    (certificate : HeightPotential)
    (production : CompiledLexicalProduction) :
    certificate.lexicalAdmissible? production = true ↔
      certificate.lexicalAdmissible production := by
  simp [HeightPotential.lexicalAdmissible?,
    HeightPotential.lexicalAdmissible]

@[simp] theorem HeightPotential.structuralAdmissible?_eq_true_iff
    (certificate : HeightPotential)
    (production : CompiledStructuralProduction) :
    certificate.structuralAdmissible? production = true ↔
      certificate.structuralAdmissible production := by
  simp [HeightPotential.structuralAdmissible?,
    HeightPotential.structuralAdmissible]

/-- The certificate is valid only when its codepoint budget is positive and
every physical production row satisfies its affine height inequality. -/
def HeightPotential.ValidFor
    (certificate : HeightPotential) (plan : CompiledParserPackPlan) : Prop :=
  0 < certificate.perCodepoint ∧
    (∀ production ∈ plan.lexical.productions,
      certificate.lexicalAdmissible production) ∧
    (∀ production ∈ plan.structural,
      certificate.structuralAdmissible production)

/-- Executable validation of the exact supplied plan. -/
def HeightPotential.validate
    (certificate : HeightPotential) (plan : CompiledParserPackPlan) : Bool :=
  decide (0 < certificate.perCodepoint) &&
    ((plan.lexical.productions.all fun production =>
      certificate.lexicalAdmissible? production) &&
    (plan.structural.all fun production =>
      certificate.structuralAdmissible? production))

theorem HeightPotential.validate_eq_true_iff
    (certificate : HeightPotential) (plan : CompiledParserPackPlan) :
    certificate.validate plan = true ↔ certificate.ValidFor plan := by
  simp [HeightPotential.validate, HeightPotential.ValidFor,
    List.all_eq_true]

private theorem span_add
    {start middle stop : Nat} (left : start ≤ middle)
    (right : middle ≤ stop) :
    ((stop - start : Nat) : Int) =
      ((middle - start : Nat) : Int) + ((stop - middle : Nat) : Int) := by
  omega

/-- A valid static potential bounds every complete and item-vector
derivation.  The proof follows the mutually indexed semantic derivations;
no parser implementation participates. -/
theorem HeightPotential.derivation_height_le
    {certificate : HeightPotential} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan}
    (valid : certificate.ValidFor plan) :
    (∀ {input resultSort start stop tree}
        (derivation : ParserPackDerivesAt profile plan input
          resultSort start stop tree),
      (derivation.height : Int) ≤
        (certificate.perCodepoint : Int) * (stop - start : Nat) +
          certificate.sortPotential resultSort) ∧
    (∀ {input items start stop children}
        (derivation : ParserPackItemsDeriveAt profile plan input
          items start stop children),
      (derivation.height : Int) ≤
        (certificate.perCodepoint : Int) * (stop - start : Nat) +
          certificate.itemsDebt items) := by
  constructor
  · intro input resultSort start stop tree derivation
    induction derivation using ParserPackDerivesAt.rec
      (motive_2 := fun items start stop children itemDerivation =>
        (itemDerivation.height : Int) ≤
          (certificate.perCodepoint : Int) * (stop - start : Nat) +
            certificate.itemsDebt items) with
    | lexical position positionValid matcherExact resultSortExact
        _ matched =>
        have admitted := valid.2.1
          (plan.lexical.productions.get ⟨position, positionValid⟩)
          (List.get_mem _ _)
        simp only [HeightPotential.lexicalAdmissible] at admitted
        rw [matcherExact, resultSortExact] at admitted
        rcases matched with ⟨matched, childrenExact⟩
        cases matched <;>
          simpa [HeightPotential.lexicalAdmissible, terminalWidth,
            ParserPackDerivesAt.height] using admitted
    | structural position positionValid resultSortExact _ body bodyIH =>
        have admitted := valid.2.2
          (plan.structural.get ⟨position, positionValid⟩)
          (List.get_mem _ _)
        simp only [ParserPackDerivesAt.height]
        rw [← resultSortExact]
        exact le_trans (Int.add_le_add_right bodyIH 1) (by
          simpa [add_assoc] using
            Int.add_le_add_left admitted
              ((certificate.perCodepoint : Int) *
                (stop - start : Nat)))
    | nil => simp [ParserPackItemsDeriveAt.height,
        HeightPotential.itemsDebt]
    | terminal matched rest restIH =>
        rename_i matcher itemStart middle restItems itemStop restChildren
        have startMiddle :=
          ClassAwareParserPackEnumeration.TerminalMatchesAt.start_le_stop
            matched
        have middleStop :=
          ClassAwareParserPackEnumeration.ParserPackItemsDeriveAt.start_le_stop
            rest
        have widthEq := terminal_stop_eq_start_add_width matched
        simp only [ParserPackItemsDeriveAt.height,
          HeightPotential.itemsDebt]
        rw [span_add startMiddle middleStop, mul_add]
        have spanWidth : middle - itemStart = terminalWidth matcher := by
          omega
        rw [spanWidth]
        omega
    | nonterminal head rest headIH restIH =>
        have startMiddle :=
          ClassAwareParserPackEnumeration.ParserPackDerivesAt.start_le_stop
            head
        have middleStop :=
          ClassAwareParserPackEnumeration.ParserPackItemsDeriveAt.start_le_stop
            rest
        simp only [ParserPackItemsDeriveAt.height,
          HeightPotential.itemsDebt]
        rw [span_add startMiddle middleStop, mul_add]
        omega
  · intro input items start stop children derivation
    induction derivation using ParserPackItemsDeriveAt.rec
      (motive_1 := fun resultSort start stop tree completeDerivation =>
        (completeDerivation.height : Int) ≤
          (certificate.perCodepoint : Int) * (stop - start : Nat) +
            certificate.sortPotential resultSort) with
    | lexical position positionValid matcherExact resultSortExact
        _ matched =>
        have admitted := valid.2.1
          (plan.lexical.productions.get ⟨position, positionValid⟩)
          (List.get_mem _ _)
        simp only [HeightPotential.lexicalAdmissible] at admitted
        rw [matcherExact, resultSortExact] at admitted
        rcases matched with ⟨matched, childrenExact⟩
        cases matched <;>
          simpa [HeightPotential.lexicalAdmissible, terminalWidth,
            ParserPackDerivesAt.height] using admitted
    | structural position positionValid resultSortExact _ body bodyIH =>
        have admitted := valid.2.2
          (plan.structural.get ⟨position, positionValid⟩)
          (List.get_mem _ _)
        simp only [ParserPackDerivesAt.height]
        rw [← resultSortExact]
        exact le_trans (Int.add_le_add_right bodyIH 1) (by
          simpa [add_assoc] using
            Int.add_le_add_left admitted
              ((certificate.perCodepoint : Int) *
                (stop - start : Nat)))
    | nil => simp [ParserPackItemsDeriveAt.height,
        HeightPotential.itemsDebt]
    | terminal matched rest restIH =>
        rename_i matcher itemStart middle restItems itemStop restChildren
        have startMiddle :=
          ClassAwareParserPackEnumeration.TerminalMatchesAt.start_le_stop
            matched
        have middleStop :=
          ClassAwareParserPackEnumeration.ParserPackItemsDeriveAt.start_le_stop
            rest
        have widthEq := terminal_stop_eq_start_add_width matched
        simp only [ParserPackItemsDeriveAt.height,
          HeightPotential.itemsDebt]
        rw [span_add startMiddle middleStop, mul_add]
        have spanWidth : middle - itemStart = terminalWidth matcher := by
          omega
        rw [spanWidth]
        omega
    | nonterminal head rest headIH restIH =>
        have startMiddle :=
          ClassAwareParserPackEnumeration.ParserPackDerivesAt.start_le_stop
            head
        have middleStop :=
          ClassAwareParserPackEnumeration.ParserPackItemsDeriveAt.start_le_stop
            rest
        simp only [ParserPackItemsDeriveAt.height,
          HeightPotential.itemsDebt]
        rw [span_add startMiddle middleStop, mul_add]
        omega

/-- Complete-derivation projection of the mutual height theorem. -/
theorem HeightPotential.complete_height_le
    {certificate : HeightPotential} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan}
    (valid : certificate.ValidFor plan)
    {input resultSort start stop tree}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree) :
    (derivation.height : Int) ≤
      (certificate.perCodepoint : Int) * (stop - start : Nat) +
        certificate.sortPotential resultSort :=
  (certificate.derivation_height_le valid).1 derivation

/-- A valid potential yields the natural-number fuel used by the independent
root enumerator. -/
def HeightPotential.rootFuel
    (certificate : HeightPotential) (plan : CompiledParserPackPlan)
    (input : List Nat) : Nat :=
  certificate.perCodepoint * input.length +
    Int.toNat (certificate.sortPotential plan.lexical.startSort)

/-- Static validation turns the affine semantic theorem into the exact root
height premise required by exhaustive reference enumeration. -/
theorem HeightPotential.rootHeightBound
    {certificate : HeightPotential} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan}
    (valid : certificate.ValidFor plan) (input : List Nat) :
    RootHeightBound profile plan input
      (certificate.rootFuel plan input) := by
  intro tree derivation
  have affine := certificate.complete_height_le valid derivation
  have potentialLe :
      certificate.sortPotential plan.lexical.startSort ≤
        Int.toNat (certificate.sortPotential plan.lexical.startSort) := by
    cases potential : certificate.sortPotential plan.lexical.startSort with
    | ofNat value => simp
    | negSucc value => simp; omega
  have affineNatural :
      (derivation.height : Int) ≤
        (certificate.rootFuel plan input : Nat) := by
    rw [show (input.length - 0 : Nat) = input.length by omega] at affine
    calc
      (derivation.height : Int) ≤
          (certificate.perCodepoint : Int) * input.length +
            certificate.sortPotential plan.lexical.startSort := affine
      _ ≤ (certificate.perCodepoint : Int) * input.length +
            Int.toNat (certificate.sortPotential plan.lexical.startSort) :=
          Int.add_le_add_left potentialLe _
      _ = (certificate.rootFuel plan input : Nat) := by
          simp [HeightPotential.rootFuel]
  exact_mod_cast affineNatural

/-! ## Controls -/

private def consumingLoopPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "HeightPotentialCanary"
    startSort := "Many"
    classes := []
    productions := [{
      label := "letter"
      resultSort := "Letter"
      matcher := .any
      childSlots := [0]
    }]
  }
  structural := [
    { label := "many-empty", resultSort := "Many", items := [],
      childSlots := [], source := {
        label := "many-empty", category := "Many", params := [],
        syntaxPattern := [] } },
    { label := "many-cons", resultSort := "Many",
      items := [.nonterminal "Letter", .nonterminal "Many"],
      childSlots := [0, 1], source := {
        label := "many-cons", category := "Many", params := [],
        syntaxPattern := [] } }]
}

private def consumingLoopPotential : HeightPotential := {
  perCodepoint := 6
  sortPotentials := [("Letter", -5), ("Many", 2)]
}

theorem consuming_loop_is_admissible :
    consumingLoopPotential.validate consumingLoopPlan = true := by
  decide

/-- Negative control: the same recursive grammar fails when the lexical
child receives no per-codepoint credit. -/
private def noProgressPotential : HeightPotential := {
  perCodepoint := 1
  sortPotentials := [("Letter", 0), ("Many", 2)]
}

theorem insufficient_progress_is_rejected :
    noProgressPotential.validate consumingLoopPlan = false := by
  decide

/-- Negative control: a zero-width self-loop cannot obtain a finite affine
height certificate merely by raising its sort potential. -/
private def zeroWidthLoopPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "ZeroWidthLoopCanary"
    startSort := "Loop"
    classes := []
    productions := []
  }
  structural := [
    { label := "loop", resultSort := "Loop",
      items := [.nonterminal "Loop"], childSlots := [0], source := {
        label := "loop", category := "Loop", params := [],
        syntaxPattern := [] } }]
}

private def zeroWidthLoopPotential : HeightPotential := {
  perCodepoint := 100
  sortPotentials := [("Loop", 1000000)]
}

theorem zero_width_loop_is_rejected :
    zeroWidthLoopPotential.validate zeroWidthLoopPlan = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareParserPackHeightPotential
