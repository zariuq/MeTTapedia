import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBodyNormalization
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-!
# Equality of certified MeTTa calls on finite domains

Compile ordinary source calls against the index of a space snapshot. For a
finite enumeration of captured arguments, the ordered output vector is a
complete key for completed execution on every listed input. A missing
single-answer certificate leaves the comparison undecided.

The observation includes ordered answers, final store and I/O. The input
atoms and any exact instruction budget are independent observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.SpaceCallEquivalence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics Eval PureCallExtraction

/-- The same completed observations, for all initial stores. -/
def AgreeAt (leftProgram rightProgram : Program) (bindings : Subst) (left right : Atom) : Prop :=
  ∀ (before after : Effects.State) (answers input output : List Atom),
    DeclarativeSpec.Runs leftProgram { state := before, control := .evaluate bindings left }
        (.complete after answers input output) ↔
      DeclarativeSpec.Runs rightProgram { state := before, control := .evaluate bindings right }
        (.complete after answers input output)

/-- A table whose entries carry proofs against the source program. -/
inductive Table (program : Program) (source : Atom) : List Subst → Type where
  | nil : Table program source []
  | cons {bindings : Subst} {rest : List Subst}
      (entry : Certified program bindings source) (tail : Table program source rest) :
      Table program source (bindings :: rest)

def Table.values {program : Program} {source : Atom} {inputs : List Subst} :
    Table program source inputs → List Atom
  | .nil => []
  | .cons entry tail => entry.value :: tail.values

def prepareTable (fuel : Nat) (program : Program) (source : Atom) :
    (inputs : List Subst) → Option (Table program source inputs)
  | [] => some .nil
  | bindings :: rest => do
    let entry ← prepare fuel program bindings source
    let tail ← prepareTable fuel program source rest
    return .cons entry tail

private theorem certified_agree_iff {leftProgram rightProgram : Program} {bindings : Subst}
    {left right : Atom} (first : Certified leftProgram bindings left)
    (second : Certified rightProgram bindings right) :
    first.value = second.value ↔ AgreeAt leftProgram rightProgram bindings left right := by
  constructor
  · intro same before after answers input output
    rw [pure_returns_derivation_iff _ _ before before _ _
      (first.returns before) after answers input output,
      pure_returns_derivation_iff _ _ before before _ _
      (second.returns before) after answers input output, same]
  · intro agree
    let state : Effects.State := NamedSpaces.Store.new [] []
    have computed := (pure_returns_derivation_iff _ _ state state _ _
      (first.returns state) state [first.value] [] []).mpr ⟨rfl, rfl, rfl, rfl⟩
    have transferred := (agree state state [first.value] [] []).mp computed
    have observed := (pure_returns_derivation_iff _ _ state state _ _
      (second.returns state) state [first.value] [] []).mp transferred
    exact (List.cons.inj observed.2.1).1

theorem tables_agree_iff {leftProgram rightProgram : Program} {left right : Atom}
    {inputs : List Subst} (first : Table leftProgram left inputs)
    (second : Table rightProgram right inputs) :
    first.values = second.values ↔
      ∀ bindings ∈ inputs, AgreeAt leftProgram rightProgram bindings left right := by
  induction first with
  | nil =>
    cases second
    simp [Table.values]
  | cons entry tail ih =>
    cases second with
    | cons other rest =>
      rw [Table.values, Table.values, List.cons.injEq, certified_agree_iff, ih]
      simp

def equivalentOn? (fuel : Nat) (rows : List Atom) (inputs : List Subst)
    (left right : Atom) : Option Bool := do
  let program := index rows
  let first ← prepareTable fuel program left inputs
  let second ← prepareTable fuel program right inputs
  return decide (first.values = second.values)

/-- A definite verdict decides exactly the completed-run observation on the
specified finite domain. -/
theorem equivalentOn?_exact (fuel : Nat) (rows : List Atom) (inputs : List Subst)
    (left right : Atom) (answer : Bool)
    (observed : equivalentOn? fuel rows inputs left right = some answer) :
    answer = true ↔ ∀ bindings ∈ inputs, AgreeAt (index rows) (index rows) bindings left right := by
  unfold equivalentOn? at observed
  cases first : prepareTable fuel (index rows) left inputs with
  | none => simp [first] at observed
  | some firstTable =>
    cases second : prepareTable fuel (index rows) right inputs with
    | none => simp [first, second] at observed
    | some secondTable =>
      simp [first, second] at observed
      subst answer
      rw [decide_eq_true_eq, tables_agree_iff]

section Symbolic

open Mettapedia.Machines.TypedScalar (Data)
open ScalarBody (Body Compiles Recognized)
open ScalarSource (Environment Captured)

structure EquivalentBodies {Slot : Type} (program : Program) (environment : Environment Slot)
    (left right : Atom) where
  body : Body Slot
  leftCompiled : Compiles program environment left body
  rightCompiled : Recognized program environment right body

/-- Elaborate both source bodies before comparing their canonical scalar
forms. A failed comparison leaves the equation undecided. -/
def equivalentBodies? {Slot : Type} [DecidableEq Slot] (program : Program)
    (environment : Environment Slot) (left right : Atom) :
    Option (EquivalentBodies program environment left right) := do
  let first ← ScalarBody.elaborate program environment left
  let second ← ScalarBody.recognize program environment right first.val
  return ⟨first.val, first.property, second⟩

/-- The equality is uniform over captured inputs on which the common body
returns a value. The caller must already have selected these bodies. -/
theorem EquivalentBodies.agreeAt {Slot : Type} {program : Program} {environment : Environment Slot}
    {left right : Atom} (checked : EquivalentBodies program environment left right)
    (caller : Subst) (locals : Slot → Data) (captured : Captured environment caller locals)
    (value : Atom) (success : checked.body.eval program locals = some value) :
    AgreeAt program program caller left right := by
  have equal := ScalarBody.canonical_equal_eval checked.rightCompiled.body checked.body
    checked.rightCompiled.normalized program locals
  let first : Certified program caller left := ⟨value, fun state =>
    checked.leftCompiled.returns caller state locals captured value success⟩
  let second : Certified program caller right := ⟨value, fun state =>
    checked.rightCompiled.compiled.returns caller state locals captured value (equal.trans success)⟩
  exact (certified_agree_iff first second).mp rfl

end Symbolic

section Examples

open ProgramQuotation

private def bit (value : Int) : Subst := [("x", .grounded (.int value))]
private def flipByTest : Atom := .expression [.symbol "flip-by-test", .var "x"]
private def flipBySubtract : Atom := .expression [.symbol "flip-by-subtract", .var "x"]
private def source : QuotedProgram :=
  petta_source% "(Token a)\n(= (flip-by-test $n) (if (== $n 0) 1 0))\n(= (flip-by-subtract $n) (- 1 $n))"
    sha256 "f1ec6db3c7d61a8d59095bfcd06220c4dcea476b24ed173b5c6a7e7f3840f648"

private def duplicate : QuotedProgram :=
  petta_source% "(= (flip-by-test $n) (if (== $n 0) 1 0))"
    sha256 "53a61d237aec490bc9c3cf0b3e069c926310f6f887d1b3904f58e6ae236f74df"

private def check (rows : List Atom) (inputs : List Subst) : Option Bool :=
  equivalentOn? 8 rows inputs flipByTest flipBySubtract

example : check (loadedAtoms source.program) [bit 0, bit 1] = some true := by decide +kernel

example : check (loadedAtoms source.program) [bit 2] = some false := by decide +kernel

/-- The extra source row supplies a second answer occurrence. -/
example : check (loadedAtoms source.program ++ loadedAtoms duplicate.program) [bit 0, bit 1] = none :=
  by decide +kernel

private def thresholdSource : QuotedProgram :=
  petta_source% "(= (above-direct $n) (> $n 3))\n(= (above-flipped $n) (< 3 $n))"
    sha256 "7f38a62f87b8a45fa643f2c55805443fff07099ecaa38d9eb4e7daa5ad944dad"

private def thresholdProgram : Program := index (loadedAtoms thresholdSource.program)
private def directBody : Atom := thresholdSource.program.equations[0].body
private def flippedBody : Atom := thresholdSource.program.equations[1].body
private def thresholdSlot (name : String) : Option String :=
  if name = "n" then some "n" else none

/-- The recognized comparison law holds at every exact integer input. -/
theorem threshold_agrees (value : Int) :
    AgreeAt thresholdProgram thresholdProgram [("n", .grounded (.int value))]
      directBody flippedBody := by
  let checked := (equivalentBodies? thresholdProgram thresholdSlot directBody flippedBody).get
    (by decide +kernel)
  refine checked.agreeAt _ (fun _ => .integer value) ?_ (.grounded (.bool (decide (3 < value)))) ?_
  · intro name slot present
    by_cases named : name = "n"
    · subst name
      simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, ScalarSource.encode]
    · simp [thresholdSlot, named] at present
  · rfl

end Examples

#print axioms tables_agree_iff
#print axioms equivalentOn?_exact
#print axioms EquivalentBodies.agreeAt
#print axioms threshold_agrees

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.SpaceCallEquivalence
