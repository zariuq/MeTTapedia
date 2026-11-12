import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.Triangle
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.PeTTaAndHE
import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# Named differences between HE and PeTTa, as distinguishing controls

A distinction, in Ben Goertzel's sense, is an observation that tells two systems apart. Each control
below is one program, with HE's outcome and PeTTa's outcome proved on the tree's own models:

* HE: the space operations of `HE.Space` and the executable evaluator `HE.evalAtom`;
* PeTTa: the streaming machine (`PeTTa.Streaming`) and its store projection
  (`PeTTa.RunsAsFirings`).

1. `removal`: `!(remove-atom &self (p a))` on a space holding `(p a)` twice. HE removes one
   occurrence (`HE.Space.remove`): one `(p a)` remains. PeTTa's request takes every copy, and
   nothing remains. On the step this is the store reached: the triangle fails on it.
2. `return_type_reevaluation`: one body under two declared return types. HE evaluates a call's
   result again against the declared return type: `(give-atom (+ 1 2))` with `(-> Atom Atom)`
   answers `(+ 1 2)`, `(give-undef (+ 1 2))` with `(-> Atom %Undefined%)` answers `3`. PeTTa
   answers the same for both.
3. `held_argument_under_undefined`: the Prime merge's `held_arguments` case. A parameter declared
   `Atom` holds its argument as data; returned under the range `%Undefined%`, HE evaluates it
   (`(give-undef (f a))` answers `5` where `(= (f a) 5)`), PeTTa returns it as held (`(f a)`).
4. `conjunctive_match`: `(match &self (, (p $x) q) (let $_ (remove-atom &self q) $x))` on
   `{(p 1), (p 2), q}`. HE takes the entry view for the whole query: one read of its pre-state, so both
   solutions answer. SWI-PeTTa calls the second conjunct again for each solution of the first, on the
   store the earlier bodies left, so one solution answers; PeTTa's pending fix adopts the entry view.
   On the step HE's view is one firing reading the world (`he_reads_world`); PeTTa's today is a chain
   of reads interleaved with the bodies' takes. The two readings are the models of
   `PeTTaAndHE.Controls` (the streaming machine has no conjunctive `match` to run this on).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep

namespace NamedDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space GroundedDispatch evalAtom Bindings)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

/-! ## Programs -/

def app (name : String) (args : List Atom) : Atom := .expression (.symbol name :: args)
def arrow (args : List Atom) : Atom := .expression (.symbol "->" :: args)
def decl (name : String) (type : Atom) : Atom := .expression [.symbol ":", .symbol name, type]
def eqn (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]

/-- `(+ 1 2)`. -/
def sum12 : Atom := app "+" [.grounded (.int 1), .grounded (.int 2)]

/-- `(f a)`, which reduces to `5`. -/
def fa : Atom := app "f" [.symbol "a"]

/-- HE's grounded `+` on integers. -/
def plus : GroundedDispatch where
  isExecutable := fun a => match a with
    | .symbol "+" => true
    | _ => false
  execute := fun op args => match op, args with
    | .symbol "+", [.grounded (.int m), .grounded (.int n)] =>
        .ok [(.grounded (.int (m + n)), default)]
    | _, _ => .noReduce

/-- The program of controls 2 and 3: `(= (f a) 5)`, and `give-atom`, `give-undef` returning their
`Atom` parameter under the ranges `Atom` and `%Undefined%`. -/
def programAtoms : List Atom :=
  [eqn fa (.grounded (.int 5)),
   decl "give-atom" (arrow [.symbol "Atom", .symbol "Atom"]),
   eqn (app "give-atom" [.var "x"]) (.var "x"),
   decl "give-undef" (arrow [.symbol "Atom", .symbol "%Undefined%"]),
   eqn (app "give-undef" [.var "x"]) (.var "x")]

def heSpace : Space := Space.ofList programAtoms

/-- The same program loaded in PeTTa. -/
def pettaProgram : SpaceSemantics.Program :=
  { equations := [⟨"f", [.symbol "a"], .grounded (.int 5)⟩,
      ⟨"give-atom", [.var "x"], .var "x"⟩, ⟨"give-undef", [.var "x"], .var "x"⟩],
    declarations := [decl "give-atom" (arrow [.symbol "Atom", .symbol "Atom"]),
      decl "give-undef" (arrow [.symbol "Atom", .symbol "%Undefined%"])] }

def pettaStore : Effects.State := NamedSpaces.Store.new programAtoms []

/-- HE's answers to an expression in the program's space. -/
def heAnswers (expression : Atom) : List Atom :=
  (evalAtom heSpace plus expression Atom.undefinedType Bindings.empty 40).map Prod.fst

/-- PeTTa's answers to an expression against the loaded program. -/
def pettaAnswers (expression : Atom) : List Atom :=
  Streaming.values (Streaming.advance pettaProgram 60 (Streaming.enter { state := pettaStore } expression))

/-! ## 1. Removal -/

/-- `(p a)`. -/
def pa : Atom := app "p" [.symbol "a"]

def dupAtoms : List Atom := [pa, pa]
def dupStore : Effects.State := NamedSpaces.Store.new dupAtoms []
def removePa : Atom := app "remove-atom" [.symbol "&self", pa]
def noProgram : SpaceSemantics.Program := { equations := [], declarations := [] }

/-- **Control 1: removal.** On a space holding `(p a)` twice, HE's removal leaves one `(p a)`;
PeTTa's `remove-atom` is one request taking both copies, and nothing remains. The HE side here
applies HE's `Space.remove` directly, not the machine; removal on HE's world machine is
`TriangleFootprints.WorldRemoval.he_removes_one_occurrence` and
`TriangleFootprints.HonestWrites.remove_takes_one`. -/
theorem removal :
    (Space.remove (Space.ofList dupAtoms) pa).atoms = [pa] ∧
      (requests rowSupply noProgram 30 (Streaming.enter { state := dupStore } removePa)
          (Row.load 0 dupAtoms)).map Controls.shape =
        [([⟨0, .self, pa⟩, ⟨1, .self, pa⟩], [], [])] ∧
      (Streaming.advance noProgram 30 (Streaming.enter { state := dupStore } removePa)).world.state.core
        = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 2. Re-evaluation by return type -/

/-- **Control 2: HE re-evaluates by return type.** The same body under the ranges `Atom` and
`%Undefined%` answers `(+ 1 2)` and `3` in HE; PeTTa answers `(+ 1 2)` under both. -/
theorem return_type_reevaluation :
    heAnswers (app "give-atom" [sum12]) = [sum12] ∧
      heAnswers (app "give-undef" [sum12]) = [.grounded (.int 3)] ∧
      pettaAnswers (app "give-atom" [sum12]) = [sum12] ∧
      pettaAnswers (app "give-undef" [sum12]) = [sum12] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 3. Held arguments under `%Undefined%` -/

/-- **Control 3: a held argument returned under `%Undefined%`.** HE evaluates `(f a)` on return and
answers `5`; PeTTa returns the held `(f a)`. Under the range `Atom` both return `(f a)`. -/
theorem held_argument_under_undefined :
    heAnswers (app "give-undef" [fa]) = [.grounded (.int 5)] ∧
      pettaAnswers (app "give-undef" [fa]) = [fa] ∧
      heAnswers (app "give-atom" [fa]) = [fa] ∧
      pettaAnswers (app "give-atom" [fa]) = [fa] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 4. Conjunctive match -/

open DialectsAsStrategies.PeTTaHE.Controls (perMatch perConjunct snapshot_granularity)

/-- **Control 4: conjunctive match.** On `{(p 1), (p 2), q}` (atoms `1`, `2`, `9`), with a body that
removes `q` and answers `$x`: the entry view, HE's and PeTTa's after its pending fix, answers both
solutions; SWI-PeTTa's per-conjunct reading answers one. The entry view's answers are a function of
the store the match entered. -/
theorem conjunctive_match :
    perMatch {1, 2, 9} = ([1, 2], {1, 2}) ∧ perConjunct {1, 2, 9} = ([1], {1, 2}) ∧
      ∀ s : Multiset ℕ, (perMatch s).1 = ([1, 2] : List ℕ).filter fun x => decide (x ∈ s) && decide (9 ∈ s) :=
  ⟨snapshot_granularity.1, snapshot_granularity.2, fun _ => rfl⟩

end NamedDifferences

#print axioms NamedDifferences.removal
#print axioms NamedDifferences.return_type_reevaluation
#print axioms NamedDifferences.held_argument_under_undefined
#print axioms NamedDifferences.conjunctive_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
