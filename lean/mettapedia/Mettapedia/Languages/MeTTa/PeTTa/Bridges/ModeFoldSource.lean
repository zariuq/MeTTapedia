import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBodyNormalization
import Mettapedia.Languages.MeTTa.PeTTa.FoldSource
import Mettapedia.Machines.GroupedModeRegion

/-!
# Uniform extraction of the sorted mode callback

The source compiler elaborates an actual callback body to sorted scalar IR,
normalizes it, and checks the mode-transition schema. The callback name and
formal-variable spellings are parameters. Accepted bodies have a uniform
source law for every natural input and every four-field accumulator, not just
the accumulator values encountered in a test run.

The whole-fold result uses the captured host driver and the independent
sorted-run/histogram theorem. It does not install foldl-atom into the older
general evaluator or admit effects in the enclosing label-publication loop.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeFoldSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Machines.TypedScalar
open Mettapedia.Machines.ModeAggregation
open Eval SpaceSemantics MeTTaIL.WireKit

abbrev RunState := SortedRun.State

inductive Slot | current | count | best | bestCount | item
  deriving DecidableEq

structure Names where
  current : String
  count : String
  best : String
  bestCount : String
  item : String
  deriving DecidableEq

def Names.fields (names : Names) : List String := [names.current, names.count, names.best, names.bestCount]
def Names.all (names : Names) : List String := names.fields ++ [names.item]

def environment (names : Names) : ScalarSource.Environment Slot := fun name =>
  if name = names.current then some .current else
  if name = names.count then some .count else
  if name = names.best then some .best else
  if name = names.bestCount then some .bestCount else
  if name = names.item then some .item else none

def labelData : Option Nat → Data
  | none => .symbol "none"
  | some label => .integer label

def labelAtom (label : Option Nat) : Atom := ScalarSource.encode (kind := .data) (labelData label)

def encode (state : RunState) : Atom :=
  .expression [labelAtom state.current, number state.runCount, labelAtom state.best.label, number state.best.count]

def locals (state : RunState) (item : Nat) : Slot → Data
  | .current => labelData state.current
  | .count => .integer state.runCount
  | .best => labelData state.best.label
  | .bestCount => .integer state.best.count
  | .item => .integer item

def callee (names : Names) (state : RunState) (item : Nat) : Subst :=
  [(names.item, number item), (names.bestCount, number state.best.count),
    (names.best, labelAtom state.best.label), (names.count, number state.runCount),
    (names.current, labelAtom state.current)]

theorem captured (names : Names) (distinct : names.all.Nodup) (state : RunState) (item : Nat) :
    ScalarSource.Captured (environment names) (callee names state item) (locals state item) := by
  simp only [Names.all, Names.fields, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro name slot found
  unfold environment at found
  split_ifs at found <;> cases found
  all_goals subst name
  all_goals simp_all [callee, Subst.lookup, locals, labelAtom, number, encoded,
    MeTTaIL.CettaWireAtom.encode, ScalarSource.encode, ne_comm]

def read (slot : Slot) : ScalarBody.Packed Slot := ⟨.data, .read slot⟩
def one : ScalarBody.Packed Slot := ⟨.data, .literal (.integer 1)⟩

def ir : ScalarBody.Body Slot :=
  .branch (.binary .equal (.read .item) (.read .current))
    (.tuple [read .current, ⟨.data, .binary .add (.read .count) (.literal (.integer 1))⟩,
      read .best, read .bestCount])
    (.branch (.binary .gt (.read .count) (.read .bestCount))
      (.tuple [read .item, one, read .current, read .count])
      (.tuple [read .item, one, read .best, read .bestCount]))

theorem ir_uniform (program : Program) (state : RunState) (item : Nat) :
    ir.eval program (locals state item) = some (encode (SortedRun.step state item)) := by
  cases current : state.current with
  | none =>
      by_cases larger : state.best.count < state.runCount <;>
        simp [ir, ScalarBody.Body.eval, ScalarBody.evalFields, ScalarBody.evalField, read, one,
          Expr.eval, Binary.eval, valueEq, locals, labelData, current, ScalarSource.encode,
          ScalarBody.liveHead, encode, labelAtom, number, encoded, MeTTaIL.CettaWireAtom.encode,
          SortedRun.step, SortedRun.finish, larger]
  | some label =>
      by_cases same : label = item
      · subst label
        simp [ir, ScalarBody.Body.eval, ScalarBody.evalFields, ScalarBody.evalField, read, one,
          Expr.eval, Binary.eval, valueEq, locals, labelData, current, ScalarSource.encode,
          ScalarBody.liveHead, encode, labelAtom, number, encoded, MeTTaIL.CettaWireAtom.encode, SortedRun.step]
      · by_cases larger : state.best.count < state.runCount <;>
          simp [ir, ScalarBody.Body.eval, ScalarBody.evalFields, ScalarBody.evalField, read, one,
            Expr.eval, Binary.eval, valueEq, locals, labelData, current, ScalarSource.encode,
            ScalarBody.liveHead, encode, labelAtom, number, encoded, MeTTaIL.CettaWireAtom.encode, SortedRun.step, SortedRun.finish,
            larger, same, Ne.symm same]

abbrev BodyCertificate (program : Program) (names : Names) (source : Atom) :=
  ScalarBody.Recognized program (environment names) source ir

def inferBody (program : Program) (names : Names) (source : Atom) : Option (BodyCertificate program names source) :=
  ScalarBody.recognize program (environment names) source ir

theorem BodyCertificate.returns {program : Program} {names : Names} {source : Atom}
    (certificate : BodyCertificate program names source) (distinct : names.all.Nodup)
    (world : Effects.State) (state : RunState) (item : Nat) :
    PureReturns program (callee names state item) world source world (encode (SortedRun.step state item)) := by
  apply certificate.compiled.returns _ world (locals state item) (captured names distinct state item)
  rw [ScalarBody.canonical_equal_eval certificate.body ir certificate.normalized, ir_uniform]

def arguments (names : Names) : List Atom := [.expression (names.fields.map Atom.var), .var names.item]

theorem match_arguments (names : Names) (distinct : names.all.Nodup) (state : RunState) (item : Nat) :
    SpaceSemantics.matchValue.matchValues [] (arguments names) [encode state, number item] =
      some (callee names state item) := by
  simp only [Names.all, Names.fields, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp_all [arguments, Names.fields, encode, SpaceSemantics.matchValue.matchValues,
    SpaceSemantics.matchValue, matchAtom, Subst.lookup, callee]

structure Certified (program : Program) (head : String) where
  names : Names
  distinct : names.all.Nodup
  equation : Equation
  selected : program.equations.filter (fun equation => equation.head == head) = [equation]
  formals : equation.arguments = arguments names
  body : BodyCertificate program names equation.body
  notIO : ioHead head = false
  notNative : StdLib.known head = false
  ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]

def infer (program : Program) (head : String) : Option (Certified program head) := do
  if notIO : ioHead head = false then
    if notNative : StdLib.known head = false then
      if ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"] then
        match selected : program.equations.filter (fun equation => equation.head == head) with
        | [equation] =>
            match formals : equation.arguments with
            | [.expression [.var c, .var n, .var b, .var m], .var x] =>
                let names : Names := ⟨c, n, b, m, x⟩
                if distinct : names.all.Nodup then
                  let body ← inferBody program names equation.body
                  return ⟨names, distinct, equation, selected, formals, body, notIO, notNative, ordinary⟩
                else none
            | _ => none
        | _ => none
      else none
    else none
  else none

theorem Certified.clauses {program : Program} {head : String} (certificate : Certified program head)
    (state : RunState) (item : Nat) :
    Eval.clauses program head [encode state, number item] =
      [.evaluate (callee certificate.names state item) certificate.equation.body] := by
  rw [clauses_use_only_the_named_equations, certificate.selected]
  simp only [List.filterMap_cons, List.filterMap_nil, certificate.formals,
    match_arguments certificate.names certificate.distinct state item, Option.map_some]

theorem Certified.registered {program : Program} {head : String} (certificate : Certified program head) :
    program.equations.any (·.head == head) = true := by
  have member : certificate.equation ∈ program.equations.filter (fun equation => equation.head == head) := by
    rw [certificate.selected]
    simp
  exact List.any_eq_true.mpr ⟨certificate.equation, (List.mem_filter.mp member).1,
    (List.mem_filter.mp member).2⟩

theorem Certified.invokes {program : Program} {head : String} (certificate : Certified program head)
    (world : Effects.State) (state : RunState) (item : Nat) :
    FoldSource.Invokes program (.named head) world (encode state) (number item)
      (encode (SortedRun.step state item)) := by
  apply authored_variable_call_returns program _ (callee certificate.names state item) world world head
    ["fold-accumulator", "fold-item"] certificate.equation.body _
    certificate.notIO certificate.notNative certificate.registered _
    (certificate.body.returns certificate.distinct world state item) certificate.ordinary
  simpa [FoldSource.bindings, applySubst, Subst.lookup] using certificate.clauses state item

theorem Certified.fold {program : Program} {head : String} (certificate : Certified program head)
    (world : Effects.State) (labels : List Nat) (initial : RunState) :
    FoldSource.Evaluates program (.named head) world (labels.map number) (encode initial)
      (encode (labels.foldl SortedRun.step initial)) := by
  induction labels generalizing initial with
  | nil => exact .nil _
  | cons label rest ih => exact .cons (certificate.invokes world initial label) (ih _)

theorem Certified.fold_exact {program : Program} {head : String} (certificate : Certified program head)
    (world : Effects.State) (labels : List Nat) (initial : RunState) (answer : Atom) :
    FoldSource.Evaluates program (.named head) world (labels.map number) (encode initial) answer ↔
      answer = encode (labels.foldl SortedRun.step initial) := by
  constructor
  · intro evaluated
    exact FoldSource.evaluates_unique evaluated (certificate.fold world labels initial)
  · rintro rfl
    exact certificate.fold world labels initial

def wrappedCallback (head : String) : FoldSource.Callback :=
  .inline [] "acc" "x" (apply head [.var "acc", .var "x"])

theorem Certified.wrapped_invokes {program : Program} {head : String} (certificate : Certified program head)
    (world : Effects.State) (state : RunState) (item : Nat) :
    FoldSource.Invokes program (wrappedCallback head) world (encode state) (number item)
      (encode (SortedRun.step state item)) := by
  apply authored_variable_call_returns program _ (callee certificate.names state item) world world head
    ["acc", "x"] certificate.equation.body _ certificate.notIO certificate.notNative
    certificate.registered _ (certificate.body.returns certificate.distinct world state item) certificate.ordinary
  simpa [wrappedCallback, FoldSource.bindings, applySubst, Subst.lookup] using certificate.clauses state item

theorem Certified.wrapped_fold {program : Program} {head : String} (certificate : Certified program head)
    (world : Effects.State) (labels : List Nat) (initial : RunState) :
    FoldSource.Evaluates program (wrappedCallback head) world (labels.map number) (encode initial)
      (encode (labels.foldl SortedRun.step initial)) := by
  induction labels generalizing initial with
  | nil => exact .nil _
  | cons label rest ih => exact .cons (certificate.wrapped_invokes world initial label) (ih _)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeFoldSource
