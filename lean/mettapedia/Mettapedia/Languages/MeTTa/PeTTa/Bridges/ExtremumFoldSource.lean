import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBodyNormalization
import Mettapedia.Languages.MeTTa.PeTTa.FoldSource
import Mathlib.Data.List.Perm.Basic

/-!
# Source-inferred minimum and maximum folds over integers

The same typed schema recognizer used for mode accepts pure min/max callbacks.
The source derivation is uniform over all integer inputs, including negative
values. The initial accumulator remains part of the observation, especially
on empty input. Reordering is licensed for the final extremum, not its prefix
trace or evaluator steps. No machine-width conversion is performed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ExtremumFoldSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Machines.TypedScalar
open SpaceSemantics Eval MeTTaIL.WireKit

inductive Direction | minimum | maximum
  deriving DecidableEq

inductive Slot | accumulator | item
  deriving DecidableEq

def combine : Direction → Int → Int → Int
  | .minimum => min
  | .maximum => max

def aggregate (direction : Direction) (items : List Int) (initial : Int) : Int := items.foldl (combine direction) initial

def field (slot : Slot) : ScalarBody.Body Slot := .scalar ⟨.data, .read slot⟩

def ir (direction : Direction) : ScalarBody.Body Slot :=
  .branch (.binary .lt (.read .accumulator) (.read .item))
    (field (if direction = .minimum then .accumulator else .item))
    (field (if direction = .minimum then .item else .accumulator))

def locals (accumulator item : Int) : Slot → Data
  | .accumulator => .integer accumulator
  | .item => .integer item

def environment (accumulatorName itemName : String) : ScalarSource.Environment Slot := fun name =>
  if name = accumulatorName then some .accumulator else if name = itemName then some .item else none

theorem ir_uniform (direction : Direction) (program : Program) (accumulator item : Int) :
    (ir direction).eval program (locals accumulator item) = some (integer (combine direction accumulator item)) := by
  cases direction <;> by_cases smaller : accumulator < item
  all_goals simp [ir, field, ScalarBody.Body.eval, ScalarBody.evalField, Expr.eval, Binary.eval,
    locals, ScalarSource.encode, integer, combine, smaller, le_of_not_gt, le_of_lt]

structure Certified (direction : Direction) (program : Program) (caller : Subst)
    (accumulatorName itemName : String) (source : Atom) where
  distinct : accumulatorName ≠ itemName
  freshAccumulator : caller.lookup accumulatorName = none
  freshItem : caller.lookup itemName = none
  schema : ScalarBody.Recognized program (environment accumulatorName itemName) source (ir direction)

def infer (direction : Direction) (program : Program) (caller : Subst)
    (accumulatorName itemName : String) (source : Atom) :
    Option (Certified direction program caller accumulatorName itemName source) := do
  if distinct : accumulatorName ≠ itemName then
    if freshAccumulator : caller.lookup accumulatorName = none then
      if freshItem : caller.lookup itemName = none then
        let schema ← ScalarBody.recognize program (environment accumulatorName itemName) source (ir direction)
        return ⟨distinct, freshAccumulator, freshItem, schema⟩
      else none
    else none
  else none

def callback (caller : Subst) (accumulatorName itemName : String) (source : Atom) : FoldSource.Callback :=
  .inline caller accumulatorName itemName source

theorem captured (caller : Subst) (accumulatorName itemName : String) (source : Atom)
    (distinct : accumulatorName ≠ itemName) (accumulator item : Int) :
    ScalarSource.Captured (environment accumulatorName itemName)
      (FoldSource.bindings (callback caller accumulatorName itemName source) (integer accumulator) (integer item))
      (locals accumulator item) := by
  intro name slot found
  unfold environment at found
  split_ifs at found <;> cases found
  all_goals subst name
  all_goals simp [FoldSource.bindings, callback, locals, ScalarSource.encode, integer, Subst.lookup, distinct]

theorem Certified.invokes {direction : Direction} {program : Program} {caller : Subst}
    {accumulatorName itemName : String} {source : Atom}
    (certificate : Certified direction program caller accumulatorName itemName source)
    (world : Effects.State) (accumulator item : Int) :
    FoldSource.Invokes program (callback caller accumulatorName itemName source) world
      (integer accumulator) (integer item) (integer (combine direction accumulator item)) := by
  apply certificate.schema.compiled.returns _ world (locals accumulator item)
    (captured caller accumulatorName itemName source certificate.distinct accumulator item)
  rw [ScalarBody.canonical_equal_eval _ _ certificate.schema.normalized, ir_uniform]

theorem Certified.fold {direction : Direction} {program : Program} {caller : Subst}
    {accumulatorName itemName : String} {source : Atom}
    (certificate : Certified direction program caller accumulatorName itemName source)
    (world : Effects.State) (items : List Int) (initial : Int) :
    FoldSource.Evaluates program (callback caller accumulatorName itemName source) world
      (items.map integer) (integer initial) (integer (aggregate direction items initial)) := by
  induction items generalizing initial with
  | nil => exact .nil _
  | cons item rest ih => exact .cons (certificate.invokes world initial item) (ih _)

theorem Certified.fold_exact {direction : Direction} {program : Program} {caller : Subst}
    {accumulatorName itemName : String} {source : Atom}
    (certificate : Certified direction program caller accumulatorName itemName source)
    (world : Effects.State) (items : List Int) (initial : Int) (answer : Atom) :
    FoldSource.Evaluates program (callback caller accumulatorName itemName source) world
      (items.map integer) (integer initial) answer ↔ answer = integer (aggregate direction items initial) := by
  constructor
  · intro evaluated
    exact FoldSource.evaluates_unique evaluated (certificate.fold world items initial)
  · rintro rfl
    exact certificate.fold world items initial

def prefixes (direction : Direction) : List Int → Int → List Int
  | [], _ => []
  | item :: rest, initial =>
      let next := combine direction initial item
      next :: prefixes direction rest next

theorem Certified.trace {direction : Direction} {program : Program} {caller : Subst}
    {accumulatorName itemName : String} {source : Atom}
    (certificate : Certified direction program caller accumulatorName itemName source)
    (world : Effects.State) (items : List Int) (initial : Int) :
    FoldSource.Trace program (callback caller accumulatorName itemName source) world
      (items.map integer) (integer initial) ((prefixes direction items initial).map integer) := by
  induction items generalizing initial with
  | nil => exact .nil _
  | cons item rest ih => exact .cons (certificate.invokes world initial item) (ih _)

theorem aggregate_append (direction : Direction) (first second : List Int) (initial : Int) :
    aggregate direction (first ++ second) initial = aggregate direction second (aggregate direction first initial) :=
  List.foldl_append

theorem combine_right_comm (direction : Direction) (accumulator first second : Int) :
    combine direction (combine direction accumulator first) second =
      combine direction (combine direction accumulator second) first := by
  cases direction <;> simp [combine, min_right_comm, max_right_comm]

theorem aggregate_perm (direction : Direction) {first second : List Int} (same : first.Perm second) (initial : Int) :
    aggregate direction first initial = aggregate direction second initial :=
  same.foldl_eq' (fun x _ y _ z => combine_right_comm direction z x y) initial

namespace Controls

def program : Program := {equations := [], declarations := []}
def minimumBody : Atom := apply "if" [apply "<" [.var "a", .var "x"], .var "a", .var "x"]
def maximumBody : Atom := apply "if" [apply "<" [.var "a", .var "x"], .var "x", .var "a"]

theorem min_is_inferred : (infer .minimum program [] "a" "x" minimumBody).isSome = true := by decide +kernel
theorem max_is_inferred : (infer .maximum program [] "a" "x" maximumBody).isSome = true := by decide +kernel

def minimumCertificate := (infer .minimum program [] "a" "x" minimumBody).get min_is_inferred
def maximumCertificate := (infer .maximum program [] "a" "x" maximumBody).get max_is_inferred

theorem negative_values_are_integers_not_refusals (world : Effects.State) :
    FoldSource.Evaluates program (callback [] "a" "x" minimumBody) world
      ([-3, 7, -8].map integer) (integer 0) (integer (-8)) := minimumCertificate.fold world [-3, 7, -8] 0

theorem initial_value_is_not_erased (world : Effects.State) :
    FoldSource.Evaluates program (callback [] "a" "x" maximumBody) world
      ([1, 2].map integer) (integer 9) (integer 9) := maximumCertificate.fold world [1, 2] 9

theorem empty_input_returns_initial (world : Effects.State) :
    FoldSource.Evaluates program (callback [] "a" "x" minimumBody) world [] (integer 12) (integer 12) := .nil _

theorem same_final_extremum_different_prefix :
    aggregate .minimum [1, 2] 3 = aggregate .minimum [2, 1] 3 ∧
      prefixes .minimum [1, 2] 3 ≠ prefixes .minimum [2, 1] 3 := by decide

theorem arithmetic_side_effect_is_not_a_minimum_schema :
    (infer .minimum program [] "a" "x" (apply "println!" [.var "x"])).isNone = true := by decide +kernel

theorem maximum_is_not_misclassified_as_minimum :
    (infer .minimum program [] "a" "x" maximumBody).isNone = true := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ExtremumFoldSource
