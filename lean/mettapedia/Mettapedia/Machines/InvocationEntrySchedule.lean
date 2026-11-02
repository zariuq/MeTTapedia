import Mettapedia.Machines.SourceAccounting
import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Preserving the metered entrance of a ready invocation

The reference reconstructs an application and reads its fields at each of
three entrance stages. The target keeps the captured and supplied spans and
executes the same stages from a retained instruction schedule. Stage services
may change the world; their field reads are opaque and no value is evaluated
by transport. Every source/physical prefix and the exact residual agree.

This instantiates the maintained accounting machine, not another evaluator.
The native finite partial-call route currently retains its canonical visits
and materialization. A borrowed C implementation must preserve those visits
or establish a separate licensed observer. Pointer lifetimes, native stage
selection, and faulting/branching services have their own correspondence laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InvocationEntrySchedule

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeCallReturn.Arguments
open SourceAccounting
open ContextualCBPV.EpisodeAccounting (Purse)

inductive Stage where
  | applyReady | solve | callReady
  deriving DecidableEq, Repr

abbrev Services (World : Type) :=
  Stage → Atom → Nat → (Nat → Option Atom) → World → World

def materialize (input : Input Atom) : Atom :=
  .expression (input.head :: input.arguments)

def sourceAction {World : Type} (services : Services World) (stage : Stage)
    (head : Atom) (arguments : List Atom) : World → World :=
  services stage head arguments.length (fun index => arguments[index]?)

def targetAction {World : Type} (services : Services World) (stage : Stage)
    (input : Input Atom) : World → World :=
  services stage input.head input.arity input.read

theorem stage_fields_exact {World : Type} (services : Services World)
    (stage : Stage) (input : Input Atom) :
    targetAction services stage input = sourceAction services stage input.head input.arguments := by
  have reads : input.read = fun index => input.arguments[index]? := by
    funext index
    exact Input.read_refines input index
  simp [targetAction, sourceAction, Input.arguments_length, reads]

def sourceJobs {World : Type} (root : Nat) (services : Services World)
    (head : Atom) (arguments : List Atom) : List (Job World) :=
  [⟨⟨root, 0⟩, 1, sourceAction services .applyReady head arguments⟩,
   ⟨⟨root, 0⟩, 1, sourceAction services .solve head arguments⟩,
   ⟨⟨root, 0⟩, 1, sourceAction services .callReady head arguments⟩]

def source {World : Type} (root : Nat) (services : Services World)
    (application : Atom) (world : World) (purse : Purse) (trace : List Origin) :
    Option (Source World) :=
  match application with
  | .expression (head :: arguments) =>
      some ⟨sourceJobs root services head arguments, world, purse, trace⟩
  | _ => none

def instructions {World : Type} (services : Services World) (input : Input Atom) :
    List (Instruction World) :=
  [Stage.applyReady, .solve, .callReady].map fun stage =>
    ⟨0, 0, targetAction services stage input⟩

def target {World : Type} (root : Nat) (services : Services World) (input : Input Atom)
    (world : World) (purse : Purse) (trace : List Origin) : Compiled World :=
  ⟨root, instructions services input, 0, world, purse, trace⟩

theorem reconstruction_refines {World : Type} (root : Nat) (services : Services World)
    (input : Input Atom) (world : World) (purse : Purse) (trace : List Origin) :
    source root services (materialize input) world purse trace =
      some (decode (target root services input world purse trace)) := by
  simp [source, materialize, sourceJobs, target, instructions, decode,
    Instruction.charge, stage_fields_exact]

theorem all_physical_prefixes {World : Type} (maximum allowance root : Nat)
    (services : Services World) (input : Input Atom) (world : World)
    (purse : Purse) (trace : List Origin)
    (inRange : purse.spent + purse.remaining ≤ maximum) :
    let compiled := target root services input world purse trace
    ((SourceAccounting.sourceCore (World := World)).runSlice allowance (decode compiled)).1 =
        decode ((compiledCore maximum).runSlice allowance compiled).1 ∧
    ((SourceAccounting.sourceCore (World := World)).runSlice allowance (decode compiled)).2 =
        ((compiledCore maximum).runSlice allowance compiled).2 := by
  exact SourceAccounting.slice_refines maximum allowance
    (target root services input world purse trace) inRange

theorem source_prefix {World : Type} (maximum allowance root : Nat)
    (services : Services World) (input : Input Atom) (world : World)
    (purse : Purse) (trace : List Origin)
    (inRange : purse.spent + purse.remaining ≤ maximum) :
    (source root services (materialize input) world purse trace).map
      (fun reference => ((SourceAccounting.sourceCore (World := World)).runSlice allowance reference).1) =
      some (decode ((compiledCore maximum).runSlice allowance
        (target root services input world purse trace)).1) := by
  exact (congrArg (fun reference : Option (Source World) =>
    reference.map fun image =>
      ((SourceAccounting.sourceCore (World := World)).runSlice allowance image).1)
    (reconstruction_refines root services input world purse trace)).trans
      (congrArg some (all_physical_prefixes maximum allowance root services input world purse trace inRange).1)

theorem split_resume {World : Type} (maximum first later root : Nat)
    (services : Services World) (input : Input Atom) (world : World)
    (purse : Purse) (trace : List Origin) :
    (compiledCore maximum).runSlice (first + later)
        (target root services input world purse trace) =
      let earlier := (compiledCore maximum).runSlice first
        (target root services input world purse trace)
      let suffix := (compiledCore maximum).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) := by
  exact SourceAccounting.split_resume maximum first later
    (target root services input world purse trace)

theorem charge_is_not_erased {World : Type} (services : Services World) (input : Input Atom) :
    (instructions services input).map Instruction.charge = [1, 1, 1] := by
  simp [instructions, Instruction.charge]

/-- Once preparation has actually run, its retained suffix contains only
the entry word. Borrowing at that stage does not charge preparation again. -/
def entryOnly {World : Type} (root : Nat) (services : Services World) (input : Input Atom)
    (world : World) (purse : Purse) (trace : List Origin) : Compiled World :=
  ⟨root, [⟨0, 0, targetAction services .callReady input⟩], 0, world, purse, trace⟩

theorem prepared_suffix_exact {World : Type} (root : Nat) (services : Services World)
    (input : Input Atom) (world : World) (purse : Purse) (trace : List Origin) :
    decode {target root services input world purse trace with pc := 2} =
      decode (entryOnly root services input world purse trace) := by
  simp [target, instructions, decode, entryOnly]

theorem same_schedule_prefixes {World : Type} (maximum allowance : Nat)
    (left right : Compiled World) (same : decode left = decode right)
    (leftRange : left.purse.spent + left.purse.remaining ≤ maximum)
    (rightRange : right.purse.spent + right.purse.remaining ≤ maximum) :
    decode ((compiledCore maximum).runSlice allowance left).1 =
        decode ((compiledCore maximum).runSlice allowance right).1 ∧
    ((compiledCore maximum).runSlice allowance left).2 =
        ((compiledCore maximum).runSlice allowance right).2 := by
  have leftLaw := SourceAccounting.slice_refines maximum allowance left leftRange
  have rightLaw := SourceAccounting.slice_refines maximum allowance right rightRange
  have sources := congrArg (fun state : Source World =>
    (SourceAccounting.sourceCore (World := World)).runSlice allowance state) same
  exact ⟨leftLaw.1.symm.trans ((congrArg Prod.fst sources).trans rightLaw.1),
    leftLaw.2.symm.trans ((congrArg Prod.snd sources).trans rightLaw.2)⟩

theorem prepared_entry_prefixes {World : Type} (maximum allowance root : Nat)
    (services : Services World) (input : Input Atom) (world : World)
    (purse : Purse) (trace : List Origin)
    (inRange : purse.spent + purse.remaining ≤ maximum) :
    decode ((compiledCore maximum).runSlice allowance
        {target root services input world purse trace with pc := 2}).1 =
      decode ((compiledCore maximum).runSlice allowance
        (entryOnly root services input world purse trace)).1 := by
  exact (same_schedule_prefixes maximum allowance _ _
    (prepared_suffix_exact root services input world purse trace) inRange inRange).1

namespace Controls

def input : Input Atom :=
  ⟨.symbol "callee", #[.expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]],
    #[.grounded (.int 7), .grounded (.int 7)]⟩

/-- Preparation is deliberately neutral in this witness: even then, deleting
its source visits changes when the one visible callee entry is reached. -/
def services : Services Nat
  | .applyReady, _, _, _, world => world
  | .solve, _, _, _, world => world
  | .callReady, _, _, _, world => world + 1

def staged (credit : Nat) : Compiled Nat := target 17 services input 0 ⟨credit, 0⟩ []

def elided (credit : Nat) : Compiled Nat :=
  ⟨17, [⟨0, 0, targetAction services .callReady input⟩], 0, 0, ⟨credit, 0⟩, []⟩

def aggregated (credit : Nat) : Compiled Nat :=
  ⟨17, [⟨1, 3, targetAction services .callReady input⟩], 0, 0, ⟨credit, 0⟩, []⟩

theorem equal_completed_values :
    ((compiledCore 64).runSlice 3 (staged 3)).1.world = 1 ∧
    ((compiledCore 64).runSlice 3 (elided 3)).1.world = 1 := by decide

theorem elision_changes_bounded_entry :
    ((compiledCore 64).runSlice 3 (staged 1)).1.world = 0 ∧
    ((compiledCore 64).runSlice 3 (elided 1)).1.world = 1 := by decide

theorem aggregation_changes_credit_prefix :
    ((compiledCore 64).runSlice 3 (staged 1)).1.purse = ⟨0, 1⟩ ∧
    ((compiledCore 64).runSlice 3 (aggregated 1)).1.purse = ⟨1, 0⟩ := by decide

theorem spent_credit_stays_with_residual :
    let earlier :=  ((compiledCore 64).runSlice 2 (staged 2)).1
    ((compiledCore 64).runSlice 1 {earlier with purse := ⟨1, earlier.purse.spent⟩}).1.world = 1 ∧
    earlier.pc = 2 ∧ earlier.world = 0 := by decide

theorem duplicate_operands_are_retained :
    input.read 1 = input.read 2 ∧ input.arity = 3 := by decide

theorem returned_code_is_an_argument :
    input.read 0 = some (.expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]) := by
  decide

theorem replaying_preparation_changes_entry :
    ((compiledCore 64).runSlice 1
      {staged 1 with pc := 2, purse := ⟨1, 2⟩}).1.world = 1 ∧
    ((compiledCore 64).runSlice 1
      {staged 1 with purse := ⟨1, 2⟩}).1.world = 0 := by decide

end Controls
end Mettapedia.Machines.InvocationEntrySchedule
