import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine

/-!
# Retaining compiled data-head decisions

A literal head which is neither a control form nor callable can be emitted
as constructor data. Quotation handles no operands; native cons handles
nonempty operands in order without introducing bindings. Later registration
does not reinterpret the constructed result as a call. Complete compiler
adequacy remains distinct from this emission connection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorDataHeads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Unifying
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def namedCallable (registry : Program) (head : String) : Bool :=
  Eval.ioHead head || StdLib.known head || registry.equations.any (·.head == head)

def shouldFreeze (registry : Program) (head : Atom) (arguments : List Atom) : Bool :=
  match head with
  | .symbol name => !(sourceControlForm (.expression (.symbol name :: arguments)) || namedCallable registry name)
  | _ => false

def frozen (head : Atom) : Atom := .expression [.symbol "quote",.expression [head]]

def construct (head : Atom) : List Atom → Atom
  | [] => frozen head
  | first :: rest => ConstructorSpine.build (head :: first :: rest)

def emit (registry : Program) (head : Atom) (arguments : List Atom) : Atom :=
  if shouldFreeze registry head arguments then construct head arguments else .expression (head :: arguments)

theorem shouldFreeze_iff (registry : Program) (head : Atom) (arguments : List Atom) :
    shouldFreeze registry head arguments = true ↔
      ∃ name, head = .symbol name ∧
        sourceControlForm (.expression (.symbol name :: arguments)) = false ∧ namedCallable registry name = false := by
  cases head <;> simp [shouldFreeze]

inductive Emission (registry : Program) (head : Atom) (arguments : List Atom) : Atom → Prop where
  | frozen {name} : head = .symbol name →
      sourceControlForm (.expression (.symbol name :: arguments)) = false → namedCallable registry name = false →
      Emission registry head arguments (construct (.symbol name) arguments)
  | retained : shouldFreeze registry head arguments = false →
      Emission registry head arguments (.expression (head :: arguments))

theorem emit_source (registry : Program) (head : Atom) (arguments : List Atom) :
    Emission registry head arguments (emit registry head arguments) := by
  cases selected : shouldFreeze registry head arguments
  · simpa only [emit,selected,Bool.false_eq_true,↓reduceIte] using Emission.retained selected
  · obtain ⟨name,rfl,notControl,notCallable⟩ := (shouldFreeze_iff registry head arguments).mp selected
    simpa only [emit,selected,↓reduceIte] using
      Emission.frozen (registry := registry) rfl notControl notCallable

theorem emission_iff (registry : Program) (head : Atom) (arguments : List Atom) (result : Atom) :
    Emission registry head arguments result ↔ emit registry head arguments = result := by
  constructor
  · intro source
    cases source with
    | frozen headEq notControl notCallable =>
        subst head
        simp [emit,shouldFreeze,notControl,notCallable]
    | retained selected => simp [emit,selected]
  · rintro rfl
    exact emit_source registry head arguments

theorem construct_nonempty (head first : Atom) (rest : List Atom) :
    construct head (first :: rest) = ConstructorSpine.build (head :: first :: rest) := rfl

theorem emit_of_retained (registry : Program) (head : Atom) (arguments : List Atom)
    (retained : shouldFreeze registry head arguments = false) :
    emit registry head arguments = .expression (head :: arguments) := by simp [emit,retained]

theorem frozen_step (registry : Program) (base : Configuration) (bindings : Subst) (head : String) :
    step registry {base with control := .evaluate bindings (frozen (.symbol head))} =
      some {base with control := .returned [⟨.expression [.symbol head],bindings⟩]} := rfl

/-- The reached caller, world, input/output and identity supply are exact.
No agreement with the future registry is required to retain this data. -/
theorem run_frozen (registry : Program) (fuel : Nat) (base : Configuration)
    (bindings : Subst) (head : String) :
    run registry (fuel + 1) {base with control := .evaluate bindings (frozen (.symbol head))} =
      run registry fuel {base with control := .returned [⟨.expression [.symbol head],bindings⟩]} :=
  run_succ_of_step registry fuel _ _ (frozen_step registry base bindings head)

/-- The ordinary unknown-head route reaches the same return boundary in
eight source steps. Quotation's one step therefore changes finite cutoffs;
neither route performs a store effect on this segment. -/
theorem run_raw_nullary (registry : Program) (fuel : Nat) (base : Configuration)
    (bindings : Subst) (head : String)
    (notControl : sourceControlForm (.expression [.symbol head]) = false)
    (notCallable : namedCallable (codeRegistry registry base.privateCode) head = false) :
    run registry (fuel + 8) {base with control := .evaluate bindings (.expression [.symbol head])} =
      run registry fuel {base with control := .returned [⟨.expression [.symbol head],bindings⟩]} := by
  let result : Answer := ⟨.expression [.symbol head],bindings⟩
  let one : Configuration := {base with control := .arguments bindings .data [.symbol head] [] 0}
  let two : Configuration := {base with
    control := .evaluate bindings (.symbol head)
    frames := .argument .data [] [] 0 :: base.frames}
  let three : Configuration := {two with control := .returned [⟨.symbol head,bindings⟩]}
  let four : Configuration := {base with control := .sequence [.arguments bindings .data [] [.symbol head] 1] []}
  let five : Configuration := {base with
    control := .arguments bindings .data [] [.symbol head] 1
    frames := .sequence [] [] :: base.frames}
  let six : Configuration := {five with control := .returned [result]}
  let seven : Configuration := {base with control := .sequence [] [result]}
  have entry : step registry {base with control := .evaluate bindings (.expression [.symbol head])} = some one :=
    transition_step (.data_enter rfl notControl notCallable)
  calc
    _ = run registry (fuel + 7) one := run_succ_of_step registry (fuel + 7) _ _ entry
    _ = run registry (fuel + 6) two := run_succ_of_step registry (fuel + 6) _ _ rfl
    _ = run registry (fuel + 5) three := run_succ_of_step registry (fuel + 5) _ _ rfl
    _ = run registry (fuel + 4) four := run_succ_of_step registry (fuel + 4) _ _ rfl
    _ = run registry (fuel + 3) five := run_succ_of_step registry (fuel + 3) _ _ rfl
    _ = run registry (fuel + 2) six := run_succ_of_step registry (fuel + 2) _ _ rfl
    _ = run registry (fuel + 1) seven := run_succ_of_step registry (fuel + 1) _ _ rfl
    _ = _ := run_succ_of_step registry fuel _ _ rfl

theorem empty_remains_a_control_form :
    shouldFreeze {equations := [],declarations := []} (.symbol "empty") [] = false := by decide

theorem unknown_nullary_head_is_frozen :
    emit {equations := [],declarations := []} (.symbol "lambda_1") [] =
      .expression [.symbol "quote",.expression [.symbol "lambda_1"]] := by decide

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorDataHeads
