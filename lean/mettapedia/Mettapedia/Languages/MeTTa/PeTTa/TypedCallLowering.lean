import Mettapedia.Machines.OrderedProtocol
import Mettapedia.Languages.MeTTa.PeTTa.CallGuardOptimization

/-!
# Lowering complete PeTTa typed-call protocols

The source model inspects each literal domain and performs its operational
argument protocol before the body and selected result contract. The compiler
independently emits the existing native classes of actions: raw operand,
translation, guard, body, result guard, and result publication. Arbitrary
primitive continuations retain effects, failures, faults, suspension and the
saved cut delimiter. Ordered signature alternatives are not deduplicated here.

Whole-scheme hygiene is supplied by TypeSchemeActivation. This proves protocol
lowering, not implementation of get-type, C allocation, or machine/OEM copying.
Partial and dependent-profile calls are outside this full-call theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.TypedCallLowering

open Mettapedia.Machines.OrderedProtocol
open CallGuardOptimization
open OSLFCore (Atom)

inductive Action where
  | activate (signature : Signature)
  | raw (position : Nat)
  | translate (position : Nat)
  | guardArgument (position : Nat)
  | body (held : Bool)
  | guardResult
  | publish
  deriving DecidableEq, Repr

def compileArgument (position : Nat) (formal : Atom) : List Action :=
  match demand formal with
  | .raw => [.raw position]
  | .translate => [.translate position]
  | .checked => [.translate position, .guardArgument position]

def compileArguments : Nat → List Atom → List Action
  | _, [] => []
  | position, formal :: rest =>
      compileArgument position formal ++ compileArguments (position + 1) rest

def compileCall (held : Bool) (signature : Signature) : List Action :=
  .activate signature ::
    (compileArguments 1 signature.domains ++
      [.body held] ++
      (if demand signature.codomain == .checked then [.guardResult] else []) ++
      [.publish])

variable {State World Fault Pause Result : Type}

/-- Primitive authority is shared; the source protocol and emitted program
have separate control constructions. A guard primitive owns exact/fallback
commitment, rather than allowing the compiler to treat it as a Boolean. -/
abbrev Services (State World Fault Pause Result : Type) :=
  Action → Kernel State World Fault Pause Result

def sourceArgument (services : Services State World Fault Pause Result) (position : Nat) (formal : Atom)
    (next : Kernel State World Fault Pause Result) :
    Kernel State World Fault Pause Result :=
  match demand formal with
  | .raw => sequence (services (.raw position)) next
  | .translate => sequence (services (.translate position)) next
  | .checked => sequence (services (.translate position))
      (sequence (services (.guardArgument position)) next)

def sourceArguments (services : Services State World Fault Pause Result) :
    Nat → List Atom → Kernel State World Fault Pause Result →
      Kernel State World Fault Pause Result
  | _, [], next => next
  | position, formal :: rest, next =>
      sourceArgument services position formal
        (sourceArguments services (position + 1) rest next)

def sourceCall (services : Services State World Fault Pause Result) (held : Bool) (signature : Signature) :
    Kernel State World Fault Pause Result :=
  sequence (services (.activate signature))
    (sourceArguments services 1 signature.domains
      (sequence (services (.body held))
        (if demand signature.codomain == .checked then
          sequence (services .guardResult) (services .publish)
        else services .publish)))

theorem compileArgument_exact (services : Services State World Fault Pause Result) (position : Nat) (formal : Atom)
    (next : Kernel State World Fault Pause Result) :
    sequence (execute services (compileArgument position formal)) next =
      sourceArgument services position formal next := by
  cases mode : demand formal <;>
    simp [compileArgument, sourceArgument, mode, execute, sequence_assoc, sequence_done]

theorem compileArguments_exact (services : Services State World Fault Pause Result) (position : Nat) (formals : List Atom)
    (next : Kernel State World Fault Pause Result) :
    sequence (execute services (compileArguments position formals)) next =
      sourceArguments services position formals next := by
  induction formals generalizing position with
  | nil => rfl
  | cons formal rest ih =>
      simp only [compileArguments, sourceArguments, execute_append, sequence_assoc]
      rw [ih, compileArgument_exact]

/-- Equality holds for every incoming state and every continuation consumer,
including terminal-fault and suspension consumers. It covers every arity. -/
theorem compileCall_exact (services : Services State World Fault Pause Result) (held : Bool) (signature : Signature) :
    execute services (compileCall held signature) = sourceCall services held signature := by
  simp only [compileCall, execute, execute_append, sourceCall, sequence_assoc]
  rw [compileArguments_exact]
  cases checking : (demand signature.codomain == .checked) <;>
    simp [execute, sequence_done, done_sequence]

def compileFamily (family : List Signature) : List (List Action) :=
  family.map (compileCall (holdBody family))

def sourceFamily (services : Services State World Fault Pause Result) (family : List Signature) :
    Kernel State World Fault Pause Result :=
  alternatives (family.map (sourceCall services (holdBody family)))

theorem compileFamily_exact (services : Services State World Fault Pause Result) (family : List Signature) :
    alternatives ((compileFamily family).map (execute services)) =
      sourceFamily services family := by
  unfold compileFamily sourceFamily
  rw [List.map_map]
  apply alternatives_map_congr
  intro signature _
  exact compileCall_exact services (holdBody family) signature

theorem every_signature_keeps_an_alternative (family : List Signature) :
    (compileFamily family).length = family.length := by simp [compileFamily]

theorem fresh_activation_keeps_argument_actions (names : String → String)
    (position : Nat) (formals : List Atom) :
    compileArguments position (formals.map (TypeSchemeActivation.rename names)) =
      compileArguments position formals := by
  induction formals generalizing position with
  | nil => rfl
  | cons formal rest ih =>
      simp only [List.map_cons, compileArguments, compileArgument, demand_rename, ih]

theorem fresh_activation_keeps_call_actions (names : String → String)
    (held : Bool) (signature : Signature) :
    (compileCall held (renameSignature names signature)).tail =
      (compileCall held signature).tail := by
  simp [compileCall, renameSignature, fresh_activation_keeps_argument_actions, demand_rename]

namespace Controls

theorem literal_atom_retains_its_source :
    compileArgument 1 (.symbol "Atom") = [.raw 1] := by
  simp [compileArgument, demand]

theorem formal_variable_remains_guarded :
    compileArgument 65 (.var "t") = [.translate 65, .guardArgument 65] := by
  simp [compileArgument, demand]

theorem binding_before_classification_changes_the_protocol :
    compileArgument 1 (.var "t") ≠ compileArgument 1 (.symbol "Atom") := by
  simp [compileArgument, demand]

theorem held_body_does_not_erase_selected_result_guard :
    compileCall true ⟨[], .symbol "Number"⟩ =
      [.activate ⟨[], .symbol "Number"⟩, .body true, .guardResult, .publish] := by
  simp [compileCall, compileArguments, demand]

theorem duplicate_signatures_keep_two_trials :
    (compileFamily [⟨[], .symbol "Atom"⟩, ⟨[], .symbol "Atom"⟩]).length = 2 := rfl

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.TypedCallLowering
