import Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping
import Mettapedia.Logic.ConstraintTypes.PatternControls

/-!
# Explicit wildcard policy

This is a normalized source-policy specification. Literal input `Atom` holds
its argument; `_` and `%Undefined%` evaluate it. In checking positions all three
omit a requirement. A result contains no evaluation mode: templates are ordinary
quoted body computations. This specifies a proposed policy, not a change to an
existing evaluator or an assertion about its current quotation behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.CheckingPolicy

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Wildcard where
  | atom | underscore | undefined
  deriving DecidableEq

def source : Wildcard → Atom
  | .atom => .symbol "Atom"
  | .underscore => .symbol "_"
  | .undefined => .symbol "%Undefined%"

def wildcardName : String → Option Wildcard
  | "Atom" => some .atom
  | "_" => some .underscore
  | "%Undefined%" => some .undefined
  | _ => none

/-- Admissible proper names exclude checking syntax. The proper type algebra
can still contain genuine shared nominal types; it is not a list of observed
primitive tags or an enumeration of all parameter assignments. -/
abbrev ProperName := {name : String // wildcardName name = none}

abbrev ProperWitness (C : Type) (arity : C → Nat) :=
  SymbolicTypes.Closed ProperName C arity

theorem wildcard_spelling_is_not_a_proper_name (name : ProperName) (spelling : Wildcard) :
    Atom.symbol name.val ≠ source spelling := by
  intro same
  have impossible := name.property
  cases spelling <;> simp_all [source,wildcardName]

variable {Kind : Type} {sig : CheckingPatterns.Signature Kind} {P Q C : Type}
  {typeArity : C → Nat} {valueKind : Kind}

def valueCheck (_ : Wildcard) : CheckingPatterns.Pattern sig P Q C typeArity valueKind := .any

def input (spelling : Wildcard) : PatternContracts.Input sig P Q C typeArity valueKind where
  evaluation := if spelling = .atom then .hold else .evaluate
  check := valueCheck spelling

theorem input_mode_agrees_with_source_protocol (spelling : Wildcard) :
    argumentMode (source spelling) =
      match (input (sig := sig) (P := P) (Q := Q) (C := C) (typeArity := typeArity)
        (valueKind := valueKind) spelling).evaluation with
      | .hold => .hold
      | .evaluate => .evaluate := by
  cases spelling <;> rfl

theorem every_literal_wildcard_omits_the_value_check
    {Carrier : Kind → Type} {Context : Type}
    (model : CheckingPatterns.Model sig Carrier Context Q C typeArity)
    (parameters : P → SymbolicTypes.Closed Q C typeArity) (context : Context)
    (value : Carrier valueKind) (spelling : Wildcard) :
    CheckingPatterns.Matches model parameters (valueCheck spelling) context value := .any _ _

theorem type_substitution_never_changes_literal_argument_mode {X : Type}
    (substitution : P → SymbolicTypes.Expr X Q C typeArity) (spelling : Wildcard) :
    (PatternContracts.Input.substitute substitution
      (input (sig := sig) (typeArity := typeArity) (valueKind := valueKind) spelling)).evaluation =
      (input (sig := sig) (P := P) (Q := Q) (C := C) (typeArity := typeArity)
        (valueKind := valueKind) spelling).evaluation := rfl

/-- The normalized source protocol uses the certified pattern boundary, rather
than leaving membership and mode selection unrelated parameters. All call
routes still use `Runtime.run`; a source declaration parser is not supplied. -/
def checkedRuntime {World Fault Effect : Type} [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (model : CheckingPatterns.Model sig (fun _ => Atom) World Q C typeArity)
    (compiler : CheckingPatterns.Compiler model)
    (declarations : World → (f : FunctionKey) →
      List (PatternContracts.Declaration sig P Q C typeArity valueKind f.arity))
    (bodies : World → (f : FunctionKey) →
      Boundary.Body World (Fin f.arity → Atom) Atom Fault Effect)
    (evaluate : World → Atom → Trace (Atom × World) Fault Effect)
    (wrongArity : FunctionKey → Nat → Fault) : Runtime World Fault Effect where
  modes world f index := if within : index < f.arity then
    match PatternContracts.argumentPlan ((declarations world f).map fun declaration => declaration.input ⟨index,within⟩) with
    | .hold => .hold
    | .evaluate => .evaluate
    else .evaluate
  evaluate := evaluate
  contract _ _ := none
  worker entered f world args := if saturated : args.length = f.arity then
    PatternContracts.invoke model compiler (declarations entered f) (bodies entered f) world
      (fun i => args[i.val]'(by rw [saturated]; exact i.isLt))
    else .fault (wrongArity f args.length)
  wrongArity := wrongArity

theorem checked_worker_uses_the_pattern_boundary {World Fault Effect : Type}
    [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (model : CheckingPatterns.Model sig (fun _ => Atom) World Q C typeArity)
    (compiler : CheckingPatterns.Compiler model)
    (declarations : World → (f : FunctionKey) →
      List (PatternContracts.Declaration sig P Q C typeArity valueKind f.arity))
    (bodies : World → (f : FunctionKey) →
      Boundary.Body World (Fin f.arity → Atom) Atom Fault Effect)
    (evaluate : World → Atom → Trace (Atom × World) Fault Effect)
    (wrongArity : FunctionKey → Nat → Fault) (entered world : World)
    (f : FunctionKey) (arguments : Fin f.arity → Atom) :
    (checkedRuntime model compiler declarations bodies evaluate wrongArity).worker entered f world (List.ofFn arguments) =
      PatternContracts.invoke model compiler (declarations entered f) (bodies entered f) world arguments := by
  simp [checkedRuntime]

open PatternControls in
theorem nested_atom_and_underscore_accept_mixed_elements :
    check (listCheck (valueCheck (sig := signature) (P := Empty) .atom)) mixed = true ∧
      check (listCheck (valueCheck (sig := signature) (P := Empty) .underscore)) mixed = true :=
  ⟨wildcard_list_accepts_mixed_values, wildcard_list_accepts_mixed_values⟩

open PatternControls in
theorem nested_undefined_accepts_mixed_elements :
    check (listCheck (valueCheck (sig := signature) (P := Empty) .undefined)) mixed = true :=
  wildcard_list_accepts_mixed_values

open PatternControls Controls in
/-- Nested wildcard support does not extend the type-witness algebra. -/
theorem shared_type_variables_still_reject_incompatible_primitives :
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := PatternControls.Kind.value)
      PatternControls.model PatternControls.compiler false
      (fun i => if i.val = 0 then number 1 else text "a") [shared]) = false :=
  PatternControls.shared_parameter_rejects_number_and_string

theorem let_return_preserves_body_observations {V F E : Type} (body : Trace V F E) :
    body.bind (fun value => .answer value .done) = body := Trace.bind_return body

end Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.CheckingPolicy
