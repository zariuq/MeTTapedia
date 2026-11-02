import Mettapedia.Machines.ExecutionControl
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# PeTTa source shapes and basic occurrence words

The native classifier combines source shape, an established value origin,
direct-call syntax and the three sources of named callability. The independent
source classifier uses constructor patterns and membership in their union.
Both lower through the maintained value/construction/invocation interface.

This covers basic occurrence authority, before a dialect-control word takes
precedence. Certification of lists, closures and held values, recursive child
planning, control decoding and concrete C storage retain their own obligations.
The value-origin input is that certification, not an inspection of its payload.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceRoleElaboration

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ExecutionControl.Occurrence (Authority)

structure Facts where
  intrinsic : Finset String
  relations : Finset String
  extensions : Finset String
  deriving DecidableEq

def nativeKnown (facts : Facts) (name : String) : Bool :=
  decide (name ∈ facts.intrinsic) || decide (name ∈ facts.relations) ||
    decide (name ∈ facts.extensions)

def sourceKnown (facts : Facts) (name : String) : Bool :=
  decide (name ∈ facts.intrinsic ∪ facts.relations ∪ facts.extensions)

theorem known_refines (facts : Facts) (name : String) :
    nativeKnown facts name = sourceKnown facts name := by
  simp [nativeKnown, sourceKnown, Finset.mem_union, Bool.decide_or, Bool.or_assoc]

def classify (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) : Authority :=
  if valueOrigin then .value else
  match term with
  | .expression [] => .constructor
  | .expression (head :: arguments) =>
      match head with
      | .symbol name =>
          if !arguments.isEmpty && (name == ":" || name == "->") then .constructor
          else if directCall || nativeKnown facts name then .staticCall else .constructor
      | _ => .dynamicCall
  | _ => .value

/-- The source gives nonempty type-constructor applications precedence over
named callability. A bare symbol remains a value. -/
def sourceRole (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) : Authority :=
  if valueOrigin then .value else
  match term with
  | .expression (.symbol name :: _first :: _later) =>
      if name = ":" ∨ name = "->" then .constructor
      else if directCall = true ∨ name ∈ facts.intrinsic ∪ facts.relations ∪ facts.extensions
        then .staticCall else .constructor
  | .expression [.symbol name] =>
      if directCall = true ∨ name ∈ facts.intrinsic ∪ facts.relations ∪ facts.extensions
        then .staticCall else .constructor
  | .expression [] => .constructor
  | .expression (_ :: _) => .dynamicCall
  | _ => .value

theorem classification_refines (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) :
    classify facts valueOrigin directCall term = sourceRole facts valueOrigin directCall term := by
  cases valueOrigin <;> cases term with
  | symbol name => rfl
  | var name => rfl
  | grounded value => rfl
  | expression fields =>
      cases fields with
      | nil => rfl
      | cons head arguments =>
          cases head <;> cases arguments <;>
            simp [classify, sourceRole, known_refines, sourceKnown,
              Bool.or_eq_true]

theorem value_origin_ignores_callability (first second : Facts)
    (firstDirect secondDirect : Bool) (term : Atom) :
    classify first true firstDirect term = classify second true secondDirect term := by
  rfl

theorem constructor_priority (facts : Facts) (direct : Bool)
    (name : String) (first : Atom) (later : List Atom)
    (constructor : name = ":" ∨ name = "->") :
    classify facts false direct (.expression (.symbol name :: first :: later)) = .constructor := by
  rw [classification_refines]
  simp [sourceRole, constructor]

theorem unknown_name_is_data (facts : Facts) (name : String) (arguments : List Atom)
    (unknown : name ∉ facts.intrinsic ∪ facts.relations ∪ facts.extensions) :
    classify facts false false (.expression (.symbol name :: arguments)) = .constructor := by
  have absent := unknown
  simp only [Finset.mem_union, not_or] at absent
  cases arguments <;> simp [classify, nativeKnown, absent]

theorem known_ordinary_name_is_call (facts : Facts) (name : String) (arguments : List Atom)
    (known : name ∈ facts.intrinsic ∪ facts.relations ∪ facts.extensions)
    (ordinary : name ≠ ":" ∧ name ≠ "->") :
    classify facts false false (.expression (.symbol name :: arguments)) = .staticCall := by
  have present := known
  simp only [Finset.mem_union] at present
  cases arguments <;> simp [classify, nativeKnown, ordinary]
  all_goals tauto

theorem source_symbol_is_value (facts : Facts) (name : String) (direct : Bool) :
    classify facts false direct (.symbol name) = .value := by rfl

/-- This query records the aggregate callability fact needed for an ordinary
symbol-headed role, including an absent name. It is not the complete compiler
dependency certificate, which also covers demand, control and value evidence. -/
def roleQuery (valueOrigin directCall : Bool) (term : Atom) :
    ReadOnlyQuery.Program String Bool Authority :=
  if valueOrigin then .pure .value else
  match term with
  | .expression (.symbol name :: arguments) =>
      if !arguments.isEmpty && (name == ":" || name == "->") then .pure .constructor
      else if directCall then .pure .staticCall
      else .read name fun known => .pure (if known then .staticCall else .constructor)
  | .expression [] => .pure .constructor
  | .expression (_ :: _) => .pure .dynamicCall
  | _ => .pure .value

theorem role_query_refines (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) :
    (ReadOnlyQuery.run (nativeKnown facts) (roleQuery valueOrigin directCall term)).answer =
      classify facts valueOrigin directCall term := by
  cases valueOrigin <;> cases term with
  | symbol name => rfl
  | var name => rfl
  | grounded value => rfl
  | expression fields =>
      cases fields with
      | nil => rfl
      | cons head arguments =>
          cases head <;> cases directCall <;>
            simp [roleQuery, classify, ReadOnlyQuery.run]
          all_goals split <;> simp [ReadOnlyQuery.run]

theorem validated_role_reuse (first second : Facts)
    (valueOrigin directCall : Bool) (term : Atom)
    (valid : ReadOnlyQuery.checkReads (nativeKnown second)
      (ReadOnlyQuery.run (nativeKnown first) (roleQuery valueOrigin directCall term)).reads = true) :
    classify second valueOrigin directCall term = classify first valueOrigin directCall term := by
  rw [← role_query_refines, ← role_query_refines]
  exact ReadOnlyQuery.validated_answer _ _ _ valid

variable {Value Effect Fault Delay Suspension Context World Worker : Type}

local notation "Call" => Authority × Atom
local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

def lower (value : Atom → Value) (constructor : Atom → Code)
    (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) : Option Code :=
  let role := classify facts valueOrigin directCall term
  ExecutionControl.Occurrence.lower (fun item : Call => value item.2)
    (fun item => constructor item.2) id
    (ExecutionControl.Occurrence.elaborate role) (role, term)

def source (value : Atom → Value) (constructor : Atom → Code)
    (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) : Code :=
  match sourceRole facts valueOrigin directCall term with
  | .value => .returned (value term)
  | .constructor => constructor term
  | .staticCall => .invoke (.staticCall, term)
  | .dynamicCall => .invoke (.dynamicCall, term)

theorem lowering_refines (value : Atom → Value) (constructor : Atom → Code)
    (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) :
    lower value constructor facts valueOrigin directCall term =
      some (source value constructor facts valueOrigin directCall term) := by
  simp only [lower, classification_refines]
  cases chosen : sourceRole facts valueOrigin directCall term <;>
    simp [source, chosen, ExecutionControl.Occurrence.lower,
      ExecutionControl.Occurrence.elaborate]

theorem contextual_step_refines
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (value : Atom → Value) (constructor : Atom → Code)
    (facts : Facts) (valueOrigin directCall : Bool) (term : Atom) :
    (lower value constructor facts valueOrigin directCall term).bind (fun code =>
      ContextualCBPV.step sem {state with focus := ⟨.compute context code, state.focus.frames⟩}) =
      ContextualCBPV.step sem {state with focus :=
        ⟨.compute context (source value constructor facts valueOrigin directCall term), state.focus.frames⟩} := by
  rw [lowering_refines]
  rfl

namespace Controls

def absent : Facts := ⟨{}, {}, {}⟩
def added : Facts := ⟨{":"}, {"future"}, {"extension"}⟩
def application (name : String) : Atom :=
  .expression [.symbol name, .grounded (.int 7)]

theorem missing_callability_is_observed :
    (ReadOnlyQuery.run (nativeKnown absent)
      (roleQuery false false (application "future"))).reads = [("future", false)] := by
  decide +kernel

theorem declaration_change_invalidates_old_role :
    ReadOnlyQuery.checkReads (nativeKnown added)
      (ReadOnlyQuery.run (nativeKnown absent)
        (roleQuery false false (application "future"))).reads = false ∧
    classify absent false false (application "future") = .constructor ∧
    classify added false false (application "future") = .staticCall := by
  decide +kernel

theorem established_value_does_not_become_code :
    classify added true false (application "future") = .value ∧
    (ReadOnlyQuery.run (nativeKnown added)
      (roleQuery true false (application "future"))).reads = [] := by
  decide +kernel

theorem forced_call_and_constructor_priority :
    classify absent false true (application "future") = .staticCall ∧
    classify added false true (application ":") = .constructor := by
  decide +kernel

theorem constructor_arity_matters :
    classify added false false (.expression [.symbol ":"]) = .staticCall ∧
    classify added false false (application ":") = .constructor := by
  decide +kernel

theorem dispatch_is_not_a_static_name_lookup :
    classify absent false false (.expression [.var "head", .symbol "argument"]) = .dynamicCall ∧
    (ReadOnlyQuery.run (nativeKnown absent)
      (roleQuery false false (.expression [.var "head", .symbol "argument"]))).reads = [] := by
  decide +kernel

end Controls
end Mettapedia.Machines.SourceRoleElaboration
