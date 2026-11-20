import Mathlib.Data.List.Basic

/-!
# General heads, activation and scope are separate dispatch decisions

This is the head/arity candidate-selection component, not a new MeTTa evaluator.
Payloads may be source equations or compiled actions; their argument matching,
freshening and execution belong to the existing caller. A variable in a rule's
head is a general head pattern, not higher-order unification or dynamic function
application. Scope is supplied by the caller's authority, not inferred from an
untrusted term spelling.

The finite design family has three independent Boolean choices. Its separating
controls and exact law characterization concern this family only. The selected
lists denote observations, not a native instruction to gather all candidates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.HeadDispatchDesigns

structure Design where
  generalHeads : Bool
  protectHeld : Bool
  respectScope : Bool
  deriving DecidableEq, Repr

structure Rule (Payload : Type) where
  scope : Nat
  head : Option String
  arity : Nat
  payload : Payload
  deriving DecidableEq, Repr

structure Request where
  head : String
  arity : Nat
  held : Bool
  deriving DecidableEq, Repr

variable {Payload : Type}

def headMatches (design : Design) (head : String) : Option String → Bool
  | none => design.generalHeads
  | some name => name == head

def enabled (design : Design) (scope : Nat) (request : Request) (rule : Rule Payload) : Bool :=
  (!(design.protectHeld && request.held)) &&
    (!design.respectScope || rule.scope == scope) &&
    (rule.arity == request.arity) && headMatches design request.head rule.head

def select (design : Design) (scope : Nat) (request : Request)
    (rules : List (Rule Payload)) : List Payload :=
  rules.filterMap fun rule => if enabled design scope request rule then some rule.payload else none

theorem select_append (design : Design) (scope : Nat) (request : Request)
    (first second : List (Rule Payload)) :
    select design scope request (first ++ second) =
      select design scope request first ++ select design scope request second := by
  simp [select]

theorem held_is_inert {design : Design} (heldSafe : design.protectHeld = true)
    (scope : Nat) (request : Request) (held : request.held = true)
    (rules : List (Rule Payload)) : select design scope request rules = [] := by
  simp [select, enabled, heldSafe, held]

theorem foreign_rule_is_invisible {design : Design} (scopeSafe : design.respectScope = true)
    (scope : Nat) (request : Request) (rule : Rule Payload) (foreign : rule.scope ≠ scope) :
    enabled design scope request rule = false := by
  simp [enabled, scopeSafe, foreign]

theorem foreign_extension_keeps_selection {design : Design}
    (scopeSafe : design.respectScope = true) (scope : Nat) (request : Request)
    (rules added : List (Rule Payload))
    (foreign : ∀ rule ∈ added, rule.scope ≠ scope) :
    select design scope request (rules ++ added) = select design scope request rules := by
  rw [select_append]
  suffices empty : select design scope request added = [] by simp [empty]
  apply List.filterMap_eq_nil_iff.mpr
  intro rule member
  simp [foreign_rule_is_invisible scopeSafe scope request rule (foreign rule member)]

/-- The named-head fragment has identical selections with general heads on
or off. This preserves ordering and duplicate payloads, not just membership. -/
theorem named_fragment_conservative (design : Design) (scope : Nat) (request : Request)
    (rules : List (Rule Payload)) (named : ∀ rule ∈ rules, rule.head ≠ none) :
    select { design with generalHeads := true } scope request rules =
      select { design with generalHeads := false } scope request rules := by
  unfold select
  apply List.filterMap_congr
  intro rule member
  cases head : rule.head with
  | none => exact False.elim (named rule member head)
  | some name => simp [enabled, headMatches, head]

/-- A separated authoritative row view removes scope tests from the inner
selection. This is a representation license, not a CPU-time measurement. -/
theorem separated_view_erases_scope_tests (design : Design) (scope : Nat) (request : Request)
    (source internal : List (Rule Payload))
    (sourceScope : ∀ rule ∈ source, rule.scope = scope)
    (internalScope : ∀ rule ∈ internal, rule.scope ≠ scope) :
    select { design with respectScope := true } scope request (source ++ internal) =
      select { design with respectScope := false } scope request source := by
  rw [foreign_extension_keeps_selection rfl scope request source internal internalScope]
  unfold select
  apply List.filterMap_congr
  intro rule member
  cases shape : rule.head <;> simp [enabled, headMatches, shape, sourceScope rule member]

def HeldInert (design : Design) : Prop :=
  ∀ (scope : Nat) (request : Request) (rules : List (Rule Nat)), request.held = true →
    select design scope request rules = []

def Scoped (design : Design) : Prop :=
  ∀ (scope : Nat) (request : Request) (rule : Rule Nat), rule.scope ≠ scope →
    select design scope request [rule] = []

def GeneralExpressive (design : Design) : Prop :=
  ∀ (scope : Nat) (head : String) (arity payload : Nat),
    select design scope ⟨head, arity, false⟩ [⟨scope, none, arity, payload⟩] = [payload]

theorem general_head_selects_once {design : Design} (general : design.generalHeads = true)
    (scope : Nat) (head : String) (arity : Nat) (payload : Payload) :
    select design scope ⟨head, arity, false⟩ [⟨scope, none, arity, payload⟩] = [payload] := by
  simp [select, enabled, headMatches, general]

theorem held_inert_iff (design : Design) : HeldInert design ↔ design.protectHeld = true := by
  constructor
  · intro inert
    have witness := inert 0 ⟨"f", 1, true⟩ [⟨0, some "f", 1, 8⟩] rfl
    cases held : design.protectHeld <;> simp_all [select, enabled, headMatches]
  · intro heldSafe scope request rules held
    exact held_is_inert heldSafe scope request held rules

theorem scoped_iff (design : Design) : Scoped design ↔ design.respectScope = true := by
  constructor
  · intro isolated
    have witness := isolated 0 ⟨"f", 1, false⟩ ⟨1, some "f", 1, 8⟩ (by decide)
    cases scope : design.respectScope <;> simp_all [select, enabled, headMatches]
  · intro scopeSafe scope request rule foreign
    simp [select, foreign_rule_is_invisible scopeSafe scope request rule foreign]

theorem general_expressive_iff (design : Design) :
    GeneralExpressive design ↔ design.generalHeads = true := by
  constructor
  · intro expressive
    have witness := expressive 0 "f" 1 8
    cases general : design.generalHeads <;> simp_all [select, enabled, headMatches]
  · intro general scope head arity payload
    exact general_head_selects_once general scope head arity payload

/-- All three desired properties can coexist. They characterize exactly this
combination within the stated eight designs; no universal optimality follows. -/
theorem three_laws_iff (design : Design) :
    HeldInert design ∧ Scoped design ∧ GeneralExpressive design ↔
      design.protectHeld = true ∧ design.respectScope = true ∧ design.generalHeads = true := by
  rw [held_inert_iff, scoped_iff, general_expressive_iff]

namespace Controls

def unrestricted : Design := ⟨true, false, false⟩
def scopedGeneral : Design := ⟨true, true, true⟩
def namedOnly : Design := ⟨false, true, true⟩

def generalUnary : Rule Nat := ⟨0, none, 1, 8⟩

theorem held_data_is_a_candidate_without_activation_protection :
    select unrestricted 0 ⟨"pm:state", 1, true⟩ [generalUnary] = [8] := by decide

theorem scoped_general_rules_keep_held_data_and_run_explicit_calls :
    select scopedGeneral 0 ⟨"pm:state", 1, true⟩ [generalUnary] = [] ∧
      select scopedGeneral 0 ⟨"double", 1, false⟩ [generalUnary] = [8] := by decide

theorem named_only_loses_general_head_expressiveness :
    select namedOnly 0 ⟨"double", 1, false⟩ [generalUnary] = [] ∧
      ¬ GeneralExpressive namedOnly := by
  constructor
  · decide
  · intro expressive
    have impossible := (general_expressive_iff namedOnly).mp expressive
    contradiction

theorem a_private_named_rule_also_leaks_through_flat_visibility :
    select unrestricted 0 ⟨"count", 0, false⟩ [⟨1, some "count", 0, 99⟩] = [99] ∧
      select scopedGeneral 0 ⟨"count", 0, false⟩ [⟨1, some "count", 0, 99⟩] = [] := by decide

theorem general_rules_preserve_equal_occurrences :
    select scopedGeneral 0 ⟨"double", 1, false⟩ [generalUnary, generalUnary] = [8, 8] := by decide

end Controls

end Mettapedia.Machines.OperatorChoice.HeadDispatchDesigns
