import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.GSLT.Contracts.TheoryViews
import Mathlib.Data.Finset.Basic

/-!
# Scoped operations and protected imports

Shadowing is a new child environment, not an edit to the parent. A
module may capture its own environment, or be linked against a caller
subject to a protected import interface. A protected slot is checked
even if the old reply was missing. An adaptive program typed over that
interface cannot silently ask an unlisted ambient slot.

Replies are the *effective* declared services: an ordered rule view,
a comparison binding, an equation presentation, or a certified port.
These are not necessarily the definitions written under one head.
Authority evidence may be part of a reply; equality of the resulting
reply alone does not mint authority to change an actual declaration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ScopedTheoryImports

open Mettapedia.Machines.ReadOnlyQuery

universe u v w

variable {Slot : Type u} {Binding : Type v} {Answer : Type w}

abbrev Environment (Slot : Type u) (Binding : Type v) := Slot → Option Binding

/-- A local definition shadows an inherited one without modifying it.
The absence of a local definition searches the parent. This is not an
operation that hides an inherited definition. -/
def shadow (parent child : Environment Slot Binding) : Environment Slot Binding :=
  fun slot => (child slot).orElse (fun _ => parent slot)

theorem shadow_assoc (root parent child : Environment Slot Binding) :
    shadow (shadow root parent) child = shadow root (shadow parent child) := by
  funext slot
  cases here : child slot <;> simp [shadow, here]

/-- Selection is local on the declared dependency set. On an
executable backend, reply equality can compare immutable identities,
provided those identities faithfully determine the declared reply. -/
def Protects (required : Finset Slot) (pinned incoming : Environment Slot Binding) : Prop :=
  ∀ slot ∈ required, incoming slot = pinned slot

theorem shadow_outside_protects (required : Finset Slot)
    (parent child : Environment Slot Binding) (disjoint : ∀ slot ∈ required, child slot = none) :
    Protects required parent (shadow parent child) := by
  intro slot needed
  simp [shadow, disjoint slot needed]

abbrev Key (required : Finset Slot) := {slot : Slot // slot ∈ required}

abbrev Module (required : Finset Slot) (Binding : Type v) (Answer : Type w) :=
  Program (Key required) (Option Binding) Answer

def expose (required : Finset Slot) (env : Environment Slot Binding)
    (slot : Key required) : Option Binding :=
  env slot.val

/-- An admitted link preserves every adaptive observation through the
module interface, not just the last answer of its first call. -/
theorem protected_run {required : Finset Slot} {pinned incoming : Environment Slot Binding}
    (unchanged : Protects required pinned incoming) (program : Module required Binding Answer) :
    run (expose required incoming) program = run (expose required pinned) program := by
  have same : expose required incoming = expose required pinned :=
    funext fun slot => unchanged slot.val slot.property
  rw [same]

/-- For the interface as a whole the check is exact: every listed
coordinate can be probed, even when today's program does not use it. -/
theorem protects_iff_all_clients (required : Finset Slot) (pinned incoming : Environment Slot Binding) :
    Protects required pinned incoming ↔
      ∀ program : Module required Binding (Option Binding),
        run (expose required incoming) program = run (expose required pinned) program := by
  refine ⟨fun unchanged program => protected_run unchanged program, ?_⟩
  intro clients slot used
  have probe := clients (.read ⟨slot, used⟩ (fun reply => .pure reply))
  exact congrArg Observation.answer probe

def compatible [DecidableEq Binding] (required : Finset Slot)
    (pinned incoming : Environment Slot Binding) : Bool :=
  decide (∀ slot ∈ required, incoming slot = pinned slot)

theorem compatible_iff [DecidableEq Binding] (required : Finset Slot)
    (pinned incoming : Environment Slot Binding) :
    compatible required pinned incoming = true ↔ Protects required pinned incoming := by
  simp only [compatible, decide_eq_true_eq, Protects]

/-- Refusing an import is distinct from running it and getting no
answer. A separately captured module simply uses its pinned exposure. -/
def link [DecidableEq Binding] (required : Finset Slot)
    (pinned incoming : Environment Slot Binding) (program : Module required Binding Answer) :
    Option (Observation (Key required) (Option Binding) Answer) :=
  if compatible required pinned incoming then some (run (expose required incoming) program)
  else none

theorem link_eq_some_iff [DecidableEq Binding] (required : Finset Slot)
    (pinned incoming : Environment Slot Binding) (program : Module required Binding Answer)
    (answer : Observation (Key required) (Option Binding) Answer) :
    link required pinned incoming program = some answer ↔
      Protects required pinned incoming ∧ run (expose required pinned) program = answer := by
  unfold link
  by_cases good : compatible required pinned incoming = true
  · have unchanged := (compatible_iff required pinned incoming).mp good
    simp [good, unchanged, protected_run unchanged program]
  · rw [if_neg good]
    constructor
    · intro impossible
      cases impossible
    · intro agrees
      exact (good ((compatible_iff required pinned incoming).mpr agrees.1)).elim

/-- A prepared execution has a more precise licence than a whole
module import: the actual read receipt determines that one ordered
execution. This converse uses the ordered receipt, not just its answer. -/
theorem run_eq_iff_receipt (before after : Environment Slot Binding)
    (program : Program Slot (Option Binding) Answer) :
    run after program = run before program ↔ Agrees after (run before program).reads := by
  refine ⟨fun same => ?_, run_eq_of_agrees before after program⟩
  rw [← same]
  exact run_agrees after program

namespace Controls

open Mettapedia.GSLT.Contracts.TheoryViews.Controls (Literal value)

inductive Port where
  | compare
  | matchTheory
  | helper
  deriving DecidableEq

inductive BindingTag where
  | literal
  | number
  deriving DecidableEq

private def top : Environment Port BindingTag :=
  fun slot => if slot = .helper then none else some .literal

private def child : Environment Port BindingTag
  | .compare => some .number
  | _ => none

private def asked : Program Port (Option BindingTag) Bool :=
  .read .compare fun response =>
    let one := Literal.integer 1
    let oneAgain := Literal.dyadic 2 1
    .pure (match response with
      | some .number => decide (value one = value oneAgain)
      | some .literal => decide (one = oneAgain)
      | none => false)

theorem local_comparison_can_change_without_rekeying :
    (run top asked).answer = false ∧ (run (shadow top child) asked).answer = true ∧
      Protects {.matchTheory} top (shadow top child) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro slot member
  have : slot = .matchTheory := Finset.mem_singleton.mp member
  subst slot
  rfl

theorem protected_comparison_refuses_relink :
    let locked : Finset Port := {.compare}
    let p : Module locked BindingTag Bool :=
      .read ⟨.compare, Finset.mem_singleton_self _⟩ (fun _ => .pure true)
    link locked top (shadow top child) p = none := by
  rfl

theorem previously_undefined_is_a_dependency :
    ¬ Protects {.helper} top (shadow top (fun _ => some .number)) := by
  intro changed
  have impossible : some BindingTag.number = none := changed .helper (by simp)
  cases impossible

end Controls

/-! ## The effective rule view, including catch-all definitions -/

namespace RuleView

variable {Head : Type u} {Body : Type v} [DecidableEq Head]

structure Entry (Head : Type u) (Body : Type v) where
  head : Option Head
  body : Body
  deriving DecidableEq

def mayAnswer (named : Head) (entry : Entry Head Body) : Bool :=
  entry.head.isNone || decide (entry.head = some named)

def visible (named : Head) (definitions : List (Entry Head Body)) : List (Entry Head Body) :=
  definitions.filter (mayAnswer named)

/-- A trailing definition that matches can change the effective view
without rewriting any existing row. This is a negative dependency of
an exact prepared rule view. -/
theorem append_keeps_view_iff (named : Head) (defs extra : List (Entry Head Body)) :
    visible named (defs ++ extra) = visible named defs ↔ visible named extra = [] := by
  unfold visible
  rw [List.filter_append]
  constructor
  · intro unchanged
    exact List.length_eq_zero_iff.mp (by
      have sizes := congrArg List.length unchanged
      simp only [List.length_append] at sizes
      omega)
  · intro empty
    simp [empty]

theorem own_named_rows_can_miss_a_visible_definition :
    let a : Entry Bool Nat := ⟨some true, 1⟩
    let wildcard : Entry Bool Nat := ⟨none, 2⟩
    ([a, wildcard].filter (fun e => decide (e.head = some true))) = [a] ∧
      visible true [a] ≠ visible true [a, wildcard] := by
  decide

end RuleView

#print axioms protects_iff_all_clients
#print axioms link_eq_some_iff
#print axioms run_eq_iff_receipt
#print axioms Controls.local_comparison_can_change_without_rekeying
#print axioms Controls.protected_comparison_refuses_relink
#print axioms Controls.previously_undefined_is_a_dependency
#print axioms RuleView.append_keeps_view_iff
#print axioms RuleView.own_named_rows_can_miss_a_visible_definition

end Mettapedia.GSLT.Contracts.ScopedTheoryImports
