import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS

/-!
# Binding refinement in the occurrence-wise Destination owner

The source rules of Destination, not a batched evaluator, earn these facts.
Bindings are constraints: a later record refines an earlier record when
every later solution is an earlier solution. This permits retained and
copied caller presentations without assuming literal list equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def Extends (earlier later : Equations) : Prop :=
  ∀ environment, Solves environment later → Solves environment earlier

theorem Extends.refl (bindings : Equations) : Extends bindings bindings := fun _ solved => solved

theorem Extends.trans {first second third : Equations}
    (one : Extends first second) (two : Extends second third) : Extends first third :=
  fun environment solved => one environment (two environment solved)

/-- A branch-local observation justified by its reached equations. Logical
contracts can carry an existential entry witness per occurrence; two equal
contexts need not identify their different branch records. -/
structure BindingPredicate (Context : Type) where
  holds : Context → Equations → Prop
  closed : ∀ context before after, holds context before → Extends before after → holds context after

def BindingPredicate.initialRows {Context : Type} (initial : Context → Equations) : BindingPredicate Context where
  holds context bindings := Extends (initial context) bindings
  closed _ _ _ before after := before.trans after

theorem append_extends (before after : Equations) : Extends before (before ++ after) := by
  intro environment solved pair present
  exact solved pair (List.mem_append_left _ present)

theorem accepted_extends {before after : Equations} {value destination : Atom}
    (accepted : Refinement before value destination (some after)) : Extends before after := by
  cases accepted
  exact append_extends _ _

def localRecords {Context : Type} : Source.Action Context → List Equations
  | .silent cursor => [cursor.control.bindings]
  | .publish _ cursor => [cursor.control.bindings]
  | .finish (_, cursor) => [cursor.control.bindings]
  | .call _ cursor => [cursor.control.bindings]
  | .fail _ => []

/-- Error propagation can discard younger goals but cannot replace the
reached bindings with an older caller record. -/
theorem argument_return_extends {Context : Type} {cursor : Cursor Context}
    {value destination : Atom} {younger older : List Goal} {action : Source.Action Context}
    (source : ArgumentReturn cursor value destination younger older action) :
    ∀ bindings ∈ localRecords action, Extends cursor.control.bindings bindings := by
  cases source with
  | ordinary => simp only [localRecords, List.mem_singleton]; intro _ same; subst same; exact .refl _
  | propagated environment resolved error after accepted =>
      simp only [localRecords, List.mem_singleton]
      intro _ same
      subst same
      exact accepted_extends accepted
  | refused => simp only [localRecords, List.mem_singleton]; intro _ same; subst same; exact .refl _
  | invalid => simp only [localRecords, List.mem_singleton]; intro _ same; subst same; exact .refl _

/-- Every local source case retains or strengthens its actual branch
record. Primitive effects remain in the original action; no reordering or
evaluation equivalence is inferred from this binding law. -/
theorem local_step_extends {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {cursor : Cursor Context} {action : Source.Action Context}
    (source : Source.Step policy program cursor action) :
    ∀ bindings ∈ localRecords action, Extends cursor.control.bindings bindings := by
  cases source with
  | expanded expression destination older next atGoal ordinary prepared =>
      simp only [localRecords, List.mem_singleton]
      intro _ same
      subst same
      rw [prepared.retains_frame.1]
      exact .refl _
  | accepted value destination older after atGoal accepted =>
      simp only [localRecords, List.mem_singleton]
      intro _ same
      subst same
      exact accepted_extends accepted
  | argument value destination younger older action atGoal returned => exact argument_return_extends returned
  | opening | committing | restoring | refused | returned | conditional | inconsistent |
    invalidDelimiter | printed | requested | querying =>
      simp only [localRecords, List.mem_singleton]
      intro _ same
      subst same
      exact .refl _

theorem actual_local_step_extends {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (licensed : Source.Licensed cursor.control)
    (action : Source.Action Context) (computed : (machine policy program).step cursor = some action) :
    ∀ bindings ∈ localRecords action, Extends cursor.control.bindings bindings := by
  obtain ⟨actual, source, checked⟩ := Source.step_has_source policy program cursor licensed
  have same : actual = action := Option.some.inj (checked.symm.trans computed)
  subst actual
  exact local_step_extends source

def resultBindings : Result → Equations
  | .value _ bindings => bindings
  | .noValue bindings => bindings

theorem finished_record_is_reached {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {cursor reached : Cursor Context} {result : Result}
    (source : Source.Step policy program cursor (.finish (result, reached))) :
    resultBindings result = reached.control.bindings := by
  cases source with
  | returned => rfl
  | refused => rfl
  | argument _ _ _ _ _ _ returned => cases returned; rfl

theorem silent_context_preserved {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {cursor reached : Cursor Context}
    (source : Source.Step policy program cursor (.silent reached)) : reached.context = cursor.context := by
  cases source <;> try rfl
  case argument returned => cases returned <;> rfl

theorem finished_context_preserved {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {cursor reached : Cursor Context} {result : Result}
    (source : Source.Step policy program cursor (.finish (result, reached))) : reached.context = cursor.context := by
  cases source <;> try rfl
  case argument returned => cases returned; rfl

/-- The complete earlier materialized packet is absorbed by every later
actual solved branch, including aliases in saved observations. -/
theorem resolved_packet_absorbed {before after : Equations} {old current : Environment}
    (earlier : resolve before = some old) (later : resolve after = some current)
    (extension : Extends before after) (observations : List Atom) :
    (observations.map (read old)).map (read current) = observations.map (read current) :=
  resolve_packet_preserves earlier current (extension current (resolve_sound later)) observations

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport
