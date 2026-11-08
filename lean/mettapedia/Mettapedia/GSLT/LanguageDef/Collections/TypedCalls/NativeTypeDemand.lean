import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews
import Mettapedia.Machines.ReadOnlyQueryDemand

/-!
# Demand-directed admission from completed type observations

An inference plan is an adaptive read-only query. Its admission interpreter
reads only already completed observations and stops at the first unavailable
one. A completed empty list is a value, not an unavailable observation.

The plan below follows the special-head, annotation, ordered signature and
tuple branches of `NativeTypeViews.sourceNode`. It preserves first-local-match
argument selection and stops tuple reads at the first empty component. It
does not call the source evaluator on decline and does not execute a program
body. Primitive services in `Ops` remain pure and fixed within the scope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemand

open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryDemand
open NativeTypeViews

variable {Value TypeAtom Bind Kind : Type}

inductive Question (Value : Type) where
  | classify (head : Value) (children : List Value)
  | annotations (head : Value) (children : List Value)
  | headRows (head : Value)
  | tupleHead (head : Value)
  | kind (value : Value)
  | inferred (value : Value)
  | tuplePart (value : Value)
  deriving DecidableEq

inductive ViewReply (TypeAtom Kind : Type) where
  | class_ (value : HeadClass)
  | types (values : List TypeAtom)
  | kind (value : Kind)
  deriving DecidableEq

abbrev CheckedPlan (Value TypeAtom Kind Result : Type) :=
  Program (Question Value) (ViewReply TypeAtom Kind) (Except Unit Result)

/-- The total oracle is used for the semantic comparison, not by admission.
Admission receives only a partial store of completed primitive observations. -/
def sourceStore (reads : NativeTypeViews.Reads Value TypeAtom Kind) :
    Question Value → ViewReply TypeAtom Kind
  | .classify head children => .class_ (reads.classify head children)
  | .annotations head children => .types (reads.annotations head children)
  | .headRows head => .types (reads.headRows head)
  | .tupleHead head => .types (reads.tupleHead head)
  | .kind value => .kind (reads.kind value)
  | .inferred value => .types (reads.inferred value)
  | .tuplePart value => .types (reads.tuplePart value)

def typesRead {Result : Type} (key : Question Value)
    (next : List TypeAtom → CheckedPlan Value TypeAtom Kind Result) :
    CheckedPlan Value TypeAtom Kind Result :=
  .read key fun
    | .types types => next types
    | _ => .pure (.error ())

def argsPlan (ops : Ops TypeAtom Bind Kind) :
    List TypeAtom → List Value → Bind → CheckedPlan Value TypeAtom Kind (Option Bind)
  | [], [], state => .pure (.ok (some state))
  | formal :: formals, value :: values, state =>
      .read (.kind value) fun
        | .kind kind =>
            match ops.metaCheck (ops.apply state formal) kind with
            | some true => argsPlan ops formals values state
            | some false => .pure (.ok none)
            | none => typesRead (.inferred value) fun types =>
                match StampInference.firstResult
                    (fun actual => ops.unify state actual (ops.apply state formal)) types with
                | none => .pure (.ok none)
                | some next => argsPlan ops formals values next
        | _ => .pure (.error ())
  | _, _, _ => .pure (.ok none)

theorem argsPlan_exact (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind) (formals : List TypeAtom) :
    ∀ values state, (run (sourceStore reads) (argsPlan ops formals values state)).answer =
      .ok (sourceArgs ops reads formals values state) := by
  induction formals with
  | nil => intro values state; cases values <;> rfl
  | cons formal formals ih =>
      intro values state
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [argsPlan, run, sourceStore, sourceArgs]
          cases metatype : ops.metaCheck (ops.apply state formal) (reads.kind value) with
          | some answer => cases answer <;> simp [run, ih]
          | none =>
              simp only [typesRead, run, sourceStore]
              cases chosen : StampInference.firstResult
                  (fun actual => ops.unify state actual (ops.apply state formal)) (reads.inferred value) with
              | none => rfl
              | some next => exact ih values next

def rowsPlan (ops : Ops TypeAtom Bind Kind) (values : List Value) :
    List TypeAtom → CheckedPlan Value TypeAtom Kind (List TypeAtom)
  | [] => .pure (.ok [])
  | row :: rows =>
      match ops.arrow row with
      | none => rowsPlan ops values rows
      | some (formals, range) => bind (argsPlan ops formals values ops.initial) fun
          | .error error => .pure (.error error)
          | .ok none => rowsPlan ops values rows
          | .ok (some state) => map (Except.map (ops.normalize (ops.apply state range) :: ·))
              (rowsPlan ops values rows)

theorem rowsPlan_exact (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind) (values : List Value) (rows : List TypeAtom) :
    (run (sourceStore reads) (rowsPlan ops values rows)).answer =
      .ok (sourceRows ops reads values rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [rowsPlan, sourceRows]
      cases arrow : ops.arrow row with
      | none => exact ih
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          simp only [run_bind, argsPlan_exact]
          cases checked : sourceArgs ops reads formals values ops.initial with
          | none => exact ih
          | some state => simp [run_map, ih, Except.map]

/-- Tuple reads stop at the first completed empty component. -/
def productPlan : List (Question Value) → CheckedPlan Value TypeAtom Kind (List (List TypeAtom))
  | [] => .pure (.ok [[]])
  | key :: keys => typesRead key fun types =>
      if types.isEmpty then .pure (.ok [])
      else map (Except.map (fun tails => types.flatMap fun type_ => tails.map (type_ :: ·)))
        (productPlan keys)

theorem productPlan_exact (store : Question Value → ViewReply TypeAtom Kind)
    (types : Question Value → List TypeAtom) (keys : List (Question Value))
    (typed : ∀ key ∈ keys, store key = .types (types key)) :
    (run store (productPlan keys)).answer = .ok (StampInference.product (keys.map types)) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      have tail : ∀ k ∈ keys, store k = .types (types k) := fun k member => typed k (by simp [member])
      simp only [productPlan, typesRead, run, typed key (by simp), List.map_cons]
      cases current : types key with
      | nil => simp [StampInference.product, run]
      | cons type_ rest => simp [run_map, ih tail, StampInference.product, Except.map]

def ordinaryPlan (ops : Ops TypeAtom Bind Kind) (head : Value) (values : List Value) :
    CheckedPlan Value TypeAtom Kind (List TypeAtom) :=
  typesRead (.headRows head) fun rows =>
    if rows.any (fun row => (ops.arrow row).isSome) then rowsPlan ops values rows
    else map (Except.map (fun product => defaultTypes ops (product.map ops.tuple)))
      (productPlan (.tupleHead head :: values.map Question.tuplePart))

def annotatedPlan (ops : Ops TypeAtom Bind Kind) (head : Value) (values : List Value)
    (annotations : List TypeAtom) : CheckedPlan Value TypeAtom Kind (List TypeAtom) :=
  match ops.annotationPolicy with
  | .historicalOverride => .pure (.ok (ops.close annotations))
  | .supplement same => typesRead (.headRows head) fun rows =>
      if rows.any (fun row => (ops.arrow row).isSome) then
        map (Except.map (supplement same (ops.close annotations))) (rowsPlan ops values rows)
      else .pure (.ok (ops.close annotations))

def nodePlan (ops : Ops TypeAtom Bind Kind) (question : Bool) (head : Value) (values : List Value) :
    CheckedPlan Value TypeAtom Kind (List TypeAtom) :=
  .read (.classify head values) fun
    | .class_ .nativeMork => .pure (.ok [ops.nativeMork])
    | .class_ .listValue => .pure (.ok [ops.listType])
    | .class_ .ordinary =>
        if question then typesRead (.annotations head values) fun types =>
          if types.isEmpty then ordinaryPlan ops head values else annotatedPlan ops head values types
        else ordinaryPlan ops head values
    | _ => .pure (.error ())

def tupleTypes (reads : NativeTypeViews.Reads Value TypeAtom Kind) : Question Value → List TypeAtom
  | .tupleHead head => reads.tupleHead head
  | .tuplePart value => reads.tuplePart value
  | _ => []

theorem tuplePlan_exact (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (head : Value) (values : List Value) :
    (run (sourceStore reads)
      (productPlan (.tupleHead head :: values.map Question.tuplePart))).answer =
      .ok (StampInference.product (reads.tupleHead head :: values.map reads.tuplePart)) := by
  have typed : ∀ key ∈ (Question.tupleHead head :: values.map Question.tuplePart),
      sourceStore reads key = .types (tupleTypes reads key) := by
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
      rfl
  simpa [tupleTypes, List.map_map, Function.comp_def] using
    productPlan_exact (sourceStore reads) (tupleTypes reads)
      (.tupleHead head :: values.map Question.tuplePart) typed

theorem ordinaryPlan_exact (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind) (head : Value) (values : List Value) :
    (run (sourceStore reads) (ordinaryPlan ops head values)).answer =
      .ok (if (reads.headRows head).any (fun row => (ops.arrow row).isSome) then
        sourceRows ops reads values (reads.headRows head)
      else defaultTypes ops ((StampInference.product
        (reads.tupleHead head :: values.map reads.tuplePart)).map ops.tuple)) := by
  simp only [ordinaryPlan, typesRead, run, sourceStore]
  split
  · exact rowsPlan_exact ops reads values (reads.headRows head)
  · simp [run_map, tuplePlan_exact, Except.map]

theorem annotatedPlan_exact (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind) (head : Value) (values : List Value)
    (annotations : List TypeAtom) :
    (run (sourceStore reads) (annotatedPlan ops head values annotations)).answer =
      .ok (match ops.annotationPolicy with
        | .historicalOverride => ops.close annotations
        | .supplement same =>
            if (reads.headRows head).any (fun row => (ops.arrow row).isSome) then
              supplement same (ops.close annotations) (sourceRows ops reads values (reads.headRows head))
            else ops.close annotations) := by
  cases policy : ops.annotationPolicy with
  | historicalOverride => simp [annotatedPlan, policy, run]
  | supplement same =>
      simp only [annotatedPlan, policy, typesRead, run, sourceStore]
      split
      · simp [run_map, rowsPlan_exact, Except.map]
      · rfl

/-- The complete-read plan is derived from the independently specified
source traversal, not a wrapper that calls that traversal as its body. -/
theorem nodePlan_exact (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value) :
    (run (sourceStore reads) (nodePlan ops question head values)).answer =
      .ok (sourceNode ops reads question head values) := by
  simp only [nodePlan, run, sourceStore, sourceNode]
  cases classified : reads.classify head values with
  | nativeMork => rfl
  | listValue => rfl
  | ordinary =>
      cases question with
      | false => simpa using ordinaryPlan_exact ops reads head values
      | true =>
          simp only [if_true, typesRead, run, sourceStore]
          split
          · exact ordinaryPlan_exact ops reads head values
          · exact annotatedPlan_exact ops reads head values (reads.annotations head values)

/-- Admission returns `none` at the first missing observation, `some (.ok
[])` for a completed empty result, and a distinct malformed-response marker
for an ill-typed service reply. No canonical evaluation is run on decline. -/
def check (ops : Ops TypeAtom Bind Kind) (question : Bool) (head : Value) (values : List Value)
    (available : Question Value → Option (ViewReply TypeAtom Kind)) :
    Observation (Question Value) (Option (ViewReply TypeAtom Kind)) (Option (Except Unit (List TypeAtom))) :=
  run available (demand (nodePlan ops question head values))

/-- Exactly the source-selected questions must be available. In particular,
unread child inference, tuple or annotation views are not admission premises. -/
theorem check_exact_iff_covered (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value)
    (available : Question Value → Option (ViewReply TypeAtom Kind))
    (truthful : Truthful (sourceStore reads) available) :
    (check ops question head values available).answer =
        some (.ok (sourceNode ops reads question head values)) ↔
      Covered available (run (sourceStore reads) (nodePlan ops question head values)).reads := by
  constructor
  · intro correct
    apply (demand_success_iff_covered (sourceStore reads) available truthful
      (nodePlan ops question head values)).mp
    change (check ops question head values available).answer ≠ none
    rw [correct]
    simp
  · intro covered
    rw [check, demand_eq_of_covered (sourceStore reads) available _ covered]
    simp [lifted, nodePlan_exact]

theorem check_accepted_eq_source (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value)
    (available : Question Value → Option (ViewReply TypeAtom Kind))
    (truthful : Truthful (sourceStore reads) available) (answers : List TypeAtom)
    (accepted : (check ops question head values available).answer = some (.ok answers)) :
    answers = sourceNode ops reads question head values := by
  have success : (run available (demand (nodePlan ops question head values))).answer ≠ none := by
    change (check ops question head values available).answer ≠ none
    rw [accepted]
    simp
  have exactRun := congrArg Observation.answer
    (demand_success_exact (sourceStore reads) available truthful (nodePlan ops question head values) success)
  change (check ops question head values available).answer = _ at exactRun
  simpa [accepted, lifted, nodePlan_exact] using exactRun

/-- Successful admission publishes the exact ordered dependency certificate,
not merely the positive lookups or the support of the answer set. -/
theorem check_accepted_reads (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value)
    (available : Question Value → Option (ViewReply TypeAtom Kind))
    (truthful : Truthful (sourceStore reads) available)
    (accepted : (check ops question head values available).answer ≠ none) :
    (check ops question head values available).reads =
      liftedReads (run (sourceStore reads) (nodePlan ops question head values)).reads :=
  congrArg Observation.reads
    (demand_success_exact (sourceStore reads) available truthful (nodePlan ops question head values) accepted)

theorem check_decline_first_missing (ops : Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value)
    (available : Question Value → Option (ViewReply TypeAtom Kind))
    (truthful : Truthful (sourceStore reads) available)
    (declined : (check ops question head values available).answer = none) :
    ∃ before key reply suffix,
      (run (sourceStore reads) (nodePlan ops question head values)).reads = before ++ (key, reply) :: suffix ∧
      (check ops question head values available).reads = liftedReads before ++ [(key, none)] ∧
      Covered available before ∧ available key = none :=
  demand_decline_prefix (sourceStore reads) available truthful (nodePlan ops question head values) declined

/-- The existing read-only replay theorem is the authority for retained
certificates. Only the questions actually observed need agree. -/
theorem source_eq_of_agrees (ops : Ops TypeAtom Bind Kind)
    (before after : NativeTypeViews.Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value)
    (agree : Agrees (sourceStore after)
      (run (sourceStore before) (nodePlan ops question head values)).reads) :
    sourceNode ops after question head values = sourceNode ops before question head values := by
  have eq := congrArg Observation.answer
    (run_eq_of_agrees (sourceStore before) (sourceStore after) (nodePlan ops question head values) agree)
  simpa [nodePlan_exact] using eq

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemand
