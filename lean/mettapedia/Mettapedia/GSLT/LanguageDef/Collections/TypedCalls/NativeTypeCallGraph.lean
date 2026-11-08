import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyClosure
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureRounds
import Mettapedia.Machines.ReadOnlyQueryExpansion

/-!
# The native inference call graph as adaptive read programs

The existing argument, row and Cartesian-product plans are reused unchanged.
This adapter exposes their recursive requests and places a completed-closure
port exactly at the native annotation/tuple closure sites. Application result
rows are not additionally subtype-closed. An unfinished port remains missing;
it is never converted to an empty type list.

Three recursive inquiries are distinct: ordinary inference, tuple-part
inference, and effective operator rows. Symbols used as tuple parts read raw
annotations, not subtype-closed inferred types. An expression operator is
recursively inferred only when its direct declarations are empty. Metatype
formals and the first empty tuple component retain the existing demand cuts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQuery
open NativeTypeViews

inductive Primitive where
  | annotations (atom : Atom)
  | intrinsic (atom : Atom)
  | kind (atom : Atom)
  | classify (head : Atom) (values : List Atom)
  | closure (seeds : List Atom)
  deriving DecidableEq

inductive Call where
  | infer (direct : Bool) (atom : Atom)
  | tuplePart (atHead : Bool) (atom : Atom)
  | operatorRows (atom : Atom)
  deriving DecidableEq

abbrev Question := Sum Primitive Call
abbrev Reply := NativeTypeDemand.ViewReply Atom Atom
abbrev Plan (Answer : Type) := Program Question Reply (Except Unit Answer)

def viewQuestion : NativeTypeDemand.Question Atom → Question
  | .classify head values => .inl (.classify head values)
  | .annotations head values => .inl (.annotations (.expression (head :: values)))
  | .headRows head => .inr (.operatorRows head)
  | .tupleHead head => .inr (.tuplePart true head)
  | .kind atom => .inl (.kind atom)
  | .inferred atom => .inr (.infer true atom)
  | .tuplePart atom => .inr (.tuplePart false atom)

def liftViews {Answer : Type} :
    Program (NativeTypeDemand.Question Atom) Reply Answer → Program Question Reply Answer
  | .pure answer => .pure answer
  | .read key next => .read (viewQuestion key) fun reply => liftViews (next reply)

def typesRead {Answer : Type} (key : Question) (next : List Atom → Plan Answer) : Plan Answer :=
  .read key fun
    | .types types => next types
    | _ => .pure (.error ())

def finishTypes (types : List Atom) : Plan Reply := .pure (.ok (.types types))

def closeTypes (types : List Atom) : Plan Reply :=
  typesRead (.inl (.closure types)) finishTypes

def mapTypes (program : Plan (List Atom)) : Plan Reply :=
  map (Except.map (fun types => .types types)) program

def ordinary (ops : Ops Atom TypeScopeMatcher.State Atom) (head : Atom) (values : List Atom) : Plan Reply :=
  typesRead (.inr (.operatorRows head)) fun rows =>
    if rows.any (fun row => (ops.arrow row).isSome) then
      mapTypes (liftViews (NativeTypeDemand.rowsPlan ops values rows))
    else bind (liftViews (NativeTypeDemand.productPlan
        (.tupleHead head :: values.map NativeTypeDemand.Question.tuplePart))) fun
      | .error error => .pure (.error error)
      | .ok product =>
          let seeds := product.map ops.tuple
          if seeds.isEmpty then finishTypes [ops.undefined] else closeTypes seeds

/-- In the current policy the annotation prefix is subtype-closed before
operator inference. A missing closure/read stops the demand interpreter;
the already found annotation is not an excuse to erase that dependency. -/
def annotated (ops : Ops Atom TypeScopeMatcher.State Atom) (head : Atom) (values : List Atom)
    (annotations : List Atom) : Plan Reply :=
  match ops.annotationPolicy with
  | .historicalOverride => closeTypes annotations
  | .supplement same => typesRead (.inl (.closure annotations)) fun closed =>
      typesRead (.inr (.operatorRows head)) fun rows =>
        if rows.any (fun row => (ops.arrow row).isSome) then
          map (Except.map (fun derived => .types (supplement same closed derived)))
            (liftViews (NativeTypeDemand.rowsPlan ops values rows))
        else finishTypes closed

def node (ops : Ops Atom TypeScopeMatcher.State Atom) (direct : Bool)
    (head : Atom) (values : List Atom) : Plan Reply :=
  .read (.inl (.classify head values)) fun
    | .class_ .nativeMork => finishTypes [ops.nativeMork]
    | .class_ .listValue => finishTypes [ops.listType]
    | .class_ .ordinary =>
        if direct then typesRead (.inl (.annotations (.expression (head :: values)))) fun types =>
          if types.isEmpty then ordinary ops head values else annotated ops head values types
        else ordinary ops head values
    | _ => .pure (.error ())

def keepTuple (ops : Ops Atom TypeScopeMatcher.State Atom) (atHead : Bool) (type_ : Atom) : Bool :=
  type_ != ops.undefined && (!atHead || !(ops.arrow type_).isSome)

def body (ops : Ops Atom TypeScopeMatcher.State Atom) : Call → Plan Reply
  | .infer direct atom => match atom with
      | .var _ => finishTypes [ops.undefined]
      | .grounded _ => typesRead (.inl (.intrinsic atom)) fun types =>
          if types.isEmpty then finishTypes [ops.undefined] else finishTypes types
      | .symbol _ =>
          if direct then typesRead (.inl (.annotations atom)) fun types =>
            if types.isEmpty then finishTypes [ops.undefined] else closeTypes types
          else finishTypes [ops.undefined]
      | .expression [] => finishTypes [ops.undefined]
      | .expression (head :: values) => node ops direct head values
  | .tuplePart atHead atom =>
      let finish := fun types => finishTypes (types.filter (keepTuple ops atHead))
      match atom with
      | .var _ => finishTypes []
      | .grounded _ => typesRead (.inl (.intrinsic atom)) finish
      | .symbol _ => typesRead (.inl (.annotations atom)) finish
      | .expression _ => typesRead (.inr (.infer true atom)) finish
  | .operatorRows atom => typesRead (.inl (.annotations atom)) fun rows =>
      if rows.isEmpty then match atom with
        | .expression _ => typesRead (.inr (.infer true atom)) fun inferred =>
            finishTypes (inferred.filter fun type_ => (ops.arrow type_).isSome)
        | _ => finishTypes []
      else finishTypes rows

/-- Mathematical completed-observation port for one node. A partial source
adapter must earn every reached closure reply before using this port. -/
def completedStore (ops : Ops Atom TypeScopeMatcher.State Atom) (reads : NativeTypeViews.Reads Atom Atom Atom) :
    Question → Reply
  | .inl (.classify head values) => .class_ (reads.classify head values)
  | .inl (.annotations (.expression (head :: values))) => .types (reads.annotations head values)
  | .inl (.annotations atom) => .types (reads.headRows atom)
  | .inl (.intrinsic (.grounded value)) => .types [getGroundedType value]
  | .inl (.intrinsic _) => .types []
  | .inl (.kind atom) => .kind (reads.kind atom)
  | .inl (.closure seeds) => .types (ops.close seeds)
  | .inr (.operatorRows atom) => .types (reads.headRows atom)
  | .inr (.infer _ atom) => .types (reads.inferred atom)
  | .inr (.tuplePart true atom) => .types (reads.tupleHead atom)
  | .inr (.tuplePart false atom) => .types (reads.tuplePart atom)

theorem completedStore_view (ops : Ops Atom TypeScopeMatcher.State Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom) (key : NativeTypeDemand.Question Atom) :
    completedStore ops reads (viewQuestion key) = NativeTypeDemand.sourceStore reads key := by
  cases key <;> rfl

theorem liftViews_answer {Answer : Type} (ops : Ops Atom TypeScopeMatcher.State Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom)
    (program : Program (NativeTypeDemand.Question Atom) Reply Answer) :
    (run (completedStore ops reads) (liftViews program)).answer =
      (run (NativeTypeDemand.sourceStore reads) program).answer := by
  induction program with
  | pure answer => rfl
  | read key next ih => simp only [liftViews, run, completedStore_view]; exact ih _

theorem ordinary_exact (ops : Ops Atom TypeScopeMatcher.State Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom) (head : Atom) (values : List Atom) :
    (run (completedStore ops reads) (ordinary ops head values)).answer =
      .ok (.types (if (reads.headRows head).any (fun row => (ops.arrow row).isSome) then
        sourceRows ops reads values (reads.headRows head)
      else defaultTypes ops ((StampInference.product (reads.tupleHead head :: values.map reads.tuplePart)).map ops.tuple))) := by
  simp only [ordinary, typesRead, run, completedStore]
  split
  · simp [mapTypes, run_map, liftViews_answer, NativeTypeDemand.rowsPlan_exact, Except.map]
  · simp only [run_bind, liftViews_answer, NativeTypeDemand.tuplePlan_exact]
    cases product : StampInference.product (reads.tupleHead head :: values.map reads.tuplePart) <;>
      simp [finishTypes, closeTypes, typesRead, run, completedStore, defaultTypes]

theorem annotated_exact (ops : Ops Atom TypeScopeMatcher.State Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom) (head : Atom) (values : List Atom)
    (annotations : List Atom) :
    (run (completedStore ops reads) (annotated ops head values annotations)).answer =
      .ok (.types (match ops.annotationPolicy with
        | .historicalOverride => ops.close annotations
        | .supplement same =>
            if (reads.headRows head).any (fun row => (ops.arrow row).isSome) then
              supplement same (ops.close annotations) (sourceRows ops reads values (reads.headRows head))
            else ops.close annotations)) := by
  cases policy : ops.annotationPolicy with
  | historicalOverride => simp [annotated, policy, closeTypes, typesRead, finishTypes, run, completedStore]
  | supplement same =>
      simp only [annotated, policy, typesRead, run, completedStore]
      split
      · simp [run_map, liftViews_answer, NativeTypeDemand.rowsPlan_exact, Except.map]
      · rfl

/-- The call-graph adapter agrees with the existing source traversal at
completed ports; it does not substitute a different evaluator definition. -/
theorem node_exact (ops : Ops Atom TypeScopeMatcher.State Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom) (direct : Bool) (head : Atom) (values : List Atom) :
    (run (completedStore ops reads) (node ops direct head values)).answer =
      .ok (.types (sourceNode ops reads direct head values)) := by
  simp only [node, run, completedStore, sourceNode]
  cases kind : reads.classify head values with
  | nativeMork => rfl
  | listValue => rfl
  | ordinary =>
      cases direct with
      | false => exact ordinary_exact ops reads head values
      | true =>
          simp only [typesRead, run, completedStore, if_true]
          split
          · exact ordinary_exact ops reads head values
          · cases policy : ops.annotationPolicy with
            | historicalOverride =>
                simp [annotated, policy, closeTypes, typesRead, finishTypes, run, completedStore]
            | supplement same =>
                simp only [policy, annotated, typesRead, run, completedStore]
                split
                · simp [run_map, liftViews_answer, NativeTypeDemand.rowsPlan_exact, Except.map]
                · rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph
